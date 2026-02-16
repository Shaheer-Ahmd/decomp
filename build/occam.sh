#!/usr/bin/env bash
set -euo pipefail

IMAGE="sricsl/occam:bionic"

usage() {
  cat >&2 <<EOF
Usage:
  $0 /path/to/input.ll [static_arg1 static_arg2 ...]

Notes:
  - input.ll MUST be LLVM10-compatible textual IR (e.g., produced via LLVM10 llvm-dis),
    since the container uses LLVM10-era tools.
  - Output: <input_basename>_slashed.ll in the same directory.
Example:
  $0 /path/to/tcas.ll 1 1 1 1000 50 900 0 400 300 0 1 0
EOF
  exit 1
}

[[ $# -ge 1 ]] || usage
INPUT_LL="$1"; shift || true
[[ -f "$INPUT_LL" ]] || { echo "Error: file not found: $INPUT_LL" >&2; exit 1; }

# Resolve absolute path
INPUT_LL_ABS="$(realpath "$INPUT_LL" 2>/dev/null || readlink -f "$INPUT_LL")"
INPUT_DIR="$(dirname "$INPUT_LL_ABS")"
INPUT_FILE="$(basename "$INPUT_LL_ABS")"
BASE="${INPUT_FILE%.ll}"

STATIC_ARGS=("$@")

# Build JSON array for manifest safely (no heredoc-arg pitfalls)
STATIC_ARGS_JSON="$(python3 -c 'import json,sys; print(json.dumps(sys.argv[1:]))' -- "${STATIC_ARGS[@]}")"

WORKDIR_NAME=".occam_slash_${BASE}_work"
WORKDIR_HOST="${INPUT_DIR}/${WORKDIR_NAME}"
OUT_LL_HOST="${INPUT_DIR}/${BASE}_slashed.ll"

rm -rf "$WORKDIR_HOST"
mkdir -p "$WORKDIR_HOST"

# Copy edited IR into workdir
cp -f "$INPUT_LL_ABS" "$WORKDIR_HOST/input.ll"

# Write manifest
cat > "$WORKDIR_HOST/funcs.manifest" <<EOF
{ "main" : "main.o.bc"
, "binary"  : "main"
, "modules"    : []
, "native_libs" : []
, "ldflags"  : []
, "static_args"    : ${STATIC_ARGS_JSON}
, "name"    : "main"
}
EOF

docker run --rm -it \
  -v "${INPUT_DIR}":/host \
  "${IMAGE}" \
  bash -lc "
    set -euo pipefail
    cd /host/${WORKDIR_NAME}

    # Assemble edited LLVM IR -> bitcode (LLVM10 toolchain)
    # This will fail if input.ll was produced by newer LLVM or uses newer syntax.
    llvm-as input.ll -o main.o.bc

    export OCCAM_LOGLEVEL=\${OCCAM_LOGLEVEL:-INFO}
    export OCCAM_LOGFILE=\${PWD}/slash/occam.log

    mkdir -p slash
    slash --intra-spec-policy=nonrec-aggressive --inter-spec-policy=nonrec-aggressive \
          --no-strip --work-dir=slash funcs.manifest

    # OCCAM outputs final specialized module as main.o-final.bc in your listing
    if [[ ! -f slash/main.o-final.bc ]]; then
      echo 'Error: expected slash/main.o-final.bc not found.' >&2
      echo 'Contents of slash/:' >&2
      ls -la slash >&2 || true
      exit 3
    fi

    llvm-dis slash/main.o-final.bc -o slashed.ll
    cp -f slashed.ll \"/host/${BASE}_slashed.ll\"

    echo \"[OK] Wrote: /host/${BASE}_slashed.ll\"
  "

[[ -f "$OUT_LL_HOST" ]] || { echo "[FAIL] Output not found: $OUT_LL_HOST" >&2; exit 4; }
echo "[DONE] Output generated: $OUT_LL_HOST"
