#pragma once

#include "llvm/ADT/StringRef.h"

namespace llvm {
namespace mdk {

// Keys

inline constexpr StringLiteral IncBlockKey{"IncBlock"};

inline constexpr StringLiteral ContBlockKey{"ContBlock"};
inline constexpr StringLiteral ForTag{"ForTag"};
inline constexpr StringLiteral ConditionBlockKey{"ConditionBlock"};
inline constexpr StringLiteral BodyBlockKey{"BodyBlock"};

inline constexpr StringLiteral CompoundConditionSuccessorsKey{"CompoundConditionSuccessors"};
inline constexpr StringLiteral CompoundConditionCaseValuesKey{"CompoundConditionCaseValues"};
inline constexpr StringLiteral DefaultSuccKey{"SwitchDefaultSucc"};
inline constexpr StringLiteral CompoundConditionIfTagKey{"CompoundConditionIfTag"};
inline constexpr StringLiteral CompoundConditionSwitchTagKey{"CompoundConditionSwitchTag"};
inline constexpr StringLiteral CompoundConditionReturnTagKey{
    "CompoundConditionReturnTag"};
inline constexpr StringLiteral CompoundConditionTree{"CompoundConditionTree"};

inline constexpr StringLiteral SwitchTag{"SwitchTag"};
inline constexpr StringLiteral WhileTag{"WhileTag"};
inline constexpr StringLiteral IfTag{"IfTag"};
inline constexpr StringLiteral LoopBreakKey{"LoopBreak"};

inline constexpr StringLiteral IfContBlockKey{"if.cont_block"};
inline constexpr StringLiteral ElseIfKey{"else_if"};

inline constexpr StringLiteral LoopContinueKey{"LoopContinue"};

} // namespace mymd
} // namespace llvm
