#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {

static bool isSkippableName(StringRef N) {
  // You asked for substring checks for these prefixes.
  return N.contains("land.") || N.contains("lor.") || N.contains("crit_edge");
}

static StringRef baseVarName(StringRef N) {
  // "c.1" -> "c", "c.0.load" -> "c", "c" -> "c"
  return N.split('.').first;
}

static StringRef baseVarName(const Value *V) {
  return (V && V->hasName()) ? baseVarName(V->getName()) : StringRef();
}

// Walk up the "first predecessor" chain until we find a non-skippable block.
// Returns nullptr if we can't find one safely.
static BasicBlock *findFirstNonSkippableFirstPredAncestor(BasicBlock *Start) {
  if (!Start)
    return nullptr;

  BasicBlock *Cur = Start;

  // Avoid infinite loops in weird CFGs.
  SmallPtrSet<BasicBlock *, 32> Visited;

  // Hard cap for safety.
  const unsigned MaxHops = 256;
  unsigned Hops = 0;

  while (Cur && Hops++ < MaxHops) {
    if (!Visited.insert(Cur).second) {
      // cycle detected
      return nullptr;
    }

    StringRef Name = Cur->getName();
    if (!isSkippableName(Name)) {
      return Cur; // found a "real" block
    }

    // If skippable, move to its first predecessor
    if (pred_empty(Cur)) {
      return nullptr;
    }
    Cur = *pred_begin(Cur); // "first predecessor"
  }

  return nullptr; // too deep
}

static std::string baseNameFromIRName(llvm::StringRef N) {
  // Examples:
  //   x.0.slot  -> x
  //   x.0.load  -> x
  //   x.addr    -> x
  //   x.12      -> x
  if (N.empty()) return "";

  // Keep everything before the first '.'
  auto Base = N.split('.').first;
  return Base.str();
}

struct RemovePhiToStoresPass : public PassInfoMixin<RemovePhiToStoresPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
    bool Changed = false;

    BasicBlock &Entry = F.getEntryBlock();
    Instruction *AllocaIP =
        &*Entry.getFirstInsertionPt(); // insert allocas here

    // Collect PHIs first
    SmallVector<PHINode *, 32> Phis;
    for (BasicBlock &BB : F) {
      for (Instruction &I : BB) {
        if (auto *PN = dyn_cast<PHINode>(&I))
          Phis.push_back(PN);
        else
          break;
      }
    }
    StringMap<AllocaInst *> SlotByBase;
    IRBuilder<> EntryB(AllocaIP);
    for (PHINode *PN : Phis) {
      BasicBlock *PhiBB = PN->getParent();

      // (Req) Skip PHIs that are inside land./lor./crit_edge blocks
      if (isSkippableName(PhiBB->getName())) {
        continue;
      }

      Changed = true;

      Type *Ty = PN->getType();

      // (A) alloca in entry
      AllocaInst *Slot;
      if (auto It = SlotByBase.find(baseNameFromIRName(PN->getName())); It != SlotByBase.end()) {
        Slot = It->second;
      } else {
        Slot = EntryB.CreateAlloca(Ty, nullptr, baseNameFromIRName(PN->getName()));
        SlotByBase[baseNameFromIRName(PN->getName())] = Slot;
      }

      // (B) Insert stores in first non land/lor/crit_edge ancestor on
      // first-pred chain
      for (unsigned i = 0; i < PN->getNumIncomingValues(); i++) {
        Value *IncomingV = PN->getIncomingValue(i);
        BasicBlock *IncomingBB = PN->getIncomingBlock(i);

        BasicBlock *InsertBB = IncomingBB;

        // Only do the "skip land/lor/crit_edge by walking up" when the current
        // pred is skippable. If it isn't skippable, we just store in it.
        if (isSkippableName(IncomingBB->getName())) {
          BasicBlock *Ancestor =
              findFirstNonSkippableFirstPredAncestor(IncomingBB);
          if (Ancestor)
            InsertBB = Ancestor;
          // If no ancestor found, fall back to IncomingBB (or you could skip
          // store)
        }
        if (baseNameFromIRName(IncomingV->getName()) ==
            baseNameFromIRName(PN->getName())) {
          // Avoid self-copy store
          continue;
        }

        Instruction *Term = InsertBB->getTerminator();
        IRBuilder<> PredB(Term);
        PredB.CreateStore(IncomingV, Slot);
      }

      // (C) load in phi block (after PHIs)
      Instruction *AfterPhisIP = &*PhiBB->getFirstInsertionPt();
      IRBuilder<> PhiB(AfterPhisIP);
      LoadInst *Ld = PhiB.CreateLoad(Ty, Slot, PN->getName() + ".load");

      PN->replaceAllUsesWith(Ld);

      // (D) erase the PHI
      PN->eraseFromParent();
    }

    return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
  }
};

} // namespace

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "remove-phi-to-stores", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "remove-phi-to-stores") {
                    FPM.addPass(RemovePhiToStoresPass());
                    return true;
                  }
                  return false;
                });
          }};
}
