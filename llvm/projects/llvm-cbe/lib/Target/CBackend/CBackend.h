#include "CTargetMachine.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseMapInfoVariant.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/CodeGen/IntrinsicLowering.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCObjectFileInfo.h"
#include "llvm/MC/MCRegisterInfo.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include "llvm/MC/MCSymbol.h"
#include "llvm/Pass.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Transforms/Scalar.h"

#include <optional>
#include <set>
#include <string>
#include <variant>

#include "IDMap.h"
#include "llvm/ADT/StringMap.h"

namespace llvm_cbe {

using namespace llvm;

class CBEMCAsmInfo : public MCAsmInfo {
public:
  CBEMCAsmInfo() { PrivateGlobalPrefix = ""; }
};

using FunctionInfoVariant = std::variant<const Function *, const CallInst *>;

struct ConditionSource {
  llvm::Value *IRValue = nullptr; // if non-null: print via writeOperand
  llvm::MDNode *OverwriteCCTree = nullptr; // if non-empty: print this directly
  llvm::Instruction *OverwriteCCTreeInstruction = nullptr; 
};

/// Normalized shape for an `if` statement.
struct IfShape {
  ConditionSource Cond;
  llvm::BasicBlock *ThenBB = nullptr;
  llvm::BasicBlock *ElseBB = nullptr; // may be null (no else)
  llvm::BasicBlock *JoinBB = nullptr; // merge block (if.cont_block)
  bool IsElseIf = false;              // true if ElseBB starts another `if`
};

struct ForShape {
  ConditionSource Cond; // condition in `for (;; Cond; ...)`

  llvm::BasicBlock *CondBB =
      nullptr; // block that computes the condition (may be null)
  llvm::BasicBlock *BodyBB = nullptr; // loop body entry
  llvm::BasicBlock *IncBB = nullptr;  // increment block (may be null)
  llvm::BasicBlock *ExitBB = nullptr; // block after the loop
};

struct WhileShape {
  ConditionSource Cond;

  llvm::BasicBlock *CondBB =
      nullptr; // block that computes the condition (may be null)
  llvm::BasicBlock *BodyBB = nullptr; // loop body entry
  llvm::BasicBlock *ExitBB = nullptr; // block after the loop
};

struct SwitchShape {
  ConditionSource Cond;
  llvm::SmallVector<std::pair<llvm::ConstantInt *, llvm::BasicBlock *>, 8>
      Cases;
  llvm::BasicBlock *DefaultBB = nullptr;
  llvm::BasicBlock *ExitBB = nullptr; // block after the switch
};

struct ReturnShape {
  ConditionSource Cond;
};

enum class NormalizedBranchKind {
  If,
  For,
  While,
  LoopBreak,
  UserIntroducedGoto,
  CCSwitch,
  CCReturn,
  UnconditionalJump,
  Unknown, // placeholder for everything we don't handle yet
};

struct NormalizedBranch {
  NormalizedBranchKind Kind = NormalizedBranchKind::Unknown;
  IfShape IfInfo;
  ForShape ForInfo;
  WhileShape WhileInfo;
  SwitchShape CCSwitchInfo;
  ReturnShape CCReturnInfo;

  void printDetails() {
    switch (Kind) {
    case NormalizedBranchKind::If:
      llvm::errs() << "NormalizedBranchKind::If\n";
      llvm::errs() << "  ThenBB: "
                   << (IfInfo.ThenBB ? IfInfo.ThenBB->getName() : "<null>")
                   << "\n";
      llvm::errs() << "  ElseBB: "
                   << (IfInfo.ElseBB ? IfInfo.ElseBB->getName() : "<null>")
                   << "\n";
      llvm::errs() << "  JoinBB: "
                   << (IfInfo.JoinBB ? IfInfo.JoinBB->getName() : "<null>")
                   << "\n";
      llvm::errs() << "  IsElseIf: " << (IfInfo.IsElseIf ? "true" : "false")
                   << "\n";
      break;
    case NormalizedBranchKind::For:
      llvm::errs() << "NormalizedBranchKind::For\n";
      llvm::errs() << "  CondBB: "
                   << (ForInfo.CondBB ? ForInfo.CondBB->getName() : "<null>")
                   << "\n";
      llvm::errs() << "  BodyBB: "
                   << (ForInfo.BodyBB ? ForInfo.BodyBB->getName() : "<null>")
                   << "\n";
      llvm::errs() << "  IncBB: "
                   << (ForInfo.IncBB ? ForInfo.IncBB->getName() : "<null>")
                   << "\n";
      llvm::errs() << "  ExitBB: "
                   << (ForInfo.ExitBB ? ForInfo.ExitBB->getName() : "<null>")
                   << "\n";
      break;
    case NormalizedBranchKind::While:
      llvm::errs() << "NormalizedBranchKind::While\n";
      llvm::errs() << "  CondBB: "
                   << (WhileInfo.CondBB ? WhileInfo.CondBB->getName()
                                        : "<null>")
                   << "\n";
      llvm::errs() << "  BodyBB: "
                   << (WhileInfo.BodyBB ? WhileInfo.BodyBB->getName()
                                        : "<null>")
                   << "\n";
      llvm::errs() << "  ExitBB: "
                   << (WhileInfo.ExitBB ? WhileInfo.ExitBB->getName()
                                        : "<null>")
                   << "\n";
      break;
    case NormalizedBranchKind::LoopBreak:
      llvm::errs() << "NormalizedBranchKind::LoopBreak\n";
      break;
    case NormalizedBranchKind::UserIntroducedGoto:
      llvm::errs() << "NormalizedBranchKind::UserIntroducedGoto\n";
      break;
    case NormalizedBranchKind::CCReturn:
      llvm::errs() << "NormalizedBranchKind::CCReturn\n";
      break;
    case NormalizedBranchKind::CCSwitch:
      llvm::errs() << "NormalizedBranchKind::CCSwitch\n";

      llvm::errs() << "  DefaultBB: "
                   << (CCSwitchInfo.DefaultBB
                           ? CCSwitchInfo.DefaultBB->getName()
                           : "<null>")
                   << "\n";
      llvm::errs() << "  ExitBB: "
                   << (CCSwitchInfo.ExitBB ? CCSwitchInfo.ExitBB->getName()
                                            : "<null>")
                   << "\n";

      llvm::errs() << "  Cases (" << CCSwitchInfo.Cases.size() << "):\n";
      for (unsigned i = 0; i < CCSwitchInfo.Cases.size(); ++i) {
        auto &Pair = CCSwitchInfo.Cases[i];
        llvm::ConstantInt *CI = Pair.first;
        llvm::BasicBlock *BB = Pair.second;

        llvm::errs() << "    [" << i << "] value = ";
        if (CI) {
          // Print the integer value, signed for readability
          CI->getValue().print(llvm::errs(), /*isSigned=*/true);
        } else {
          // nullptr can mean default or “no specific value”
          llvm::errs() << "<default/null>";
        }

        llvm::errs() << ", BB = " << (BB ? BB->getName() : "<null>") << "\n";
      }
      break;
    case NormalizedBranchKind::Unknown:
      llvm::errs() << "NormalizedBranchKind::Unknown\n";
      break;
    case NormalizedBranchKind::UnconditionalJump:
      llvm::errs() << "NormalizedBranchKind::UnconditionalJump\n";
      break;
    }
  }
};

/// CWriter - This class is the main chunk of code that converts an LLVM
/// module to a C translation unit.
class CWriter : public FunctionPass, public InstVisitor<CWriter> {
  llvm::StringMap<llvm::BasicBlock *> BlockNameToBlockPtrMap;
  mutable DenseMap<const StructType *, SmallVector<std::string, 8>>
      StructFieldNameCache;
  std::string _Out;
  std::string _OutHeaders;
  raw_string_ostream OutHeaders;
  raw_string_ostream Out;
  raw_ostream &FileOut;
  IntrinsicLowering *IL = nullptr;
  LoopInfo *LI = nullptr;
  const Module *TheModule = nullptr;
  const MCAsmInfo *TAsm = nullptr;
  const MCRegisterInfo *MRI = nullptr;
  const MCObjectFileInfo *MOFI = nullptr;
  MCContext *TCtx = nullptr;
  const DataLayout *TD = nullptr;
  const Instruction *CurInstr = nullptr;

  IDMap<const ConstantFP *> FPConstantMap;

  IDMap<const Value *> AnonValueNumbers;

  /// UnnamedStructIDs - This contains a unique ID for each struct that is
  /// either anonymous or has no name.
  IDMap<StructType *> UnnamedStructIDs;

  std::set<Type *> TypedefDeclTypes;
  std::set<Type *> SelectDeclTypes;
  // std::set<BasicBlock *> PrintedLabels;
  std::set<std::pair<CmpInst::Predicate, VectorType *>> CmpDeclTypes;
  std::set<std::pair<CastInst::CastOps, std::pair<Type *, Type *>>>
      CastOpDeclTypes;
  std::set<std::pair<unsigned, Type *>> InlineOpDeclTypes;
  std::set<Type *> CtorDeclTypes;
  std::set<BasicBlock *> InlinedBlocks;
  IDMap<FunctionInfoVariant> UnnamedFunctionIDs;

  // This is used to keep track of intrinsics that get generated to a lowered
  // function. We must generate the prototypes before the function body which
  // will only be expanded on first use
  std::vector<Function *> prototypesToGen;

  unsigned LastAnnotatedSourceLine = 0;

  struct {
    // Standard headers
    bool Stdarg : 1;
    bool Setjmp : 1;
    bool Limits : 1;
    bool Math : 1;

    // printModuleTypes()
    bool BitCastUnion : 1;

    // generateCompilerSpecificCode()
    bool BuiltinAlloca : 1;
    bool Unreachable : 1;
    bool NoReturn : 1;
    bool ExternalWeak : 1;
    bool AttributeWeak : 1;
    bool Hidden : 1;
    bool AttributeList : 1;
    bool UnalignedLoad : 1;
    bool Aligns : 1;
    bool FunctionAlign : 1;
    bool NanInf : 1;
    bool Int128 : 1;
    bool ThreadFence : 1;
    bool StackSaveRestore : 1;
    bool ConstantDoubleTy : 1;
    bool ConstantFloatTy : 1;
    bool ConstantFP80Ty : 1;
    bool ConstantFP128Ty : 1;
    bool ForceInline : 1;
    bool Trap : 1;
    bool ConstructorsDestructors : 1;
  } UsedHeaders;

#define USED_HEADERS_FLAG(Name)                                                \
  void headerUse##Name() { UsedHeaders.Name = true; }                          \
  bool headerInc##Name() const { return UsedHeaders.Name; }

  // Standard headers
  USED_HEADERS_FLAG(Stdarg)
  USED_HEADERS_FLAG(Setjmp)
  USED_HEADERS_FLAG(Limits)
  USED_HEADERS_FLAG(Math)

  // printModuleTypes()
  USED_HEADERS_FLAG(BitCastUnion)

  // generateCompilerSpecificCode()
  USED_HEADERS_FLAG(BuiltinAlloca)
  USED_HEADERS_FLAG(Unreachable)
  USED_HEADERS_FLAG(NoReturn)
  USED_HEADERS_FLAG(ExternalWeak)
  USED_HEADERS_FLAG(AttributeWeak)
  USED_HEADERS_FLAG(Hidden)
  USED_HEADERS_FLAG(AttributeList)
  USED_HEADERS_FLAG(UnalignedLoad)
  USED_HEADERS_FLAG(Aligns)
  USED_HEADERS_FLAG(FunctionAlign)
  USED_HEADERS_FLAG(NanInf)
  USED_HEADERS_FLAG(Int128)
  USED_HEADERS_FLAG(ThreadFence)
  USED_HEADERS_FLAG(StackSaveRestore)
  USED_HEADERS_FLAG(ConstantDoubleTy)
  USED_HEADERS_FLAG(ConstantFloatTy)
  USED_HEADERS_FLAG(ConstantFP80Ty)
  USED_HEADERS_FLAG(ConstantFP128Ty)
  USED_HEADERS_FLAG(ForceInline)
  USED_HEADERS_FLAG(Trap)
  USED_HEADERS_FLAG(ConstructorsDestructors)

  llvm::SmallSet<CmpInst::Predicate, 26> FCmpOps;
  void headerUseFCmpOp(CmpInst::Predicate P);

  void generateCompilerSpecificCode(raw_ostream &Out, const DataLayout *) const;

public:
  static char ID;
  explicit CWriter(raw_ostream &o)
      : FunctionPass(ID), OutHeaders(_OutHeaders), Out(_Out), FileOut(o) {
    memset(&UsedHeaders, 0, sizeof(UsedHeaders));
  }

  virtual StringRef getPassName() const { return "C backend"; }

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<PostDominatorTreeWrapperPass>();
    AU.setPreservesCFG();
  }

  virtual bool doInitialization(Module &M);
  virtual bool doFinalization(Module &M);
  virtual bool runOnFunction(Function &F);

private:
  void generateHeader(Module &M);
  void declareOneGlobalVariable(GlobalVariable *I);

  void forwardDeclareStructs(raw_ostream &Out, Type *Ty,
                             std::set<Type *> &TypesPrinted);

  raw_ostream &printFunctionAttributes(raw_ostream &Out, AttributeList Attrs);

  bool isStandardMain(const FunctionType *FTy);
  raw_ostream &printFunctionProto(raw_ostream &Out, FunctionInfoVariant FIV,
                                  const std::string_view Name);

  raw_ostream &printFunctionDeclaration(raw_ostream &Out,
                                        FunctionInfoVariant FIV,
                                        const std::string_view Name);
  raw_ostream &printStructDeclaration(raw_ostream &Out, StructType *STy, const Module &M);
  raw_ostream &printArrayDeclaration(raw_ostream &Out, ArrayType *Ty);
  raw_ostream &printVectorDeclaration(raw_ostream &Out, VectorType *Ty);

  raw_ostream &printTypeName(raw_ostream &Out, Type *Ty, bool isSigned = false,
                             std::pair<AttributeList, CallingConv::ID> PAL =
                                 std::make_pair(AttributeList(),
                                                CallingConv::C));
  raw_ostream &printTypeNameForAddressableValue(raw_ostream &Out, Type *Ty,
                                                bool isSigned = false);
  raw_ostream &customPrintSimpleType(raw_ostream &Out, std::string Type);
  raw_ostream &printSimpleType(raw_ostream &Out, Type *Ty, bool isSigned);
  raw_ostream &printTypeString(raw_ostream &Out, Type *Ty, bool isSigned);

  std::string getStructName(StructType *ST);
  std::string getFunctionName(FunctionInfoVariant FIV);
  std::string getArrayName(ArrayType *AT);
  std::string getVectorName(VectorType *VT);

  enum OperandContext {
    ContextNormal,
    ContextCasted,
    // Casted context means the type-cast will be implicit,
    // such as the RHS of a `var = RHS;` expression
    // or inside a struct initializer expression
    ContextStatic
    // Static context means that it is being used in as a static initializer
    // (also implies ContextCasted)
  };

  struct writeOperandCustomArgs {
    bool wrapInParens = true;
    std::string metadata;
    writeOperandCustomArgs(bool w = true, std::string m = "")
        : wrapInParens(w), metadata(std::move(m)) {}
  };
  struct visitBranchInstCustomArgs {
    std::string overwriteCondition;
    visitBranchInstCustomArgs(std::string ow = "")
        : overwriteCondition(std::move(ow)) {}
  };

  void emitCondition(const ConditionSource &C, llvm::Instruction* I = nullptr);
  NormalizedBranch *normalizeIfBranch(llvm::BranchInst &I);
  NormalizedBranch *normalizeBranch(llvm::BranchInst &I);
  NormalizedBranch *normalizeForBranch(llvm::BranchInst &I);
  NormalizedBranch *normalizeWhileBranch(llvm::BranchInst &I);
  NormalizedBranch *normalizeCompoundConditionIfBranch(llvm::BranchInst &BI);
  NormalizedBranch *normalizeCompoundConditionSwitchInst(
      llvm::BranchInst &BI);
  void emitIf(IfShape ifShape);
  void emitFor(ForShape forShape);
  void emitWhile(WhileShape whileShape);
  void emitSwitch(SwitchShape switchShape);
  void emitReturn(ReturnShape returnShape);

  std::string getFieldNameFromMetadata(const StructType *ST, unsigned FieldIdx) const;

      void writeOperandDeref(Value *Operand);

  void
  writeOperand(Value *Operand, enum OperandContext Context = ContextNormal,
               writeOperandCustomArgs customArgs = writeOperandCustomArgs());
  void writeInstComputationInline(Instruction &I);
  void writeOperandInternal(
      Value *Operand, enum OperandContext Context = ContextNormal,
      writeOperandCustomArgs customArgs = writeOperandCustomArgs());
  void writeOperandWithCast(
      Value *Operand, unsigned Opcode,
      writeOperandCustomArgs customArgs = writeOperandCustomArgs());
  void writeVectorOperandWithCast(Value *Operand, unsigned Index,
                                  unsigned Opcode);
  void opcodeNeedsCast(unsigned Opcode, bool &shouldCast, bool &castIsSigned);

  void writeOperandWithCast(
      Value *Operand, ICmpInst &I,
      writeOperandCustomArgs customArgs = writeOperandCustomArgs());
  bool writeInstructionCast(Instruction &I);
  void writeMemoryAccess(Value *Operand, Type *OperandType, bool IsVolatile,
                         unsigned Alignment);

  std::string InterpretASMConstraint(InlineAsm::ConstraintInfo &c);

  bool lowerIntrinsics(Function &F);
  /// Prints the definition of the intrinsic function F. Supports the
  /// intrinsics which need to be explicitly defined in the CBackend.
  void printIntrinsicDefinition(Function &F, raw_ostream &Out);
  void printIntrinsicDefinition(FunctionType *funT, unsigned Opcode,
                                std::string OpName, raw_ostream &Out);

  void printModuleTypes(raw_ostream &Out);
  void printContainedTypes(raw_ostream &Out, Type *Ty, std::set<Type *> &);

  void printFloatingPointConstants(Function &F);
  void printFloatingPointConstants(const Constant *C);

  void printFunction(Function &);

  struct printBasicBlockCustomArgs {
    bool isForIncBlock = false;
    bool noTerminator = false;
    bool noLabel = true;
    printBasicBlockCustomArgs(bool i = false, bool nT = false, bool nL = true)
        : isForIncBlock(i), noTerminator(nT), noLabel(nL) {}
  };

  void printBasicBlock(BasicBlock *BB, printBasicBlockCustomArgs customArgs =
                                           printBasicBlockCustomArgs());
  void printLoop(Loop *L);

  void printCast(unsigned opcode, Type *SrcTy, Type *DstTy);
  void printConstant(Constant *CPV, enum OperandContext Context);
  void printConstantWithCast(Constant *CPV, unsigned Opcode);
  bool printConstExprCast(ConstantExpr *CE);
  void printConstantArray(ConstantArray *CPA, enum OperandContext Context);
  void printConstantVector(ConstantVector *CV, enum OperandContext Context);
  void printConstantDataSequential(ConstantDataSequential *CDS,
                                   enum OperandContext Context);
  bool printConstantString(Constant *C, enum OperandContext Context);

  bool isEmptyType(Type *Ty) const;
  Type *skipEmptyArrayTypes(Type *Ty) const;
  std::optional<Type *> tryGetTypeOfAddressExposedValue(Value *V) const;
  bool isInlinableInst(Instruction &I) const;
  AllocaInst *isDirectAlloca(Value *V) const;
  bool isInlineAsm(Instruction &I) const;

  // Instruction visitation functions
  friend class InstVisitor<CWriter>;

  void visitReturnInst(ReturnInst &I);
  void visitBranchInst(BranchInst &I, visitBranchInstCustomArgs customArgs =
                                          visitBranchInstCustomArgs());
  std::string blockNameToConditionString(llvm::Instruction *I,
                                         StringRef BBName);
                                         bool compoundHasExistingBlock(llvm::MDNode *Node,
                                       llvm::Instruction *I);
  bool emitCompoundConditionRecursive(llvm::MDNode *Node,
                                             llvm::Instruction *I);

  void visitSwitchInst(SwitchInst &I);
  void visitIndirectBrInst(IndirectBrInst &I);
  void visitInvokeInst(InvokeInst &I) {
    llvm_unreachable("Lowerinvoke pass didn't work!");
  }
  void visitResumeInst(ResumeInst &I) {
    llvm_unreachable("DwarfEHPrepare pass didn't work!");
  }
  void visitUnreachableInst(UnreachableInst &I);

  void visitPHINode(PHINode &I);
  void visitUnaryOperator(UnaryOperator &I);
  void visitBinaryOperator(BinaryOperator &I);
  void visitICmpInst(ICmpInst &I);
  void visitIcmpInstHandleBinOp(Value *BinOp);
  void visitIcmpInstHandleLoad(Value *Load);

  void visitFCmpInst(FCmpInst &I);

  void visitCastInst(CastInst &I);
  void visitSelectInst(SelectInst &I);
  void visitCallInst(CallInst &I);
  void visitInlineAsm(CallInst &I);
  bool visitBuiltinCall(CallInst &I, Intrinsic::ID ID);

  void visitAllocaInst(AllocaInst &I);
  void visitLoadInst(LoadInst &I);
  void visitStoreInst(StoreInst &I);
  void visitFenceInst(FenceInst &I);
  void visitGetElementPtrInst(GetElementPtrInst &I);
  void visitVAArgInst(VAArgInst &I);

  void visitInsertElementInst(InsertElementInst &I);
  void visitExtractElementInst(ExtractElementInst &I);
  void visitShuffleVectorInst(ShuffleVectorInst &SVI);

  void visitInsertValueInst(InsertValueInst &I);
  void visitExtractValueInst(ExtractValueInst &I);

  void visitInstruction(Instruction &I) {
    CurInstr = &I;
    errorWithMessage("unsupported LLVM instruction");
  }

  [[noreturn]] void errorWithMessage(const char *message);

  bool isGotoCodeNecessary(BasicBlock *From, BasicBlock *To);
  bool canDeclareLocalLate(Instruction &I);
  void printPHICopiesForSuccessor(BasicBlock *CurBlock, BasicBlock *Successor,
                                  unsigned Indent);
  void printBranchToBlock(BasicBlock *CurBlock, BasicBlock *SuccBlock,
                          unsigned Indent);
  void printGEPExpression(Value *Ptr, unsigned NumOperands, gep_type_iterator I,
                          gep_type_iterator E,
                          std::optional<Type *> SourceType = std::nullopt);

  std::string GetValueName(const Value *Operand);

  friend class CWriterTestHelper;
};

} // namespace llvm_cbe
