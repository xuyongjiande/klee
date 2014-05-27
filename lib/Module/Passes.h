//===-- Passes.h ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_PASSES_H
#define KLEE_PASSES_H

#include "klee/Config/Version.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#else
#include "llvm/Constants.h"
#include "llvm/Instructions.h"
#include "llvm/Module.h"
#endif
#include "llvm/Pass.h"
#include "llvm/CodeGen/IntrinsicLowering.h"

namespace llvm {
  class Function;
  class Instruction;
  class Module;
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
  class TargetData;
#else
  class DataLayout;
#endif
  class TargetLowering;
  class Type;
}

//-----------------------------------------------
#include <llvm/Module.h>
#include <llvm/Instructions.h>
#include <llvm/Support/IRBuilder.h>
#include <llvm/Pass.h>
#include "llvm/Support/raw_ostream.h"
#include <llvm/Support/Debug.h>
#include <llvm/Analysis/DebugInfo.h>
#include <llvm/Metadata.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Analysis/Dominators.h>
#include <llvm/Support/CallSite.h>
#include <llvm/Support/CFG.h>
#include <llvm/ADT/SCCIterator.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/ADT/OwningPtr.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/InstIterator.h>
//-------------------------------------------------

namespace klee {

//-------------------------------------------------
using namespace llvm;
typedef std::vector< std::vector<BasicBlock*> > paths;
typedef std::map< Function*, std::vector<Instruction*> >  func_bbs_type;
typedef std::map<std::pair<Function*, Instruction*>, std::vector<BasicBlock*> >  pathsInFuncMapType;
typedef std::vector<std::vector<std::pair< Function*, Instruction*> > > entire_path;

class PathList : public ModulePass {
public:
	static char ID;

	PathList(std::string _filename, int _lineno, func_bbs_type *func_bbs, pathsInFuncMapType *pathsInFuncMap, std::vector< Function* > *_otherCalledFuncs, BasicBlock *&targetBB);
	PathList();

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
		AU.setPreservesAll();
		AU.addRequired<CallGraph>();
		AU.addRequired<DominatorTree>();
	}
	virtual bool runOnModule(Module &M);

private:
	Module* module;
	std::string fileName;
	int lineNo;

	//data struct to store paths
	paths* paths_found;

	typedef IRBuilder<> BuilderTy;
	BuilderTy *Builder;

	DominatorTree *DT;

	// Set of filenames and line numbers pointing to areas of interest
	typedef std::map<std::string, std::vector<int> > defectList;
	defectList dl;

	typedef std::vector<std::pair<Function*, Instruction*> > CalledFunctions;
	typedef std::map<const Function*, CalledFunctions> FunctionMapTy;
	FunctionMapTy calledFunctionMap;

	typedef std::pair<const llvm::BasicBlock *, const llvm::BasicBlock *> Edge;
	SmallVector<Edge, 32> BackEdges;
	typedef llvm::SmallVectorImpl<Edge> EdgeVec;

	// to expand function sets
	std::vector<Instruction*> call_insts;
	std::vector<BasicBlock*> path_basicblocks;
	std::vector<Instruction*> path_call_insts;
	std::vector< Function* > *otherCalledFuncs;

	// modification by wh
	// a new struct of storing paths
	llvm::BasicBlock *targetBB;
	llvm::BasicBlock **targetBbpp;
	entire_path *evo_paths;
	func_bbs_type *filter_paths;//跟目标路径有关的所有Function和Function出口
	// a structure to store a big map of pahts
	pathsInFuncMapType *BB_paths_map;//一个Map，映射关系：（pair<funtion, 出口inst>, function的entry到这个出口的过程中涉及到的所有的bb）
	// modification by wh
	void explore_function_paths(Function *srcFunc, Function *dstFunc, Instruction *inst, std::vector<std::pair< Function*, Instruction*> > *tmp_func_path);
	void explore_basicblock_paths(Function *F, BasicBlock *BB, std::vector<BasicBlock*> *tmp_bb_path);
	void collect_funcitons(Function *srcFunc, Function *dstFunc, Instruction *inst, std::vector<std::pair<Function*, Instruction*> > *tmp_func_path);

	Instruction* target_Inst;

	BasicBlock *getBB(std::string srcFile, int srcLine);
	bool findLineInBB(BasicBlock *BB, std::string srcFile, unsigned srcLine);

	void printCalledFuncPath(Function *srcFunc, Function *dstFunc);
	void printCalledFuncAndCFGPath(Function *srcFunc, Function *dstFunc, BasicBlock *BB, std::vector<BasicBlock*> argp);
	Constant* getSourceFile(Instruction* I);
	bool isBackEdge(llvm::BasicBlock *From, llvm::BasicBlock *To);

	// to analyze function pointer
	bool extend_calledFunctionMap(Instruction *tmpfi, User *tmpuser, GlobalVariable *func_table, Function *ff);
	bool function_pointer_analysis();

	bool filter_uclibc();
	bool traverse_basicblocks_of_function(BasicBlock *BB, std::vector<BasicBlock*> p, paths &bb_paths);
};
//-------------------------------------------------

  /// RaiseAsmPass - This pass raises some common occurences of inline
  /// asm which are used by glibc into normal LLVM IR.
class RaiseAsmPass : public llvm::ModulePass {
  static char ID;

  const llvm::TargetLowering *TLI;

  llvm::Function *getIntrinsic(llvm::Module &M,
                               unsigned IID,
                               LLVM_TYPE_Q llvm::Type **Tys,
                               unsigned NumTys);
  llvm::Function *getIntrinsic(llvm::Module &M,
                               unsigned IID, 
                               LLVM_TYPE_Q llvm::Type *Ty0) {
    return getIntrinsic(M, IID, &Ty0, 1);
  }

  bool runOnInstruction(llvm::Module &M, llvm::Instruction *I);

public:
  RaiseAsmPass() : llvm::ModulePass(ID), TLI(0) {}
  
  virtual bool runOnModule(llvm::Module &M);
};

  // This is a module pass because it can add and delete module
  // variables (via intrinsic lowering).
class IntrinsicCleanerPass : public llvm::ModulePass {
  static char ID;
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
  const llvm::TargetData &TargetData;
#else
  const llvm::DataLayout &DataLayout;
#endif
  llvm::IntrinsicLowering *IL;
  bool LowerIntrinsics;

  bool runOnBasicBlock(llvm::BasicBlock &b, llvm::Module &M);
public:
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
  IntrinsicCleanerPass(const llvm::TargetData &TD,
#else
  IntrinsicCleanerPass(const llvm::DataLayout &TD,
#endif
                       bool LI=true)
    : llvm::ModulePass(ID),
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
      TargetData(TD),
#else
      DataLayout(TD),
#endif
      IL(new llvm::IntrinsicLowering(TD)),
      LowerIntrinsics(LI) {}
  ~IntrinsicCleanerPass() { delete IL; } 
  
  virtual bool runOnModule(llvm::Module &M);
};
  
  // performs two transformations which make interpretation
  // easier and faster.
  //
  // 1) Ensure that all the PHI nodes in a basic block have
  //    the incoming block list in the same order. Thus the
  //    incoming block index only needs to be computed once
  //    for each transfer.
  // 
  // 2) Ensure that no PHI node result is used as an argument to
  //    a subsequent PHI node in the same basic block. This allows
  //    the transfer to execute the instructions in order instead
  //    of in two passes.
class PhiCleanerPass : public llvm::FunctionPass {
  static char ID;

public:
  PhiCleanerPass() : llvm::FunctionPass(ID) {}
  
  virtual bool runOnFunction(llvm::Function &f);
};
  
class DivCheckPass : public llvm::ModulePass {
  static char ID;
public:
  DivCheckPass(): ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M);
};

/// This pass injects checks to check for overshifting.
///
/// Overshifting is where a Shl, LShr or AShr is performed
/// where the shift amount is greater than width of the bitvector
/// being shifted.
/// In LLVM (and in C/C++) this undefined behaviour!
///
/// Example:
/// \code
///     unsigned char x=15;
///     x << 4 ; // Defined behaviour
///     x << 8 ; // Undefined behaviour
///     x << 255 ; // Undefined behaviour
/// \endcode
class OvershiftCheckPass : public llvm::ModulePass {
  static char ID;
public:
  OvershiftCheckPass(): ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M);
};

/// LowerSwitchPass - Replace all SwitchInst instructions with chained branch
/// instructions.  Note that this cannot be a BasicBlock pass because it
/// modifies the CFG!
class LowerSwitchPass : public llvm::FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  LowerSwitchPass() : FunctionPass(ID) {} 
  
  virtual bool runOnFunction(llvm::Function &F);
  
  struct SwitchCase {
    llvm ::Constant *value;
    llvm::BasicBlock *block;
    
    SwitchCase() : value(0), block(0) { }
    SwitchCase(llvm::Constant *v, llvm::BasicBlock *b) :
      value(v), block(b) { }
  };
  
  typedef std::vector<SwitchCase>           CaseVector;
  typedef std::vector<SwitchCase>::iterator CaseItr;
  
private:
  void processSwitchInst(llvm::SwitchInst *SI);
  void switchConvert(CaseItr begin,
                     CaseItr end,
                     llvm::Value *value,
                     llvm::BasicBlock *origBlock,
                     llvm::BasicBlock *defaultBlock);
};

}

#endif
