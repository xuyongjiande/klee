//===-- Searcher.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Common.h"

#include "Searcher.h"

#include "CoreStats.h"
#include "Executor.h"
#include "PTree.h"
#include "StatsTracker.h"

#include "klee/ExecutionState.h"
#include "klee/Statistics.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/ADT/DiscretePDF.h"
#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/System/Time.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#else
#include "llvm/Constants.h"
#include "llvm/Instructions.h"
#include "llvm/Module.h"
#endif
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"

#include "llvm/PassManager.h"
#include "llvm/Pass.h"

#include "../Module/Passes.h"
#include <time.h>

#include <cassert>
#include <fstream>
#include <climits>

using namespace klee;
using namespace llvm;

namespace {
  cl::opt<bool>
  DebugLogMerge("debug-log-merge");
}

namespace klee {
  extern RNG theRNG;
}

Searcher::~Searcher() {
}

///

ExecutionState &DFSSearcher::selectState() {
  return *states.back();
}

void DFSSearcher::update(ExecutionState *current,
                         const std::set<ExecutionState*> &addedStates,
                         const std::set<ExecutionState*> &removedStates) {
  states.insert(states.end(),
                addedStates.begin(),
                addedStates.end());
  for (std::set<ExecutionState*>::const_iterator it = removedStates.begin(),
         ie = removedStates.end(); it != ie; ++it) {
    ExecutionState *es = *it;
    if (es == states.back()) {
      states.pop_back();
    } else {
      bool ok = false;

      for (std::vector<ExecutionState*>::iterator it = states.begin(),
             ie = states.end(); it != ie; ++it) {
        if (es==*it) {
          states.erase(it);
          ok = true;
          break;
        }
      }

      assert(ok && "invalid state removed");
    }
  }
}

///

ExecutionState &BFSSearcher::selectState() {
  return *states.front();
}

void BFSSearcher::update(ExecutionState *current,
                         const std::set<ExecutionState*> &addedStates,
                         const std::set<ExecutionState*> &removedStates) {
  states.insert(states.end(),
                addedStates.begin(),
                addedStates.end());
  for (std::set<ExecutionState*>::const_iterator it = removedStates.begin(),
         ie = removedStates.end(); it != ie; ++it) {
    ExecutionState *es = *it;
    if (es == states.front()) {
      states.pop_front();
    } else {
      bool ok = false;

      for (std::deque<ExecutionState*>::iterator it = states.begin(),
             ie = states.end(); it != ie; ++it) {
        if (es==*it) {
          states.erase(it);
          ok = true;
          break;
        }
      }

      assert(ok && "invalid state removed");
    }
  }
}

///

ExecutionState &RandomSearcher::selectState() {
  return *states[theRNG.getInt32()%states.size()];
}

void RandomSearcher::update(ExecutionState *current,
                            const std::set<ExecutionState*> &addedStates,
                            const std::set<ExecutionState*> &removedStates) {
  states.insert(states.end(),
                addedStates.begin(),
                addedStates.end());
  for (std::set<ExecutionState*>::const_iterator it = removedStates.begin(),
         ie = removedStates.end(); it != ie; ++it) {
    ExecutionState *es = *it;
    bool ok = false;

    for (std::vector<ExecutionState*>::iterator it = states.begin(),
           ie = states.end(); it != ie; ++it) {
      if (es==*it) {
        states.erase(it);
        ok = true;
        break;
      }
    }
    
    assert(ok && "invalid state removed");
  }
}

///

WeightedRandomSearcher::WeightedRandomSearcher(WeightType _type)
  : states(new DiscretePDF<ExecutionState*>()),
    type(_type) {
  switch(type) {
  case Depth: 
    updateWeights = false;
    break;
  case InstCount:
  case CPInstCount:
  case QueryCost:
  case MinDistToUncovered:
  case CoveringNew:
    updateWeights = true;
    break;
  default:
    assert(0 && "invalid weight type");
  }
}

WeightedRandomSearcher::~WeightedRandomSearcher() {
  delete states;
}

ExecutionState &WeightedRandomSearcher::selectState() {
  return *states->choose(theRNG.getDoubleL());
}

double WeightedRandomSearcher::getWeight(ExecutionState *es) {
  switch(type) {
  default:
  case Depth: 
    return es->weight;
  case InstCount: {
    uint64_t count = theStatisticManager->getIndexedValue(stats::instructions,
                                                          es->pc->info->id);
    double inv = 1. / std::max((uint64_t) 1, count);
    return inv * inv;
  }
  case CPInstCount: {
    StackFrame &sf = es->stack.back();
    uint64_t count = sf.callPathNode->statistics.getValue(stats::instructions);
    double inv = 1. / std::max((uint64_t) 1, count);
    return inv;
  }
  case QueryCost:
    return (es->queryCost < .1) ? 1. : 1./es->queryCost;
  case CoveringNew:
  case MinDistToUncovered: {
    uint64_t md2u = computeMinDistToUncovered(es->pc,
                                              es->stack.back().minDistToUncoveredOnReturn);

    double invMD2U = 1. / (md2u ? md2u : 10000);
    if (type==CoveringNew) {
      double invCovNew = 0.;
      if (es->instsSinceCovNew)
        invCovNew = 1. / std::max(1, (int) es->instsSinceCovNew - 1000);
      return (invCovNew * invCovNew + invMD2U * invMD2U);
    } else {
      return invMD2U * invMD2U;
    }
  }
  }
}

void WeightedRandomSearcher::update(ExecutionState *current,
                                    const std::set<ExecutionState*> &addedStates,
                                    const std::set<ExecutionState*> &removedStates) {
  if (current && updateWeights && !removedStates.count(current))
    states->update(current, getWeight(current));
  
  for (std::set<ExecutionState*>::const_iterator it = addedStates.begin(),
         ie = addedStates.end(); it != ie; ++it) {
    ExecutionState *es = *it;
    states->insert(es, getWeight(es));
  }

  for (std::set<ExecutionState*>::const_iterator it = removedStates.begin(),
         ie = removedStates.end(); it != ie; ++it) {
    states->remove(*it);
  }
}

bool WeightedRandomSearcher::empty() { 
  return states->empty(); 
}

///

RandomPathSearcher::RandomPathSearcher(Executor &_executor)
  : executor(_executor) {
}

RandomPathSearcher::~RandomPathSearcher() {
}

ExecutionState &RandomPathSearcher::selectState() {
  unsigned flips=0, bits=0;
  PTree::Node *n = executor.processTree->root;
  
  while (!n->data) {
    if (!n->left) {
      n = n->right;
    } else if (!n->right) {
      n = n->left;
    } else {
      if (bits==0) {
        flips = theRNG.getInt32();
        bits = 32;
      }
      --bits;
      n = (flips&(1<<bits)) ? n->left : n->right;
    }
  }

  return *n->data;
}

void RandomPathSearcher::update(ExecutionState *current,
                                const std::set<ExecutionState*> &addedStates,
                                const std::set<ExecutionState*> &removedStates) {
}

bool RandomPathSearcher::empty() { 
  return executor.states.empty(); 
}

// xyj's searcher
GuidedPathSearcher::GuidedPathSearcher(Executor &_executor, std::string _filename, int _linenum)
  : executor(_executor), miss_ctr(0), filename(_filename), linenum(_linenum) {
	killNum = 0;
	targetBbReachedNum = 0;
	
	time_t llvmpass_start = time(NULL);
	std::cerr << "========================================\n";
	std::cerr << "=                                      =\n";
	std::cerr << "=            BEGIN ANALYSIS...         =\n";
	std::cerr << "=                                      =\n";
	std::cerr << "========================================\n";
	std::cerr << "[GuidedPath] " << "Begin static analysis: " << "now time: " << localtime(&llvmpass_start)->tm_hour << ":" \
		<< localtime(&llvmpass_start)->tm_min << ":" << localtime(&llvmpass_start)->tm_sec << '\n';
	Module *M = executor.kmodule->module;
	PassManager Passes;
	Passes.add(new PathList(filename, linenum, &targetRelatedFuncs, &targetRelatedBbs, &otherCalledFuncs, targetBb));
	Passes.run(*M);
	std::cerr << "[GuidedPath] " << "End static analysis: " << "used time: " << difftime(time(NULL), llvmpass_start) << '\n';
	std::cerr << "[GuidedPath] Our Target: func(" << targetBb->getParent()->getName().str() << ")\tbb(" << targetBb->getName().str() <<")\n";
	//to get more effective data structure.
	for (pathsInFuncMapType::iterator it = targetRelatedBbs.begin(); it != targetRelatedBbs.end(); it++) {
		Function *func = (it->first).first;
		std::vector<BasicBlock*> bbVector = it->second;
		relatedFuncAndBbs[func].insert(relatedFuncAndBbs[func].end(), bbVector.begin() + 1, bbVector.end());
	}
	int relatedBbNum = 0;
	int mainPathAllBbNum = 0;
	for (std::map< Function* , std::vector< BasicBlock* > >::iterator it = relatedFuncAndBbs.begin(); it != relatedFuncAndBbs.end(); it++) {
		std::vector<BasicBlock*> *bbVector = &(it->second);
		std::vector<BasicBlock*> tmpVector;
		llvm::dbgs() << "DEBUG------------func: " << (*it).first->getName() << "\n";
		for (std::vector< BasicBlock* >::iterator it = bbVector->begin(); it != bbVector->end(); it++) {
			if (tmpVector.end() == find(tmpVector.begin(), tmpVector.end(), *it) ) {
					tmpVector.push_back(*it);
					llvm::dbgs() << "DEBUG -----bb: " << (*it)->getName() << "\n";
			}
		}
		*bbVector = tmpVector;
		relatedBbNum += tmpVector.size();
		mainPathAllBbNum += ((*it).first->getBasicBlockList()).size();
	}
	dbgs() << "[GuidedPath] mainPath related with\t" << relatedFuncAndBbs.size() << "\tfunctions.\n";
	dbgs() << "[GuidedPath] mainPath related with\t" << relatedBbNum << "\tbbs.\n";
	dbgs() << "[GuidedPath] mainPath_related_funcs totally have\t" << mainPathAllBbNum << "\tbbs.\n";
	dbgs() << "[GuidedPath] otherCalledFunctions\t" << otherCalledFuncs.size() << "\tfunctions.\n";

	//显示初始时间
	searcher_start = time(NULL);
	std::cerr << "========================================\n";
	std::cerr << "=                                      =\n";
	std::cerr << "=            BEGIN RUN...              =\n";
	std::cerr << "=                                      =\n";
	std::cerr << "========================================\n";
	std::cerr << ">>>>>GuidedPath: " << "run: " << "now time: " << localtime(&searcher_start)->tm_hour << ":" \
		<< localtime(&searcher_start)->tm_min << ":" << localtime(&searcher_start)->tm_sec << '\n';
}

GuidedPathSearcher::~GuidedPathSearcher() {
	time_t searcher_done = time(NULL);
	std::cerr << "++++++staticstics++++++++++++++++++\n";
	std::cerr << "[GuidedPath] " << "searcher done: " << "now time: " << localtime(&searcher_done)->tm_hour << ":" \
		<< localtime(&searcher_done)->tm_min << ":" << localtime(&searcher_done)->tm_sec << '\n';
	std::cerr << "[GuidedPath] " << "searcher done: " << "used time: " << difftime(searcher_done, searcher_start) << '\n';
	/*
	for (std::map<pathType*, int>::iterator it = pathsBingoNum.begin(); it != pathsBingoNum.end(); ++it, ++index)
	{
		std::cerr << "path " << index << "\tbeing executed for " << (*it).second << "\ttimes\n";
//		for (std::vector<int>::iterator ittime = pathsBingoTime[(*it).first].begin(); ittime != pathsBingoTime[(*it).first].end(); ittime++)
//			std::cerr << "\ttime passed: " << (*ittime) << "\n";
	}
	*/
	/*
	for (std::map<llvm::BasicBlock*, int>::iterator BBit= targetBBBingoNum.begin(); BBit != targetBBBingoNum.end(); BBit++)
	{
		llvm::BasicBlock* nowTargetBB = (*BBit).first;
		int nowTargetBBNum = (*BBit).second;
		std::cerr << "===>>> target: " << nowTargetBB->getParent()->getName().str() << "\t" << nowTargetBB->getName().str() <<"\thas been done " << nowTargetBBNum << "\ttimes.\n";
	}
	*/
	std::cerr << "[GuidedPath] Target: " << targetBb->getParent()->getName().str() << "\t" << targetBb->getName().str() <<"\thas been done " << targetBbReachedNum << "\ttimes.\n";
	std::cerr << "[GuidedPath] Totally killed\t" << killNum << "\tstates\n";
	std::cerr << "+++++++++++++++++++++++++++++++++++\n";
}

/*
bool GuidedPathSearcher::done(int index)//判断一条路径是否完成，根据最后一个leaf BB的指令是否全部被执行到了。
{
  std::map<llvm::Instruction*, bool> *instMap = &instMaps[index];
  if (instMap == NULL)
    return true;
  if (instMap->empty())
    return true;

  for(std::map<llvm::Instruction*, bool>::iterator it = instMap->begin(); it != instMap->end(); ++it)
	if (!it->second)
	  return false;
  return true;
}

bool GuidedPathSearcher::allDone(void)
{
  int ctr=0;
  for(std::vector<pathType>::iterator pit=paths.begin(); pit != paths.end(); ++pit, ctr++) {
	if (!done(ctr))
	  return false;
	}
  return true;
}
int GuidedPathSearcher::left(int index)//得到某一条路径最后一个bb还剩下多少条指令未执行
{
  std::map<llvm::Instruction*, bool> *instMap = &instMaps[index];

  int ctr = 0;
  for(std::map<llvm::Instruction*, bool>::iterator it = instMap->begin(); it != instMap->end(); ++it)
	if (!it->second)
	  ctr++;
  return ctr;
}
*/

void GuidedPathSearcher::killAllStates(void)
{
  for (std::vector<ExecutionState*>::iterator it = states.begin(); it != states.end(); ++it) {
	executor.terminateStateEarly(**it, "GuidedSearcher -- Path reached");
  }
  empty();
}
#if 1
bool instInUcLibcOrPOSIX(Instruction* I) {
	MDNode *MD = I->getDebugLoc().getAsMDNode(I->getContext());
	if (!MD)
		return true;
	DILocation Loc(MD);
	SmallString<64> absolutePath;
	StringRef Filename = DIScope(Loc.getScope()).getFilename();
	if (sys::path::is_absolute(Filename))
		absolutePath.append(Filename.begin(), Filename.end());
	else
		sys::path::append(absolutePath, DIScope(Loc.getScope()).getDirectory(), Filename);

	std::string strPath = absolutePath.str();
	if (strPath.find("klee-uclibc") != std::string::npos || strPath.find("POSIX") != std::string::npos) {
		return true;
	}
	return false;
}

ExecutionState &GuidedPathSearcher::selectState()
{
	/*
	if (paths.size()==0) {
		std::cerr << ">>>>>GuidedSearcher: Error, no paths! Terminating all states\n";
		killAllStates();
	}
	*/

	bool inMainBbAfter = false;
	for (std::vector<ExecutionState*>::iterator it = states.begin(); it != states.end(); ++it) {
		ExecutionState *state = *it;
		Instruction *state_i = state->pc->inst;

		bool inUcLibcOrPOSIX = instInUcLibcOrPOSIX(state_i);
		if (inUcLibcOrPOSIX) {//not to kill
			return *state;
		}
		else {
			BasicBlock *state_bb = state_i->getParent();
			Function *state_func = state_bb->getParent();
			if (find(otherCalledFuncs.begin(), otherCalledFuncs.end(), state_func) != otherCalledFuncs.end()) {//in otherCalledFuncs, not to kill
				return *state;
			}
			else {//not libcOrPosix && not otherCalledFuncs; so, now state is in MainPathFuncs or in funcs not related at all.
				if (relatedFuncAndBbs.find(state_func) != relatedFuncAndBbs.end()) {//in mainPathFuncs
					if (find(relatedFuncAndBbs[state_func].begin(), relatedFuncAndBbs[state_func].end(), state_bb) != relatedFuncAndBbs[state_func].end())
						return *state;//in mainPath totally used bbs
					else {
						for (int i = 0; i < targetRelatedFuncs[state_func].size(); i++) {
							Instruction *call_inst = targetRelatedFuncs[state_func].at(i);
							BasicBlock *call_bb = call_inst->getParent();
							if (call_bb == state_bb) {// in mainPath notTotoally used bbs
								for (BasicBlock::iterator inst = call_bb->begin(); inst != call_bb->end(); inst++) {
									if (&*inst == state_i)// and before the callInst
										return *state;
									if (&*inst == call_inst)
										break;
								}
							}
							inMainBbAfter = true;
						}
					}
				}
			}
		}
		BasicBlock *state_bb = state_i->getParent();
		Function *state_func = state_bb->getParent();
		dbgs() << "[GuidePath]\tstate_func:\t" << state_func->getName() << "\tstate_bb:\t" << state_bb->getName() << "\t\t" << inMainBbAfter << "\n";
		executor.terminateStateOnError(*state, "This state is not related with our target.",  "[GuidedPath]");
		killNum ++;
	}
	return *states[theRNG.getInt32()%states.size()];
}

#else
ExecutionState &GuidedPathSearcher::selectState()
{
	if (paths.size()==0) {
		std::cerr << "GuidedSearcher: Error, no paths! Terminating all states\n";
		killAllStates();
	}

  //  std::cerr << "selectState: processing " << states.size() << " state(s)\n";

  for (std::vector<ExecutionState*>::iterator it = states.begin(); it != states.end(); ++it) {
	ExecutionState *state = *it;
	Instruction *state_i = state->pc->inst;
	BasicBlock *state_bb = state_i->getParent();

	// Loop over all paths...
	// States can go in and out of different paths, we can't really control that,
	// so we keep picking states in paths that are not done yet.
	// .. and when a state executes the last instruction in a BB leaf, we terminate that state
	// (in order to generate the test case)
	// ... and when all paths are complete, we stop all together.

	int ctr=0;  // for index into instMaps
	for(std::vector<pathType>::iterator pit=paths.begin(); pit != paths.end(); ++pit, ctr++) {
	  pathType path = *pit;

	  // Are we done with this path?
	  if (done(ctr))
		continue;

	  // The idea here is to pick a state that has it's PC in a BB that's in the path.
	  // Preferrably as close to the leaf BB as possible, thus
	  // we travese the path in reverse order and return first match.

	  for (pathType::reverse_iterator bbit = path.rbegin(); bbit != path.rend(); ++bbit) {
		BasicBlock *BB = *bbit;
#if 0
		std::cerr << "  trying s[" << state  << "] " << " p[" << ctr << "] " << BB << " "
				  << BB->getParent()->getNameStr() << " >state: "
				  << "{" << state_bb << " " << state_bb->getParent()->getNameStr() << "}\n";
#endif
		// is the state_bb in our path?
		if (state_bb == BB) {
		  instMaps[ctr][state_i] = true;//每执行到一个path的一条指令，就记录这个path的这条指令被执行过了。
		  // Are we done? Terminate this state and write out info
		  // FIX: Doesn't this mean that we wont run the last instruction in the BB?
		  if (done(ctr)) {
			std::cerr << "---xyj---to see how many states here: before kill" <<  states.size() << "  states\n";
			executor.terminateStateOnError(*state, "BB completed", "guidedsearcher");
			std::cerr << "---xyj---to see how many states here:  After kill" <<  states.size() << "  states\n";
			continue;
		  }
#if 0 
		  if (miss_ctr != 0) {
			std::cerr << miss_ctr << " path misses [" << states.size() << " state(s)]\n";
			miss_ctr=0;
		  }
		  if (bbit == path.rbegin())
			std::cerr << "! new hit in leaf [p: " << ctr << " (" << left(ctr) << ")]\n";
		  else
			std::cerr << "* hit " << state->pc->inst->getParent()->getParent()->getNameStr()
					  << " [p: " << ctr << " (" << left(ctr) << ")]\n";
#endif
		  return *state;
		}
	  }
	}

	if (allDone()) {
	  std::cerr << "GuidedSearcher done -- terminating remaining states\n";
	  killAllStates();
	}
  }
  // std::cerr << "- found no match\n";
  miss_ctr++;
  //if ((miss_ctr%1000) == 0)
	//std::cerr << miss_ctr << " path misses [" << states.size() << " state(s)]...\n";
  return *states[theRNG.getInt32()%states.size()];  // pick a random state (this will help with fork bombing)
}
#endif

void GuidedPathSearcher::update(ExecutionState *current,
                         const std::set<ExecutionState*> &addedStates,
                         const std::set<ExecutionState*> &removedStates) {

  if (addedStates.size()==0 && removedStates.size()==0)
	return;

//  std::cerr << "Adding " << addedStates.size() << " & removing " << removedStates.size() << " state(s)\n";

  states.insert(states.end(),
                addedStates.begin(),
                addedStates.end());
  for (std::set<ExecutionState*>::const_iterator it = removedStates.begin(),
         ie = removedStates.end(); it != ie; ++it) {
    ExecutionState *es = *it;
    if (es == states.back()) {
      states.pop_back();
    } else {
      bool ok = false;

      for (std::vector<ExecutionState*>::iterator it = states.begin(),
             ie = states.end(); it != ie; ++it) {
        if (es==*it) {
          states.erase(it);
          ok = true;
          break;
        }
      }

      assert(ok && "invalid state removed");
    }
  }
}
bool GuidedPathSearcher::empty() {
  return executor.states.empty(); 
}

///

BumpMergingSearcher::BumpMergingSearcher(Executor &_executor, Searcher *_baseSearcher) 
  : executor(_executor),
    baseSearcher(_baseSearcher),
    mergeFunction(executor.kmodule->kleeMergeFn) {
}

BumpMergingSearcher::~BumpMergingSearcher() {
  delete baseSearcher;
}

///

Instruction *BumpMergingSearcher::getMergePoint(ExecutionState &es) {  
  if (mergeFunction) {
    Instruction *i = es.pc->inst;

    if (i->getOpcode()==Instruction::Call) {
      CallSite cs(cast<CallInst>(i));
      if (mergeFunction==cs.getCalledFunction())
        return i;
    }
  }

  return 0;
}

ExecutionState &BumpMergingSearcher::selectState() {
entry:
  // out of base states, pick one to pop
  if (baseSearcher->empty()) {
    std::map<llvm::Instruction*, ExecutionState*>::iterator it = 
      statesAtMerge.begin();
    ExecutionState *es = it->second;
    statesAtMerge.erase(it);
    ++es->pc;

    baseSearcher->addState(es);
  }

  ExecutionState &es = baseSearcher->selectState();

  if (Instruction *mp = getMergePoint(es)) {
    std::map<llvm::Instruction*, ExecutionState*>::iterator it = 
      statesAtMerge.find(mp);

    baseSearcher->removeState(&es);

    if (it==statesAtMerge.end()) {
      statesAtMerge.insert(std::make_pair(mp, &es));
    } else {
      ExecutionState *mergeWith = it->second;
      if (mergeWith->merge(es)) {
        // hack, because we are terminating the state we need to let
        // the baseSearcher know about it again
        baseSearcher->addState(&es);
        executor.terminateState(es);
      } else {
        it->second = &es; // the bump
        ++mergeWith->pc;

        baseSearcher->addState(mergeWith);
      }
    }

    goto entry;
  } else {
    return es;
  }
}

void BumpMergingSearcher::update(ExecutionState *current,
                                 const std::set<ExecutionState*> &addedStates,
                                 const std::set<ExecutionState*> &removedStates) {
  baseSearcher->update(current, addedStates, removedStates);
}

///

MergingSearcher::MergingSearcher(Executor &_executor, Searcher *_baseSearcher) 
  : executor(_executor),
    baseSearcher(_baseSearcher),
    mergeFunction(executor.kmodule->kleeMergeFn) {
}

MergingSearcher::~MergingSearcher() {
  delete baseSearcher;
}

///

Instruction *MergingSearcher::getMergePoint(ExecutionState &es) {
  if (mergeFunction) {
    Instruction *i = es.pc->inst;

    if (i->getOpcode()==Instruction::Call) {
      CallSite cs(cast<CallInst>(i));
      if (mergeFunction==cs.getCalledFunction())
        return i;
    }
  }

  return 0;
}

ExecutionState &MergingSearcher::selectState() {
  while (!baseSearcher->empty()) {
    ExecutionState &es = baseSearcher->selectState();
    if (getMergePoint(es)) {
      baseSearcher->removeState(&es, &es);
      statesAtMerge.insert(&es);
    } else {
      return es;
    }
  }
  
  // build map of merge point -> state list
  std::map<Instruction*, std::vector<ExecutionState*> > merges;
  for (std::set<ExecutionState*>::const_iterator it = statesAtMerge.begin(),
         ie = statesAtMerge.end(); it != ie; ++it) {
    ExecutionState &state = **it;
    Instruction *mp = getMergePoint(state);
    
    merges[mp].push_back(&state);
  }
  
  if (DebugLogMerge)
    std::cerr << "-- all at merge --\n";
  for (std::map<Instruction*, std::vector<ExecutionState*> >::iterator
         it = merges.begin(), ie = merges.end(); it != ie; ++it) {
    if (DebugLogMerge) {
      std::cerr << "\tmerge: " << it->first << " [";
      for (std::vector<ExecutionState*>::iterator it2 = it->second.begin(),
             ie2 = it->second.end(); it2 != ie2; ++it2) {
        ExecutionState *state = *it2;
        std::cerr << state << ", ";
      }
      std::cerr << "]\n";
    }

    // merge states
    std::set<ExecutionState*> toMerge(it->second.begin(), it->second.end());
    while (!toMerge.empty()) {
      ExecutionState *base = *toMerge.begin();
      toMerge.erase(toMerge.begin());
      
      std::set<ExecutionState*> toErase;
      for (std::set<ExecutionState*>::iterator it = toMerge.begin(),
             ie = toMerge.end(); it != ie; ++it) {
        ExecutionState *mergeWith = *it;
        
        if (base->merge(*mergeWith)) {
          toErase.insert(mergeWith);
        }
      }
      if (DebugLogMerge && !toErase.empty()) {
        std::cerr << "\t\tmerged: " << base << " with [";
        for (std::set<ExecutionState*>::iterator it = toErase.begin(),
               ie = toErase.end(); it != ie; ++it) {
          if (it!=toErase.begin()) std::cerr << ", ";
          std::cerr << *it;
        }
        std::cerr << "]\n";
      }
      for (std::set<ExecutionState*>::iterator it = toErase.begin(),
             ie = toErase.end(); it != ie; ++it) {
        std::set<ExecutionState*>::iterator it2 = toMerge.find(*it);
        assert(it2!=toMerge.end());
        executor.terminateState(**it);
        toMerge.erase(it2);
      }

      // step past merge and toss base back in pool
      statesAtMerge.erase(statesAtMerge.find(base));
      ++base->pc;
      baseSearcher->addState(base);
    }  
  }
  
  if (DebugLogMerge)
    std::cerr << "-- merge complete, continuing --\n";
  
  return selectState();
}

void MergingSearcher::update(ExecutionState *current,
                             const std::set<ExecutionState*> &addedStates,
                             const std::set<ExecutionState*> &removedStates) {
  if (!removedStates.empty()) {
    std::set<ExecutionState *> alt = removedStates;
    for (std::set<ExecutionState*>::const_iterator it = removedStates.begin(),
           ie = removedStates.end(); it != ie; ++it) {
      ExecutionState *es = *it;
      std::set<ExecutionState*>::const_iterator it2 = statesAtMerge.find(es);
      if (it2 != statesAtMerge.end()) {
        statesAtMerge.erase(it2);
        alt.erase(alt.find(es));
      }
    }    
    baseSearcher->update(current, addedStates, alt);
  } else {
    baseSearcher->update(current, addedStates, removedStates);
  }
}

///

BatchingSearcher::BatchingSearcher(Searcher *_baseSearcher,
                                   double _timeBudget,
                                   unsigned _instructionBudget) 
  : baseSearcher(_baseSearcher),
    timeBudget(_timeBudget),
    instructionBudget(_instructionBudget),
    lastState(0) {
  
}

BatchingSearcher::~BatchingSearcher() {
  delete baseSearcher;
}

ExecutionState &BatchingSearcher::selectState() {
  if (!lastState || 
      (util::getWallTime()-lastStartTime)>timeBudget ||
      (stats::instructions-lastStartInstructions)>instructionBudget) {
    if (lastState) {
      double delta = util::getWallTime()-lastStartTime;
      if (delta>timeBudget*1.1) {
        std::cerr << "KLEE: increased time budget from " << timeBudget << " to " << delta << "\n";
        timeBudget = delta;
      }
    }
    lastState = &baseSearcher->selectState();
    lastStartTime = util::getWallTime();
    lastStartInstructions = stats::instructions;
    return *lastState;
  } else {
    return *lastState;
  }
}

void BatchingSearcher::update(ExecutionState *current,
                              const std::set<ExecutionState*> &addedStates,
                              const std::set<ExecutionState*> &removedStates) {
  if (removedStates.count(lastState))
    lastState = 0;
  baseSearcher->update(current, addedStates, removedStates);
}

/***/

IterativeDeepeningTimeSearcher::IterativeDeepeningTimeSearcher(Searcher *_baseSearcher)
  : baseSearcher(_baseSearcher),
    time(1.) {
}

IterativeDeepeningTimeSearcher::~IterativeDeepeningTimeSearcher() {
  delete baseSearcher;
}

ExecutionState &IterativeDeepeningTimeSearcher::selectState() {
  ExecutionState &res = baseSearcher->selectState();
  startTime = util::getWallTime();
  return res;
}

void IterativeDeepeningTimeSearcher::update(ExecutionState *current,
                                            const std::set<ExecutionState*> &addedStates,
                                            const std::set<ExecutionState*> &removedStates) {
  double elapsed = util::getWallTime() - startTime;

  if (!removedStates.empty()) {
    std::set<ExecutionState *> alt = removedStates;
    for (std::set<ExecutionState*>::const_iterator it = removedStates.begin(),
           ie = removedStates.end(); it != ie; ++it) {
      ExecutionState *es = *it;
      std::set<ExecutionState*>::const_iterator it2 = pausedStates.find(es);
      if (it2 != pausedStates.end()) {
        pausedStates.erase(it);
        alt.erase(alt.find(es));
      }
    }    
    baseSearcher->update(current, addedStates, alt);
  } else {
    baseSearcher->update(current, addedStates, removedStates);
  }

  if (current && !removedStates.count(current) && elapsed>time) {
    pausedStates.insert(current);
    baseSearcher->removeState(current);
  }

  if (baseSearcher->empty()) {
    time *= 2;
    std::cerr << "KLEE: increasing time budget to: " << time << "\n";
    baseSearcher->update(0, pausedStates, std::set<ExecutionState*>());
    pausedStates.clear();
  }
}

/***/

InterleavedSearcher::InterleavedSearcher(const std::vector<Searcher*> &_searchers)
  : searchers(_searchers),
    index(1) {
}

InterleavedSearcher::~InterleavedSearcher() {
  for (std::vector<Searcher*>::const_iterator it = searchers.begin(),
         ie = searchers.end(); it != ie; ++it)
    delete *it;
}

ExecutionState &InterleavedSearcher::selectState() {
  Searcher *s = searchers[--index];
  if (index==0) index = searchers.size();
  return s->selectState();
}

void InterleavedSearcher::update(ExecutionState *current,
                                 const std::set<ExecutionState*> &addedStates,
                                 const std::set<ExecutionState*> &removedStates) {
  for (std::vector<Searcher*>::const_iterator it = searchers.begin(),
         ie = searchers.end(); it != ie; ++it)
    (*it)->update(current, addedStates, removedStates);
}
