/*
 * PathList.cpp -- Query and output all of the paths(based on basic block) 
 *                 between start point and end point
 */

#include "Passes.h"
#include <stdio.h>
#include <iostream>

using namespace llvm;
using namespace klee;

char PathList::ID = 0;

//static RegisterPass<PathList> X("pathlist", "search and output paths between start and end");
//INITIALIZE_PASS(PathList, "pathlist",
//              "search and output paths between start and end", false, false)
/*
ModulePass *llvm::createPathListPass(std::vector<std::vector<BasicBlock*> > &_paths, std::string _filename, int _lineno)
{
	PathList *pl = new PathList();
	pl->fileName = _filename;
	pl->lineNo = _lineno;
	pl->paths_found = _paths;
	return pl;
}
*/

PathList::PathList() : ModulePass(ID) {}

PathList::PathList(std::string _filename, int _lineno,func_bbs_type *func_bbs, pathsInFuncMapType *pathsInFuncMap, std::vector< Function* > *_otherCalledFuncs, BasicBlock *&targetBbp) : ModulePass(ID) {
        this->fileName = _filename;
        this->lineNo = _lineno;
        this->filter_paths = func_bbs;
		this->BB_paths_map = pathsInFuncMap;
		this->otherCalledFuncs = _otherCalledFuncs;
		this->targetBbpp = &targetBbp;
	llvm::PassRegistry &Registry = *llvm::PassRegistry::getPassRegistry();
	llvm::initializeBasicCallGraphPass(Registry);
	llvm::initializeCallGraphAnalysisGroup(Registry);                                 
	llvm::initializeDominatorTreePass(Registry);
}

static void getPath(SmallVectorImpl<char> &Path, const MDNode *MD) {
	if(MD==NULL)
		return;
	StringRef Filename = DIScope(MD).getFilename();
	if (sys::path::is_absolute(Filename))
		Path.append(Filename.begin(), Filename.end());
	else
		sys::path::append(Path, DIScope(MD).getDirectory(), Filename);
}

// get the Instruction in c code location
// addbyxqx201401
static std::string getInstPath(Instruction *I, unsigned &LineNo, unsigned &ColNo)
{
	if (I->hasMetadata()) {
		MDNode *MD = I->getDebugLoc().getAsMDNode(I->getContext());
		if (!MD)
			return "";
		DILocation Loc(MD);
		SmallString<64> Path;
		getPath(Path, Loc.getScope());

		LineNo = Loc.getLineNumber();
		ColNo = Loc.getColumnNumber();
		std::string strPath = Path.str();
		return strPath;
	}
	return "";
}

bool PathList::findLineInBB(BasicBlock* BB, std::string srcFile, unsigned int srcLine)
{
	for (BasicBlock::iterator it = BB->begin(), ie = BB->end(); it != ie; ++it) {
		if (Instruction *I = dyn_cast<Instruction>(&*it)) {
			unsigned bbLine, bbCol;
			std::string bbFile = getInstPath(I, bbLine, bbCol);
			if ((bbFile == srcFile) && (bbLine == srcLine)) {
				bug_Inst = I;
				return true;
			}
		}
	}		
	return false;
}

BasicBlock *PathList::getBB(std::string srcFile, int srcLine)
{
	for (Module::iterator fit=module->begin(); fit != module->end(); ++fit) {
		Function *F = fit;
		for (Function::iterator bbit=F->begin(); bbit != F->end(); ++bbit) {
			BasicBlock *BB = bbit;
			if (findLineInBB(BB, srcFile, srcLine))
				return BB;
		}
	}
	return NULL;
}

static BasicBlock *findCommonDominator(BasicBlock *BB, DominatorTree *DT) {
	pred_iterator i = pred_begin(BB), e = pred_end(BB);
	BasicBlock *Dom = *i;
	for (++i; i != e; ++i)
		Dom = DT->findNearestCommonDominator(Dom, *i);
	return Dom;
}

bool PathList::isBackEdge(llvm::BasicBlock *From, llvm::BasicBlock *To) {
	return std::find(BackEdges.begin(), BackEdges.end(), Edge(From, To))
		!= BackEdges.end();
}

bool PathList::filter_uclibc()
{
	FunctionMapTy::iterator cfmi = calledFunctionMap.begin();
	for (;cfmi != calledFunctionMap.end(); cfmi++) {
		CalledFunctions::iterator cfi = cfmi->second.begin();
		for (; cfi != cfmi->second.end(); cfi++) {
			unsigned int l, c;
			if (Instruction *cf_inst = cfi->second) {
				std::string cfi_path = getInstPath(cf_inst, l, c);
				if (!cfi_path.empty() && cfi_path.find("uclibc") != std::string::npos) {
					cf_inst->dump();
					// Note: there is some bug here.
					// Once I erase cfi, the klee will occur core dump error.
					//cfi = cfmi->second.erase(cfi);
					dbgs() << cfi_path <<'\n';
					dbgs() << "[Filter Uclib]: find and remove an instruction from uclibc.\n";
				} 
			}
		}
	}
	return true;
}

bool PathList::traverse_basicblocks_of_function(BasicBlock *BB, std::vector<BasicBlock*> p, paths &bb_paths)
{
	p.insert(p.begin(), BB);
//	dbgs() << "[Traverse BasicBlock]: insert " << BB->getName() <<'\n';
	if (pred_begin(BB) == pred_end(BB)) {
//		dbgs() << "------push badk bb_paths\n";
		bb_paths.push_back(p);
		p.clear();
		return true;
	}
	for (pred_iterator i = pred_begin(BB); i != pred_end(BB); i++) {
		BasicBlock *bb = *i;
		if (!bb)
			continue;
		if(i != pred_end(BB) && isBackEdge(*i,BB)) {
			bb = findCommonDominator(BB, DT);
//			llvm::errs() << "\tbk:" << bb->getName() << "->";
//			p.insert(p.begin(), bb);
//			i = pred_begin(bb);
		}
//		dbgs() << "[Traverse BasicBlock]: traverse " << bb->getName() <<'\n';
		if (traverse_basicblocks_of_function(bb, p, bb_paths)) {
			continue;
		}
	}
	p.clear();
}

void PathList::printCalledFuncAndCFGPath(Function *srcFunc, Function *dstFunc, BasicBlock *BB, std::vector<BasicBlock*> argp){
	// limit the number of paths found
	if (paths_found->size() >= 10)
		return;
	
	std::vector<BasicBlock*> p = argp;
	
	// check if the current function is existed in the current path.
	// Note: this is for avoiding funciton loop in path
	// if the current funciton FTmp is already existed in p,
	// then jump out of the current loop and go to the next
	// loop
	std::vector<BasicBlock*>::iterator bbit = p.begin();
	for (; bbit != p.end(); bbit++) {
		BasicBlock *ckbb = *bbit;
		if (ckbb->getParent() == srcFunc) {
			errs() << "*****funciton loop found*****\n";
			return;
		}
	}
	
	// analyze the backedges
	DT = &getAnalysis<DominatorTree>(*srcFunc);
	BackEdges.clear();
	if( srcFunc ){
		FindFunctionBackedges(*srcFunc, BackEdges);
	}
	
	llvm::errs() << "\t\tCFG in :" << srcFunc->getName() << "\n\t\t" << BB->getName() << "->";
			
	paths bb_paths;
	traverse_basicblocks_of_function(BB, p, bb_paths);
	dbgs() << "\n[BasicBlock Paths]: found " << bb_paths.size()<<" in all.\n";
	
/*	// firstly insert the current basicblock to the path
	p.insert(p.begin(), BB);
	//p.push_back(curBB);
	//push_num++;
	// traverse all basicblocks before BB, and insert them to path
	for (pred_iterator i = pred_begin(BB); i != pred_end(BB); ) {
		BasicBlock *bb = *i;
		if (!bb)
			continue;
		llvm::errs() << "\t" << bb->getName() << "->";
		p.insert(p.begin(), bb);
		i = pred_begin(bb);
		// check if there is backedge between bb and i
		if(i != pred_end(bb) && isBackEdge(*i,bb)) {
			bb = findCommonDominator(bb, DT);
			llvm::errs() << "\tbk:" << bb->getName() << "->";
			p.insert(p.begin(), bb);
			i = pred_begin(bb);
		}
	}
*/
//	llvm::errs() << "\n\t\tCFG end\n" ;
	// find a path from srcFunc to dstFunc
	for (paths::iterator paths_i = bb_paths.begin(); paths_i != bb_paths.end(); paths_i++) {
		std::vector<BasicBlock*> pp = *paths_i;
		
		if( srcFunc == dstFunc ) {
			llvm::errs() << "end. \na path found\n\n";
			paths_found->push_back(pp);				
			continue;
		}
		else {
			// iteratively call printCalledFuncAndCFGPath for every functions which calls srcFunc
			for (CalledFunctions::iterator ii = calledFunctionMap[srcFunc].begin(); ii != calledFunctionMap[srcFunc].end(); ii++) {
				Function *FTmp = ii->first;
				Instruction *ITmp = ii->second;
				
				// ignore function output_multitable_row, because the structure of it is too 
				// complex, the path of the funciton is infinite, so we ignore it now
				if (FTmp->getName().find("output_multitable_row") != StringRef::npos) {
					continue;
				}
				
				if (!FTmp || !ITmp || !ITmp->getParent())
					continue;
				
				printCalledFuncAndCFGPath(FTmp, dstFunc, ITmp->getParent(), pp);
				pp.clear();
			}
		}
	}
}

// add to analyze function pointer
bool PathList::extend_calledFunctionMap(Instruction *tmpfi, User *tmpuser, GlobalVariable *func_table, Function *ff)
{
	// the first operand of GetElementPtrInst is user of the table
	if (tmpfi->getOperand(0) == tmpuser) {
		errs()<<"=====find function which calls command_table\n";
//		coutn++;
		
		// if the index of the table is a constant int
		if (ConstantInt *cint = dyn_cast<ConstantInt>(tmpfi->getOperand(2))) {
			// todo: deal with the constantint index
			
		} else {// if the index is a variavle, then add all the funcitons of command_table into the CallGraph
			// get the initialization value of the global table
			if (Constant *C = func_table->getInitializer()) {
				llvm::ConstantArray *ca = dyn_cast<llvm::ConstantArray>(&*C);
				if (ca) {
					errs()<<"Get ConstantArray ca success.\n";
					errs()<<ca->getNumOperands()<<'\n';
					// get the element of the global table
					for (int cai = 0; cai < ca->getNumOperands(); cai++) {
						Constant *tmpca = ca->getOperand(cai);
						//tmpca->dump();
						ConstantStruct *cs = dyn_cast<ConstantStruct>(&*tmpca);
						if (cs) {
							//errs()<<"get ConstantStruct cs success.\n";
							//errs()<<cs->getNumOperands()<<'\n';
							Constant *tmpcs = cs->getOperand(1);
							//tmpcs->dump();
							//errs() << tmpcs->getNumOperands()<<'\n';
							//tmpcs->getType()->dump();
							//tmpcs->getOperand(0)->dump();
							
							// get the funciton pointer of the element
							if (Function *csfunc = dyn_cast<Function>(&*(tmpcs->getOperand(0)))) {
								//errs() << "get function tmpcs success.\n";
								// add the current funciton ff to the calledFunctionMap
								// as the funciton which calls function csfunc
								FunctionMapTy::iterator it2 = calledFunctionMap.find(csfunc);
								if(it2==calledFunctionMap.end()) //not find
								{
									calledFunctionMap[csfunc].push_back(std::make_pair(ff, tmpfi));
								}
								else {
									it2->second.push_back(std::make_pair(ff, tmpfi));
								}
							} 
						} 
					}
				} else 
					return false;
			} else {
				dbgs() << "Get the initialization value of the global table failed!\n";
				return false;
			}
		}
	} else 
		return false;
	return true;
}

bool PathList::function_pointer_analysis()
{
	// add by wh
	// for add the global function pointer table command_table
	// to the CallGraph
	
	// get the global function table
	GlobalVariable *func_table = module->getGlobalVariable("command_table");	
	if (func_table && func_table->getNumUses() > 0) {
		errs()<<"[Global]: get command_table.\n";
	}
	else {
		errs()<<"[Global]: miss command_table or command_table isn't used.\n";
		return false;
	}
	// output the use list of func_table
	for (Value::use_iterator ui = func_table->use_begin(); ui != func_table->use_end(); ui++) {
		User *tmpuser = *ui;
//		int coutn = 0;
		if (tmpuser) {
			//errs() << tmpuser->getName() << '\n';
			//tmpuser->dump();
			// find the function which calls command_table in Module module
			for (Module::iterator mit = module->begin(); mit != module->end(); mit++) {
				Function *ff = &*mit;				
				if (ff) {
					for (inst_iterator fit = inst_begin(ff); fit != inst_end(ff); fit++) {
						Instruction *tmpfi = &*fit;
						// the function pointer table must be used in GetElementPtrInst
						if (isa<GetElementPtrInst>(tmpfi)) {
							//errs() << "tmpi has " << tmpfi->getNumOperands() << "operands.\n";
							//tmpfi->dump();
							//tmpfi->getOperand(0)->dump();
							extend_calledFunctionMap(tmpfi, tmpuser, func_table, ff);
						} 
					}
				} else {
					errs() << "Error: get function of module failed.\n";
					mit->dump();
					continue;
				}
			}
		} else {
			errs() << "get user failed.\n";
			continue;
		}
//		errs() << "++++++there are " << coutn << " lines call command_table in all.\n";
	}
	return true;
//	errs()<<"[Global]: "<<func_table->getName()<<"\n";
//	errs()<<"[Global]: type ID is "<<func_table->getType()->getTypeID()<<'\n';
}

bool PathList::runOnModule(Module &M) {
	module = &M;
	
	llvm::dbgs() << "[runOnModule]: Moduel M has " << M.getFunctionList().size() << " Functions in all.\n";
	
	// for test
	Function *f1 = M.getFunction("fprintf");
	if (!f1)
		dbgs() << "[Test]: can not find function fprintf.\n";
	else
		dbgs() << "[Test]: find function fprintf.\n";
	  
	CallGraph &CG = getAnalysis<CallGraph>();
//	CG.dump();
	
	CallGraphNode *cgNode = CG.getRoot();
	cgNode->dump();
//	errs()<<node->getFunction()->getName()<<'\n';
	
	Function *startFunc;
	Function *endFunc;
	startFunc = M.getFunction("__user_main");
	
	//std::string fileName("/home/xqx/data/xqx/projects/benckmarks-klee/texinfo-4.8/build-shit/makeinfo/../../makeinfo/insertion.c");
	//int lineNo = 407;
	
	BB = getBB(fileName, lineNo);
	*targetBbpp = getBB(fileName, lineNo);
	if (BB) {
		endFunc = BB->getParent();
		if (!endFunc) {
			errs()<<"Error: get endFunc failed.\n";
			return false;
		}
		if (!startFunc) {
		  	errs()<<"Error: get startFunc failed.\n";
			return false;
		}
		errs()<<startFunc->getName()<<'\n';
	}
	else {
		errs()<<"Error: get BB failed.\n";
		return false;
	}
	
	
	
	//read start and end from xml files
//	defectList enStart, enEnd;
//	getEntryList("/tmp/entrys.xml", &enStart, "start");
//	getEntryList("/tmp/entrys.xml", &enEnd, "end");
//	getEntryList("/tmp/entrys.xml", &dl, "end");
//	dumpEntryList(&enStart);
//	dumpEntryList(&enEnd);
//	dumpEntryList(&dl);
	
	//read bug information from xml file
/*	for (defectList::iterator dit = dl.begin(); dit != dl.end(); dit++) {
		StringRef file(dit->first.c_str());
		std::vector<int> lines = dit->second;
		BasicBlock *BB = getBB(file, *(lines.begin()));
		if (BB) {
			endFunc = BB->getParent();
		}
	}
*/	
	//to store temporary path
	std::vector<BasicBlock*> p;
	// a counter
	int map_count = 0;
	
	for (Module::iterator i = M.begin(), e = M.end(); i != e; ++i) {
		Function *F = i;
		if (!F) {
			llvm::errs() << "***NULL Function***\n";
			continue;
		}
		cgNode = CG.getOrInsertFunction(F);
		F = cgNode->getFunction();
//		
		for (CallGraphNode::iterator I = cgNode->begin(), E = cgNode->end();
				I != E; ++I){
			CallGraphNode::CallRecord *cr = &*I;
//			llvm::errs() << "\tCS<" << cr->first << "> calls";
			// check if the CallInst is existed
			if(cr->first){
				Instruction *TmpIns = dyn_cast<Instruction>(cr->first);
				if(TmpIns) {
//					errs() << "\t" << *TmpIns << "\n";
					//unsigned int l, c;
					//std::string cfi_path = getInstPath(TmpIns, l, c);
					//if (!cfi_path.empty()) {
					//	if (cfi_path.find("uclibc") != std::string::npos) {
					//		dbgs() << "[Filter Uclib]: find an instruction from uclibc.\n";
					//		continue;
					//	} else if (cfi_path.find("POSIX") != std::string::npos) {
					//		dbgs() << "[Filter Uclib]: find an instruction from POSIX.\n";
					//		continue;
					//	}
					//}
				} else
					continue;
			}
			// get the funciton pointer which is called by current CallRecord cr
			Function *FI = cr->second->getFunction();
			if (!FI)
				continue;
			
			// create a new CalledFunctions element and push it into calledFunctionMap.
			calledFunctionMap[FI].push_back(std::make_pair(F, dyn_cast<Instruction>(cr->first)));
			// for debuging
			map_count++;			
		}

	}
	
	dbgs() << "[Count Number of calledFunctionMap]: "<< calledFunctionMap.size() <<'\n';
	
	// analyze the global function pointer table
	if(function_pointer_analysis()) {
		errs() << "[Analyze global function pointer table success]\n";
	} else {
		errs() << "[Analyze global function pointer table failed]\n";
	}
	
	dbgs() << "[Count Number of calledFunctionMap]: "<< calledFunctionMap.size() <<'\n';
	
	// filter the instructions from uclibc
	//filter_uclibc();

	llvm::errs() << "=================================hh\n";
	llvm::errs() << "get Function Path: " << endFunc->getName() 
		<< " to " << startFunc->getName() << " \n";
	
//	printCalledFuncAndCFGPath(endFunc, startFunc, BB, p);
		
	// modification by wh
	evo_paths = new entire_path;
	//filter_paths = new func_bbs_type;
	//BB_paths_map = new std::map<std::pair<Function*, BasicBlock*>, std::vector<BasicBlock*> >;
	std::vector<std::pair< Function*, Instruction*> > tmp_func_path;
//	std::vector<BasicBlock*> tmp_bb_path;
//	explore_function_paths(endFunc, startFunc, bug_Inst, &tmp_func_path);
	collect_funcitons(endFunc, startFunc, bug_Inst, &tmp_func_path);
//	dbgs() << "++++++Found " << evo_paths->size() << " function paths.\n";
	
//	for (entire_path::iterator ep_it = evo_paths->begin(); ep_it != evo_paths->end(); ep_it++) {
//		for (std::vector<std::pair< Function*, Instruction*> >::iterator pair_it = ep_it->begin(); pair_it != ep_it->end(); pair_it++) {
//			if (filter_paths->size() != 0) {
//				std::vector<Instruction*>::iterator inst_it = std::find((*filter_paths)[pair_it->first].begin(), (*filter_paths)[pair_it->first].end(), pair_it->second);
//				if (inst_it != (*filter_paths)[pair_it->first].end()) {
//					continue;
//				}
//			}
//			(*filter_paths)[pair_it->first].push_back(pair_it->second);
//		}
//	}
	dbgs() << "[filter_paths]: contain " << filter_paths->size() << " functions in all.\n";
	
	for (func_bbs_type::iterator fbs_it = filter_paths->begin(); fbs_it != filter_paths->end(); fbs_it++) {
		for (std::vector<Instruction*>::iterator bb_it2 = fbs_it->second.begin(); bb_it2 != fbs_it->second.end(); bb_it2++) {
			dbgs() << "^^^^^^ " << fbs_it->first->getName() << ": " << (*bb_it2)->getParent()->getName() << '\n';
			// to expand functions
			call_insts.push_back((*bb_it2));
			
			explore_basicblock_paths(fbs_it->first, (*bb_it2)->getParent(), &(*BB_paths_map)[std::make_pair(fbs_it->first, *bb_it2)]);
			dbgs() << "^^^^^^ found " << (*BB_paths_map)[std::make_pair(fbs_it->first, *bb_it2)].size() << " basicblocks.\n";
		}
	}
	
	llvm::dbgs() << "!!!!!!!! Found " << call_insts.size() << " call instructions.\n";
	llvm::dbgs() << "!!!!!!!! Found " << path_basicblocks.size() << " path basicblocks.\n";
	
	// expand functions
	for (std::vector<Instruction*>::iterator ci_it = call_insts.begin(); ci_it != call_insts.end(); ci_it++) {
		BasicBlock *call_bb = (*ci_it)->getParent();
		if (!call_bb) {
			continue;
		}
		for (BasicBlock::iterator inst = call_bb->begin(); inst != call_bb->end(); inst++) {
			if (&*inst == *ci_it) {
				break;
			}
			if (isa<CallInst>(&*inst)) {
				std::vector<Instruction*>::iterator ci = std::find(path_call_insts.begin(), path_call_insts.end(), &*inst);
				if (ci != path_call_insts.end())
					continue;
				path_call_insts.push_back(&*inst);
			}
		}
	}
	llvm::dbgs() << "@@@@@@@@ After search call_insts, found " << path_call_insts.size() << " call instructions.\n";
	for (std::vector<BasicBlock*>::iterator p_bb_it = path_basicblocks.begin(); p_bb_it != path_basicblocks.end(); p_bb_it++) {
		for (BasicBlock::iterator inst = (*p_bb_it)->begin(); inst != (*p_bb_it)->end(); inst++) {
			if (isa<CallInst>(&*inst)) {
				std::vector<Instruction*>::iterator ci = std::find(path_call_insts.begin(), path_call_insts.end(), &*inst);
				if (ci != path_call_insts.end())
					continue;
				path_call_insts.push_back(&*inst);
			}
		}
	}
	llvm::dbgs() << "@@@@@@@@ After search path_basicblocks, found " << path_call_insts.size() << " call instructions.\n";
	for (std::vector<Instruction*>::iterator iit = path_call_insts.begin(); iit != path_call_insts.end(); iit++) {
		CallInst *ci = dyn_cast<CallInst>(*iit);
		if (!ci)
			continue;
		Function *ff = ci->getCalledFunction();
		if (!ff) {
			//ci->dump();
			//dbgs() << "\t[called value] " << ci->getOperand(0)->getName() << '\n'; 
			
			continue;
		}
		std::vector<Function*>::iterator fit = std::find(otherCalledFuncs->begin(), otherCalledFuncs->end(), ff);
		if (fit == otherCalledFuncs->end())
			otherCalledFuncs->push_back(ff);
	}
	llvm::dbgs() << "((((((((( Found " << otherCalledFuncs->size() << " functions.\n";
	
	for (int index = 0; index < otherCalledFuncs->size(); index++) {
		Function *f = otherCalledFuncs->at(index);
/*		if (!f) {
			//f->dump();
			llvm::dbgs() << "?????? index = " << index << " size = " << otherCalledFuncs->size()<< '\n';
			continue;
		}
*/		for (inst_iterator f_it = inst_begin(f); f_it != inst_end(f); f_it++) {
			CallInst *ci = dyn_cast<CallInst>(&*f_it);
			if (!ci)
				continue;
			if (!ci->getCalledFunction()) {
				//ci->dump();
				continue;
			}
			std::vector<Function*>::iterator fit = std::find(otherCalledFuncs->begin(), otherCalledFuncs->end(), ci->getCalledFunction());
			if (fit == otherCalledFuncs->end())
				otherCalledFuncs->push_back(ci->getCalledFunction());
		}
	}
	llvm::dbgs() << "((((((((( Found " << otherCalledFuncs->size() << " functions.\n";
	
	//This should be just for statistic.
	int tmp_funcNum_in_filter_notIn_other = 0;
	for (func_bbs_type::iterator fbs_it = filter_paths->begin(); fbs_it != filter_paths->end(); fbs_it++) {
		if (!fbs_it->first) {
			llvm::dbgs() << "[Warning]: Found a null Function pointer in filter_paths.\n";
			continue;
		}
		std::vector<Function*>::iterator fit = std::find(otherCalledFuncs->begin(), otherCalledFuncs->end(), fbs_it->first);
		if (fit == otherCalledFuncs->end())
			//otherCalledFuncs->push_back(fbs_it->first);
			tmp_funcNum_in_filter_notIn_other ++;
	}
	llvm::dbgs() << "<><><><> After searching filter_paths, found " << otherCalledFuncs->size() + tmp_funcNum_in_filter_notIn_other << " functions.\n";
/*	for (entire_path::iterator ep_it = evo_paths->begin(); ep_it != evo_paths->end(); ep_it++) {
		dbgs() << "Path length is: " << ep_it->size() << '\n';
		for (std::vector<std::pair< Function*, BasicBlock*> >::iterator pair_it = ep_it->begin(); pair_it != ep_it->end(); pair_it++) {
			 dbgs() << "^^^^^^ " << pair_it->first->getName() << ": " << pair_it->second->getName() << '\n';
			 explore_basicblock_paths(pair_it->first, pair_it->second, &(*BB_paths_map)[*pair_it]);
			 dbgs() << "^^^^^^ found " << (*BB_paths_map)[*pair_it].size() << " basicblocks.\n";
		}
	}
*/		
	llvm::errs() << "on-end\n";
	llvm::errs() << "=================================\n";
	
	// output all of the paths
/*	errs()<<"Find "<<paths_found->size()<<" paths in all.\n";
	for(paths::iterator ips = paths_found->begin();ips != paths_found->end();ips++) {
//		std::vector<BasicBlock*> *tmpP = dyn_cast<std::vector<BasicBlock*>*>(&*ips);
		dbgs() << "=========A Path Start============\n";
		for(std::vector<BasicBlock*>::iterator ps = ips->begin(), pe = ips->end(); ps != pe; ps++) {
			BasicBlock *tmpStr = *ps;
			errs()<<"\t"<<tmpStr->getParent()->getName()<<": "<<tmpStr->getName()<<" -> \n";
		}
		errs()<<"=================================\n";
	}
*/	
	return false;
}

//////////////modification by wh
void PathList::explore_basicblock_paths(Function *F, BasicBlock *BB, std::vector<BasicBlock*> *tmp_bb_path)
{
	if (!F || !BB || !tmp_bb_path) {
//		dbgs() << "[explore_basicblock_paths]: arguments is null.\n";
		return;
	}
	std::vector<BasicBlock*>::iterator bb_it = std::find(tmp_bb_path->begin(), tmp_bb_path->end(), BB);
	if (bb_it != tmp_bb_path->end()) {
//		dbgs() << "[explore_basicblock_paths]: found a basicblock loop;\n";
		return;
	}
	// to expand functions
	if (tmp_bb_path->size() != 0) {
		std::vector<BasicBlock*>::iterator bb_it2 = std::find(path_basicblocks.begin(), path_basicblocks.end(), BB);
		if (bb_it2 == path_basicblocks.end())
			path_basicblocks.push_back(BB);
	}
	
	tmp_bb_path->push_back(BB);
	if (pred_begin(BB) == pred_end(BB)) {
		return;
	}
	else {
		for (pred_iterator pre_bb_it = pred_begin(BB); pre_bb_it != pred_end(BB); pre_bb_it++) {
			explore_basicblock_paths(F, *pre_bb_it, tmp_bb_path);
		}
	}
/*	if ((*BB_paths_map)[std::make_pair(F, BB)].size() >= 100)
		return;
	// check loop
	std::vector<BasicBlock*>::iterator bb_it = std::find(tmp_bb_path->begin(), tmp_bb_path->end(), iter_BB);
	if (bb_it != tmp_bb_path->end()) {
		dbgs() << "[explore_basicblock_paths]: found a basicblock loop;\n";
		return;
	}
	
	//insert the current BB to tmp_bb_path
	tmp_bb_path->insert(tmp_bb_path->begin(), iter_BB);
	
	// check if BB is entry
	if (pred_begin(iter_BB) == pred_end(iter_BB)) {
		(*BB_paths_map)[std::make_pair(F, BB)].push_back(*tmp_bb_path);
		dbgs() << "[explore_basicblock_paths]: ******found a basicblock path;\n";
		tmp_bb_path->erase(tmp_bb_path->begin());
		return;
	}
	else {
		for (pred_iterator pre_bb_it = pred_begin(iter_BB); pre_bb_it != pred_end(iter_BB); pre_bb_it++) {
			explore_basicblock_paths(F, BB, *pre_bb_it, tmp_bb_path);
		}
		tmp_bb_path->erase(tmp_bb_path->begin());
	}*/
}

void PathList::explore_function_paths(Function *srcFunc, Function *dstFunc, Instruction *inst, std::vector<std::pair< Function*, Instruction*> > *tmp_func_path)
{
//	if (evo_paths->size() >= 10)
//		return;
	
	// check function loop
	
	std::vector<std::pair< Function*, Instruction*> >::iterator func_it = std::find(tmp_func_path->begin(), tmp_func_path->end(), std::make_pair(srcFunc, inst));
	if (func_it != tmp_func_path->end()) {
//		dbgs() << "[explore_function_paths]: found a function loop.\n";
		return;
	}
	
	// insert the current srcFunc to the tmp_func_path
	if (srcFunc) {
		tmp_func_path->insert(tmp_func_path->begin(), std::make_pair(srcFunc, inst));
//		dbgs() << "[explore_function_paths]: inserting " << srcFunc->getName() << '\n';
	}
	else {
		dbgs() << "[explore_function_paths]: srcFunc is a null pointer!\n";
		return;
	}
	
	// check if srcFunc is equal to dstFunc
	if (srcFunc == dstFunc) {
//		dbgs() << "[explore_function_paths]: ******a path found, the length is " << tmp_func_path->size() << '\n';
//		for (std::vector<std::pair< Function*, BasicBlock*> >::iterator fip = tmp_func_path->begin(); fip != tmp_func_path->end(); fip++) {
//			dbgs() << "\t&&&&  " << fip->first->getName() << ": " << fip->second->getName() <<'\n';
//		}
//		dbgs() << "[explore_function_paths]: erasing " << tmp_func_path->begin()->first->getName() << '\n';
		// store the path to evo_paths
		evo_paths->push_back(*tmp_func_path);
		dbgs() << "[explore_function_paths]: evo_paths has " << evo_paths->size() << " paths now.\n";
		tmp_func_path->erase(tmp_func_path->begin());
		return;
	} else {
		// iteratively call printCalledFuncAndCFGPath for every functions which calls srcFunc
		for (CalledFunctions::iterator called_func_it = calledFunctionMap[srcFunc].begin(); called_func_it != calledFunctionMap[srcFunc].end(); called_func_it++) {
			Function *tmp_fp = called_func_it->first;
			Instruction *tmp_Ip = called_func_it->second;
			
			if (!tmp_fp || !tmp_Ip || !tmp_Ip->getParent())
				continue;
			
			// ignore function output_multitable_row, because the structure of it is too 
			// complex, the path of the funciton is infinite, so we ignore it now
			if (tmp_fp->getName().find("output_multitable_row") != StringRef::npos) {
				continue;
			}
			
			// start to iteratively call function explore_function_paths
			explore_function_paths(tmp_fp, dstFunc, tmp_Ip, tmp_func_path);
		}
//		dbgs() << "[explore_function_paths]: erasing " << tmp_func_path->begin()->first->getName() << '\n';
		tmp_func_path->erase(tmp_func_path->begin());
	}
}

void PathList::collect_funcitons(Function *srcFunc, Function *dstFunc, Instruction *inst, std::vector<std::pair<Function*, Instruction*> > *tmp_func_path)
{
	std::vector<std::pair< Function*, Instruction*> >::iterator func_it = std::find(tmp_func_path->begin(), tmp_func_path->end(), std::make_pair(srcFunc, inst));
	if (func_it != tmp_func_path->end()) {
//		dbgs() << "[explore_function_paths]: found a function loop.\n";
		return;
	}
	
	// insert the current srcFunc to the tmp_func_path
	if (srcFunc) {
		tmp_func_path->insert(tmp_func_path->begin(), std::make_pair(srcFunc, inst));
//		dbgs() << "[explore_function_paths]: inserting " << srcFunc->getName() << '\n';
	}
	else {
		dbgs() << "[explore_function_paths]: srcFunc is a null pointer!\n";
		return;
	}
	
	// check if srcFunc is equal to dstFunc
	if (srcFunc == dstFunc) {
//		dbgs() << "[explore_function_paths]: ******a path found, the length is " << tmp_func_path->size() << '\n';
//		for (std::vector<std::pair< Function*, BasicBlock*> >::iterator fip = tmp_func_path->begin(); fip != tmp_func_path->end(); fip++) {
//			dbgs() << "\t&&&&  " << fip->first->getName() << ": " << fip->second->getName() <<'\n';
//		}
//		dbgs() << "[explore_function_paths]: erasing " << tmp_func_path->begin()->first->getName() << '\n';
		// store the path to filter_paths
		std::vector<Instruction*>::iterator inst_it = std::find((*filter_paths)[srcFunc].begin(), (*filter_paths)[srcFunc].end(), inst);
		if (inst_it == (*filter_paths)[srcFunc].end()) {		
			(*filter_paths)[srcFunc].push_back(inst);
			tmp_func_path->erase(tmp_func_path->begin());
		}
		
		return;
	} else {
		// iteratively call printCalledFuncAndCFGPath for every functions which calls srcFunc
		for (CalledFunctions::iterator called_func_it = calledFunctionMap[srcFunc].begin(); called_func_it != calledFunctionMap[srcFunc].end(); called_func_it++) {
			Function *tmp_fp = called_func_it->first;
			Instruction *tmp_Ip = called_func_it->second;
			
			if (!tmp_fp || !tmp_Ip || !tmp_Ip->getParent())
				continue;
			
			// ignore function output_multitable_row, because the structure of it is too 
			// complex, the path of the funciton is infinite, so we ignore it now
			if (tmp_fp->getName().find("output_multitable_row") != StringRef::npos) {
				continue;
			}
			
			// start to iteratively call function explore_function_paths
			collect_funcitons(tmp_fp, dstFunc, tmp_Ip, tmp_func_path);
		}
//		dbgs() << "[explore_function_paths]: erasing " << tmp_func_path->begin()->first->getName() << '\n';
		
		std::vector<Instruction*>::iterator inst_it = std::find((*filter_paths)[srcFunc].begin(), (*filter_paths)[srcFunc].end(), inst);
		if (inst_it == (*filter_paths)[srcFunc].end()) {		
			(*filter_paths)[srcFunc].push_back(inst);
			tmp_func_path->erase(tmp_func_path->begin());
		}
		
	}
}
