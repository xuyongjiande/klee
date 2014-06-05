#### 总体流程

1. runOnModule(Module &M)

	+ CallGraph &CG = getAnalysis<CallGraph>();
	+ CallGraphNode *cgNode = CG.getRoot();
	+ Function *startFunc, *endFunc;
	+ set startFunc;
	+ get bugInst, endBB and set endFunc = endBB->getParent();

	+ 根据callgraph，填充calledFunctionMap
	+ 分析函数指针，填充calledFunctionMap

	+ 开始分析路径
	+ collect_functions(endFunc, startFunc, bug_Inst, tmp_func_path);  
		用于得到主路径上的函数和函数出口指令, 结果放在filter_paths里面。
	+ `for(){explore_basicblock_paths(func, inst->getparent(), tmpbbs);}`  
		搜集主路径上的函数"entry到callOutInst"的相关BB，柔和在一起放在call_insts和path_basicblocks里面
	+ 搜集主路径函数开始到callOutInst之间所有的call指令，放入path_call_insts里面
	+ 记录path_call_insts调用的函数（非主路径函数）, 放到otherCalledFuncs里面

2. collect_functions()
3. explorer_basicblock_paths()
