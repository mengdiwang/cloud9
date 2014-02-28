//===-- Searcher.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Searcher.h"

#include "PTree.h"
#include "StatsTracker.h"

#include "klee/CoreStats.h"
#include "klee/Executor.h"
#include "klee/ExecutionState.h"
#include "klee/Statistics.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/ADT/DiscretePDF.h"
#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/System/Time.h"

#include "llvm/Constants.h"
#include "llvm/Instructions.h"
#include "llvm/BasicBlock.h"
#include "llvm/Module.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"

#include "llvm/Support/InstIterator.h"
#include "llvm/Support/CallSite.h"
#include "llvm/PassManager.h"
//#include "llvm/Analysis/CEPass.h"

#include <cassert>
#include <fstream>
#include <climits>

#include <boost/config.hpp>
#include <boost/utility.hpp>
#include <boost/graph/adjacency_list.hpp>
//#include <boost/graph/graphviz.hpp> //graphviz not compatitable with dijkstra
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/depth_first_search.hpp>
#include <boost/graph/dijkstra_shortest_paths.hpp>

using namespace boost;

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
//----------CEKSearcher-------------//

bool CEKSearcher::CompareByLine(const TChoiceItem &a, const TChoiceItem &b)
{

    return a.line < b.line;
}

CEKSearcher::CEKSearcher(Executor &_executer, std::string defectFile):executor(_executer), miss_ctr(0)
{
    llvm::Module *M = executor.kmodule->module;
    klee::KModule *km = executor.kmodule;
    
    defectList dl;
    getDefectList(defectFile, &dl);
    if(dl.size() <= 0)
    {
        std::cerr << "No entry in defectFile.t\n";
        return;
    }
    
    TCList ceList;
    std::vector<boost::Vertex> path;
    
    BuildGraph();
    
    BasicBlock *rootBB = NULL;
    for(llvm::Module::iterator fit=M->begin(); fit!=M->end(); ++fit)
    {
    	if(fit->getNameStr()=="main")
    	{
    		if(rootBB!=NULL)
    		{
    			std::cerr <<"Multi main\n";
    		}
    		else
    		{
    			rootBB = fit->getEntryBlock();
    		}
    	}
    }

    std::vector<unsigned>lines;
    std::vector<BasicBlock *> bbpath;
    for(defectList::iterator dit=dl.begin(); dit!=dl.end(); ++dit)
    {

    	ceList.clear();
        std::string file = dit->first;
        lines = dit->second;
        BasicBlock *bb = NULL;
        for(std::vector<unsigned>::iterator lit = lines.begin(); lit!=lines.end(); ++lit)
        {
            std::cerr << "Looking for '" << file << "' (" << *lit << "')\n";
            for(llvm::Module::iterator fit = M->begin(); fit!=M->end(); ++fit)
            {
                bb = FindTarget(file, *lit);
                if(bb == NULL)
                {
                	std::cerr << "target:" << file << "' (" << *lit << "')Not find\n";
                    continue;
                }
            }
            
            if(bb == NULL || rootBB == NULL)
                continue;

            std::cerr << "inter-Blocks Dijkstra\n";
            //interprocedural
            boost::Vertex rootv = bbMap[rootBB];
            boost::Vertex targetv = bbMap[bb];
            path.clear();
            bbpath.clear();

            findSinglePath(&path, rootv, targetv, bbG);
            
            BasicBlock *tmpb = NULL;
            for(std::vector<boost::Vertex>::iterator it=path.begin(); it!=path.end(); ++it)
            {
            	tmpb = getBB(*it);
            	if(tmpb != NULL) bbpath.push_back(tmpb);
            }

            GetBBPathList(bbpath, bb, ceList);
            cepaths.push_back(ceList);
            bb = NULL;
        }
    }

    std::cerr <<"Prepare done\n";
}

ExecutionState &CEKSearcher::selectState() {
  return *states.back();
}

void CEKSearcher::update(ExecutionState *current,
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

BasicBlock *CEKSearcher::getBB(boost::Vertex v)
{
    for(std::map<BasicBlock *, boost::Vertex>::iterator it=bbMap.begin(); it!=bbMap.end(); ++it)
    {
        if(v == it->second)
            return it->first;
    }
    return NULL;
}

//find the path on the built graph
void CEKSearcher::findSinglePath(std::vector<boost::Vertex> *path, boost::Vertex root, boost::Vertex target, Graph &graph)
{
    std::vector<boost::Vertex> p(num_vertices(graph));
    std::vector<int> d(num_vertices(graph));
    property_map<Graph, vertex_index_t>::type indexmap = get(vertex_index, graph);
    property_map<Graph, edge_weight_t>::type bbWeightmap = get(edge_weight, graph);
    
    boost::dijkstra_shortest_paths(graph, root, &p[0], &d[0], bbWeightmap, indexmap,
                            std::less<int>(), closed_plus<int>(),
                            (std::numeric_limits<int>::max)(), 0,
                            default_dijkstra_visitor());
    
    //  std::cout << "shortest path:" << std::endl;
    while(p[target] != target)
    {
        path->insert(path->begin(), target);
        target = p[target];
    }
    // Put the root in the list aswell since the loop above misses that one
    if(!path->empty())
        path->insert(path->begin(), root);
    
}


BasicBlock *CEKSearcher::FindTarget(std::string file, unsigned line)
{
	llvm::Module *M = executor.kmodule->module;
    klee::KModule *km = executor.kmodule;
    BasicBlock *bb = NULL;

    std::cerr << "Looking for '" << file << "' (" << line << "')\n";
    for(llvm::Module::iterator fit = M->begin(); fit!=M->end(); ++fit)
    {
        for(inst_iterator it = inst_begin(fit), ie=inst_end(fit); it!=ie; ++it)
        {
        	InstructionInfo &instif = km->infos->getInfo(&*it);
        	if(instif.line == line && instif.file == file)
        	{
        		std::cerr << "find the target\n";
        		bb = &*it->getParent();
        		return bb;
        	}
        }
    }

    return bb;
}

void CEKSearcher::addBBEdges(BasicBlock *BB)
{
    graph_traits<Graph>::edge_descriptor e;
    bool inserted;
    property_map<Graph, edge_weight_t>::type bbWeightmap = get(edge_weight, bbG);
    
    for(succ_iterator si = succ_begin(BB); si!=succ_end(BB); ++si)
    {
        boost::tie(e, inserted) = add_edge(bbMap[BB], bbMap[*si], bbG);
        if(inserted)
            addBBEdges(*si);
        bbWeightmap[e] = 1;
    }
}


void CEKSearcher::BuildGraph()
{
	llvm::Module *M = executor.kmodule->module;

    for(Module::iterator fit=M->begin(); fit!=M->end(); ++fit)
    {
        Function *F = fit;
        //funcMap[F] = add_vertex(funcG);
        for(Function::iterator bbit = F->begin(), bb_ie=F->end(); bbit != bb_ie; ++bbit)
        {
            BasicBlock *BB = bbit;
            bbMap[BB] = add_vertex(bbG);
        }
    }
    
    boost::property_map<Graph, boost::edge_weight_t>::type bbWeightmap = boost::get(boost::edge_weight, bbG);
    
    llvm::Module *M = executor.kmodule->module;
	for(Module::iterator fit=M->begin(); fit!=M->end(); ++fit)
    {
        boost::graph_traits<Graph>::edge_descriptor e;bool inserted;
        
        for(inst_iterator it = inst_begin(fit), ie = inst_end(fit); it!=ie; ++it)
        {
            llvm::Instruction *i = &*it;
            if(i->getOpcode() == Instruction::Call || i->getOpcode() == Instruction::Invoke)
            {
                BasicBlock *BB = (&*fit)->getEntryBlock();
                addBBEdges(BB);
                
                CallSite cs(i);
                Function *f = cs.getCalledFunction();
                
                if(f == NULL)
                    continue;
                if(f->empty())
                    continue;
            
                BasicBlock *callerBB = i->getParent();
                Function::iterator cBBit = f->getEntryBlock();
                BasicBlock *calleeBB = &*cBBit;
                if(calleeBB == NULL)
                    continue;
                
                boost::tie(e, inserted) = boost::add_edge(bbMap[callerBB], bbMap[calleeBB], bbG);
                bbWeightmap[e] = 1;
                
                CallBlockMap[std::make_pair(fit, f)].push_back(callerBB);
                if(!isCallsite.count(callerBB))
                    isCallsite.insert(callerBB);
                
            }
        }
    }
}

void CEKSearcher::GetBBPathList(std::vector<BasicBlock *> &blist, BasicBlock *tBB, TCList &ceList)
{
	TCList list;
	std::set<Function *> fset;
	for(std::vector<BasicBlock *>::reverse_iterator vit=blist.rbegin(); vit!=blist.rend(); ++vit)
	{
		BasicBlock *frontB = *vit;
		if(*vit == tBB || isCallsite.count(frontB) > 0)
		{
			list.clear();
			if(!fset.count(frontB->getParent()))
			{
				findCEofSingleBB(frontB, list);
				ceList.insert(ceList.begin(), list.begin(), list.end());

				fset.insert(frontB->getParent());
			}
		}
	}
}

void CEKSearcher::findCEofSingleBB(BasicBlock *targetB, TCList &ceList)
{
	if(targetB == NULL)
		return;

	Function *F = targetB->getParent();

	std::queue<BasicBlock *> bbque;
	std::set<BasicBlock *>bbset;
	bbset.insert(targetB);
	bbque.push(targetB);
	BasicBlock *frontB = NULL;
	int count = 0;

	while(!bbque.empty())
	{
		frontB = bbque.front();
		bbque.pop();

		for(pred_iterator pi = pred_begin(frontB); pi != pred_end(frontB); ++pi)
		{
			BasicBlock *predB = *pi;
			if(!bbset.count(predB))
			{
				bbset.insert(predB);
				bbque.push(predB);
				count ++;
			}
		}
	}

	if(frontB == NULL)
		return;

	std::set<BasicBlock *> seqset;

	bbque.push(frontB);
	seqset.insert(frontB);
	while(!bbque.empty())
	{
		frontB = bbque.front();
		bbque.pop();
		if(frontB == targetB)
			continue;
		BranchInst *brInst = dyn_cast<BranchInst>(frontB->getTerminator());
		if(brInst == NULL)
			continue;

		if(brInst->isConditional())
		{
			Instruction *inst = dyn_cast<Instruction>(brInst);
			InstructionInfo &instinfo = executor.kmodule->infos->getInfo(inst);
			BasicBlock *trueBB = brInst->getSuccessor(0);
			BasicBlock *falseBB = brInst->getSuccessor(1);

			unsigned lineno = instinfo.line;

			if(bbset.count(trueBB) && !bbset.count(falseBB))
			{
				TChoiceItem cItem = TChoiceItem(inst, 0, lineno);
				ceList.push_back(cItem);

				if(!seqset.count(trueBB))
				{
					bbque.push(trueBB);
					seqset.insert(trueBB);
				}
			}
			else if(!bbset.count(trueBB) &&bbset.count(falseBB))
			{
				TChoiceItem cItem = TChoiceItem(inst, 1, lineno);
				ceList.push_back(cItem);

				if(!seqset.count(falseBB))
				{
					bbque.push(falseBB);
					seqset.insert(falseBB);
				}
			}
			else if(bbset.count(trueBB) && bbset.count(falseBB))
			{
				if(!seqset.count(trueBB))
				{
					bbque.push(trueBB);
					seqset.insert(trueBB);
				}

				if(!seqset.count(falseBB))
				{
					bbque.push(falseBB);
					seqset.insert(falseBB);
				}
			}
		}
	}
	std::sort(ceList.begin(), ceList.end(), CompareByLine);
}

void CEKSearcher::getDefectList(std::string docname, defectList *res)
{
    std::cerr << "Open defect file " << docname << "\n";
    std::ifstream fin(docname.c_str());
    std::string fname="";
    std::vector<unsigned> lineList;
    while(!fin.eof())
    {
        std::string filename="";
        unsigned lineno;
        
        fin >> filename >> lineno;
        if(filename.length() < 1)
            break;
        std::cerr << "readin:" << filename << "\n";
        if(fname == "")
        {
            fname = filename;
        }
        
        if(fname != filename)
        {
            res->insert(std::make_pair(filename, lineList));
            lineList.clear();
            fname = filename;
        }
        
        lineList.push_back(lineno);
    }
    //tail add
    if(lineList.size()>0 && fname != "")
    {
        res->insert(std::make_pair(fname, lineList));
        lineList.clear();
    }
    
    fin.close();
}



/*
//----------CESearcher--------------//
CESearcher::CESearcher(Executor &_executer, std::string defectFile):executor(_executer), miss_ctr(0)
{
    //build the path list

	int count;
	std::vector<TceList> &cepaths = executor.kmodule->cepaths;
    std::cerr << "CESearcher:: critical path are follow:\n";
    
    if(cepaths.size() == 0)
		std::cerr << "CESearcher:: Warning cepaths has no element\n";

    for(std::vector<TceList>::iterator pit=cepaths.begin(); pit!=cepaths.end(); ++pit)
    {
		std::cerr << count << "\n";
		count ++;
        TceList path = *pit;
        if(path.empty())
            continue;
        
        for(TceList::iterator it=path.begin(); it!=path.end(); ++it)
        {
            llvm::TCeItem ce = *it;
            BasicBlock *bb = ce.criStmtStr->getParent();

            //std::cerr << "["  << " {" << bb->getParent() << "} [" << bb << "] - ";

            std::cerr << "["  << " {" << bb->getParent() << "} [" << bb << "] - ";

        }
        std::cerr << "\n";
    
   
        //build instmap
        std::map<llvm::Instruction*, bool> instMap;
    
        llvm::TCeItem ceitem = path.back();
        BasicBlock *BB = ceitem.criStmtStr->getParent();
        for(BasicBlock::iterator bbit=BB->begin(); bbit!=BB->end(); ++bbit)
        {
            Instruction *I = bbit;
            if(I->getOpcode() != Instruction::Br)
                instMap[I] = false;
        }
        std::cerr << instMap.size() << "instruction in leaf BB\n";
        instMaps.push_back(instMap);

    }
}

ExecutionState &CESearcher::selectState()
{
    return *states.back();
}

void CESearcher::update(ExecutionState *current,
						const std::set<ExecutionState*> &addedStates,
						const std::set<ExecutionState*> &removedStates)
{
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

//~
*/

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

WeightedRandomSearcher::WeightedRandomSearcher(Executor &_executor,
                                               WeightType _type) 
  : executor(_executor),
    states(new DiscretePDF<ExecutionState*>()),
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
                                                          es->pc()->info->id);
    double inv = 1. / std::max((uint64_t) 1, count);
    return inv * inv;
  }
  case CPInstCount: {
    StackFrame &sf = es->stack().back();
    uint64_t count = sf.callPathNode->statistics.getValue(stats::instructions);
    double inv = 1. / std::max((uint64_t) 1, count);
    return inv;
  }
  case QueryCost:
    return (es->queryCost < .1) ? 1. : 1./es->queryCost;
  case CoveringNew:
  case MinDistToUncovered: {
    uint64_t md2u = computeMinDistToUncovered(es->pc(),
                                              es->stack().back().minDistToUncoveredOnReturn);

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
    Instruction *i = es.pc()->inst;

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
    ++es->pc();

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
        executor.terminateState(es, true);
      } else {
        it->second = &es; // the bump
        ++mergeWith->pc();

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
    Instruction *i = es.pc()->inst;

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
        executor.terminateState(**it, true);
        toMerge.erase(it2);
      }

      // step past merge and toss base back in pool
      statesAtMerge.erase(statesAtMerge.find(base));
      ++base->pc();
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
