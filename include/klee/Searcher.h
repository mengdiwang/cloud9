//===-- Searcher.h ----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SEARCHER_H
#define KLEE_SEARCHER_H

#include <vector>
#include <set>
#include <map>
#include <queue>

#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "Executor.h"

//#include "llvm/Analysis/CEPass.h"

#include <boost/config.hpp>
#include <boost/utility.hpp>
#include <boost/graph/adjacency_list.hpp>
//#include <boost/graph/graphviz.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/depth_first_search.hpp>

// FIXME: Move out of header, use llvm streams.
#include <ostream>

using namespace boost;

namespace llvm {
  class BasicBlock;
  class Function;
  class Instruction;
}

namespace klee {
  template<class T> class DiscretePDF;
  class ExecutionState;
  class Executor;

  class Searcher {
  public:
    virtual ~Searcher();

    virtual ExecutionState &selectState() = 0;

    virtual void update(ExecutionState *current,
                        const std::set<ExecutionState*> &addedStates,
                        const std::set<ExecutionState*> &removedStates) = 0;

    virtual bool empty() = 0;

    // prints name of searcher as a klee_message()
    // TODO: could probably make prettier or more flexible
    virtual void printName(std::ostream &os) { 
      os << "<unnamed searcher>\n";
    }

    // pgbovine - to be called when a searcher gets activated and
    // deactivated, say, by a higher-level searcher; most searchers
    // don't need this functionality, so don't have to override.
    virtual void activate() {}
    virtual void deactivate() {}

    // utility functions

    void addState(ExecutionState *es, ExecutionState *current = 0) {
      std::set<ExecutionState*> tmp;
      tmp.insert(es);
      update(current, tmp, std::set<ExecutionState*>());
    }

    void removeState(ExecutionState *es, ExecutionState *current = 0) {
      std::set<ExecutionState*> tmp;
      tmp.insert(es);
      update(current, std::set<ExecutionState*>(), tmp);
    }
  };
    
  
    //wmd
  /*
  class CESearcher : public Searcher{
  public:
//		typedef std::vector<llvm::BasicBlock*> pathType;
    typedef std::vector<llvm::TCeItem> TceList;
	private:
    std::vector<ExecutionState*> states;
    std::vector<TceList> cepaths;
    std::vector<std::map<llvm::Instruction*, bool> > instMaps;
    Executor &executor;
    int miss_ctr;
        
	//bool allDone(void);
	//bool done(int index);
	//int left(int index);
	//void KillAllStates(void);
    
  public:
    CESearcher(Executor &_executor, std::string cefile);
    ExecutionState &selectState();
    void update(ExecutionState *current,const std::set<ExecutionState*> &addedStates,
        const std::set<ExecutionState*> &removedStates);
    bool empty() {return states.empty();}
    void printName(std::ostream &os)
    {
      os << "CESearcher\n";
    }
  };
  */
	struct TChoiceItem
    {
    	TChoiceItem(llvm::Instruction *_Inst, int _brChoice, unsigned _line):Inst(_Inst),brChoice(_brChoice),line(_line)
    	{}
    	llvm::Instruction *Inst;
		int brChoice;
    	unsigned line;
    };
	
  class CEKSearcher : public Searcher{
  public:
    typedef std::vector<TChoiceItem> TCList;

  private:
    typedef std::map<std::string, std::vector<unsigned> > defectList;
    typedef boost::adjacency_list<boost::setS, boost::vecS, boost::bidirectionalS, boost::no_property,
    boost::property<boost::edge_weight_t, int> > Graph;
    typedef boost::graph_traits<Graph>::vertex_descriptor Vertex;
    typedef boost::graph_traits<Graph>::edge_descriptor Edge;
    typedef boost::color_traits<boost::default_color_type> Color;
    typedef std::vector<boost::default_color_type> ColorVec;

      
    std::vector<ExecutionState*> states;
    std::vector<TCList> cepaths;
    Executor &executor;
    int miss_ctr;
    
    std::vector<std::map<llvm::Instruction*, bool> > instMaps;
    std::map<std::pair<Function*, Function*>, std::vector<BasicBlock*> > CallBlockMap; // caller bb map<pair<caller, callee> ,BasicBlock>
    std::set<BasicBlock *> isCallsite;

    Graph bbG;
    std::map<BasicBlock*, Vertex> bbMap;
      
    BasicBlock *FindTarget(std::string file, unsigned line);
    void BuildGraph();
    void getDefectList(std::string docname, defectList *res);
    void GetBBPathList(std::vector<BasicBlock *> &blist, BasicBlock *tBB, TCList &ceList);
    void findCEofSingleBB(BasicBlock *targetB, TCList &ceList);
    
    void addBBEdges(llvm::BasicBlock *BB);
    BasicBlock *getBB(Vertex v);
    void findSinglePath(std::vector<Vertex> *path, Vertex root, Vertex target, Graph &graph);

    //bool CompareByLine(const TChoiceItem &a, const TChoiceItem &b);

    
  public:
    CEKSearcher(Executor &_executor, std::string cefile);
    ExecutionState &selectState();
    void update(ExecutionState *current,const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() {return states.empty();}
    void printName(std::ostream &os)
    {
      os << "CEKSearcher\n";
    }
  };
	//~

  class DFSSearcher : public Searcher {
    std::vector<ExecutionState*> states;

  public:
    ExecutionState &selectState();
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return states.empty(); }
    void printName(std::ostream &os) {
      os << "DFSSearcher\n";
    }
  };

  class RandomSearcher : public Searcher {
    std::vector<ExecutionState*> states;

  public:
    ExecutionState &selectState();
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return states.empty(); }
    void printName(std::ostream &os) {
      os << "RandomSearcher\n";
    }
  };

  class WeightedRandomSearcher : public Searcher {
  public:
    enum WeightType {
      Depth,
      QueryCost,
      InstCount,
      CPInstCount,
      MinDistToUncovered,
      CoveringNew
    };

  private:
    Executor &executor;
    DiscretePDF<ExecutionState*> *states;
    WeightType type;
    bool updateWeights;
    
    double getWeight(ExecutionState*);

  public:
    WeightedRandomSearcher(Executor &executor, WeightType type);
    ~WeightedRandomSearcher();

    ExecutionState &selectState();
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty();
    void printName(std::ostream &os) {
      os << "WeightedRandomSearcher::";
      switch(type) {
      case Depth              : os << "Depth\n"; return;
      case QueryCost          : os << "QueryCost\n"; return;
      case InstCount          : os << "InstCount\n"; return;
      case CPInstCount        : os << "CPInstCount\n"; return;
      case MinDistToUncovered : os << "MinDistToUncovered\n"; return;
      case CoveringNew        : os << "CoveringNew\n"; return;
      default                 : os << "<unknown type>\n"; return;
      }
    }
  };

  class RandomPathSearcher : public Searcher {
    Executor &executor;

  public:
    RandomPathSearcher(Executor &_executor);
    ~RandomPathSearcher();

    ExecutionState &selectState();
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty();
    void printName(std::ostream &os) {
      os << "RandomPathSearcher\n";
    }
  };

  class MergingSearcher : public Searcher {
    Executor &executor;
    std::set<ExecutionState*> statesAtMerge;
    Searcher *baseSearcher;
    llvm::Function *mergeFunction;

  private:
    llvm::Instruction *getMergePoint(ExecutionState &es);

  public:
    MergingSearcher(Executor &executor, Searcher *baseSearcher);
    ~MergingSearcher();

    ExecutionState &selectState();
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return baseSearcher->empty() && statesAtMerge.empty(); }
    void printName(std::ostream &os) {
      os << "MergingSearcher\n";
    }
  };

  class BumpMergingSearcher : public Searcher {
    Executor &executor;
    std::map<llvm::Instruction*, ExecutionState*> statesAtMerge;
    Searcher *baseSearcher;
    llvm::Function *mergeFunction;

  private:
    llvm::Instruction *getMergePoint(ExecutionState &es);

  public:
    BumpMergingSearcher(Executor &executor, Searcher *baseSearcher);
    ~BumpMergingSearcher();

    ExecutionState &selectState();
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return baseSearcher->empty() && statesAtMerge.empty(); }
    void printName(std::ostream &os) {
      os << "BumpMergingSearcher\n";
    }
  };

  class BatchingSearcher : public Searcher {
    Searcher *baseSearcher;
    double timeBudget;
    unsigned instructionBudget;

    ExecutionState *lastState;
    double lastStartTime;
    unsigned lastStartInstructions;

  public:
    BatchingSearcher(Searcher *baseSearcher, 
                     double _timeBudget,
                     unsigned _instructionBudget);
    ~BatchingSearcher();

    ExecutionState &selectState();
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return baseSearcher->empty(); }
    void printName(std::ostream &os) {
      os << "<BatchingSearcher> timeBudget: " << timeBudget
         << ", instructionBudget: " << instructionBudget
         << ", baseSearcher:\n";
      baseSearcher->printName(os);
      os << "</BatchingSearcher>\n";
    }
  };

  class IterativeDeepeningTimeSearcher : public Searcher {
    Searcher *baseSearcher;
    double time, startTime;
    std::set<ExecutionState*> pausedStates;

  public:
    IterativeDeepeningTimeSearcher(Searcher *baseSearcher);
    ~IterativeDeepeningTimeSearcher();

    ExecutionState &selectState();
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return baseSearcher->empty() && pausedStates.empty(); }
    void printName(std::ostream &os) {
      os << "IterativeDeepeningTimeSearcher\n";
    }
  };

  class InterleavedSearcher : public Searcher {
    typedef std::vector<Searcher*> searchers_ty;

    searchers_ty searchers;
    unsigned index;

  public:
    explicit InterleavedSearcher(const searchers_ty &_searchers);
    ~InterleavedSearcher();

    ExecutionState &selectState();
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return searchers[0]->empty(); }
    void printName(std::ostream &os) {
      os << "<InterleavedSearcher> containing "
         << searchers.size() << " searchers:\n";
      for (searchers_ty::iterator it = searchers.begin(), ie = searchers.end();
           it != ie; ++it)
        (*it)->printName(os);
      os << "</InterleavedSearcher>\n";
    }
  };

}

#endif
