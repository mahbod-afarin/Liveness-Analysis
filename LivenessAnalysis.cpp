#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/Pass.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringRef.h"

#include <algorithm>
#include <iterator>
#include <utility>
#include <list>
#include <map>
#include <set>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "LivenessAnalysis"

namespace
{
  struct LivenessAnalysis : public FunctionPass
  {
    static char ID;
    LivenessAnalysis() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override
    {
      errs() << "LivenessAnalysis: ";
      errs() << F.getName() << "\n";
      // build a map for Variable Use and Variable Kill
      map<BasicBlock *, set<llvm::StringRef>> variable_use;
      map<BasicBlock *, set<llvm::StringRef>> variable_kill;
      map<BasicBlock *, set<llvm::StringRef>>::iterator is_killed_iterator;
      for (BasicBlock &basic_block : F)
      {
        set<StringRef> temp_variable_use;
        set<StringRef> temp_variable_kill;
        variable_use.insert(std::pair<BasicBlock *, std::set<llvm::StringRef>>(&basic_block, temp_variable_use));
        variable_kill.insert(std::pair<BasicBlock *, std::set<llvm::StringRef>>(&basic_block, temp_variable_kill));

        // going trough the instructions of basic blocks
        for (Instruction &I : basic_block)
        {
          for (int i = 0; i != I.getNumOperands(); i++)
          {
            StringRef varName = I.getOperand(i)->getName();

            // check temp_variable_kill, if exists dont add to use
            is_killed_iterator = variable_kill.find(&basic_block);
            if (is_killed_iterator->second.find(varName) != is_killed_iterator->second.end())
              continue;

            // put var into temp_variable_use
            map<BasicBlock *, set<llvm::StringRef>>::iterator temp = variable_use.find(&basic_block);
            temp_variable_use = temp->second;
            variable_use.erase(temp);
              
            if (!(I.getOpcode() == Instruction::Alloca || I.getOpcode() == Instruction::Store || I.getOpcode() == Instruction::Br || I.getOpcode() == Instruction::ICmp)) // ignore inserting in variable use if command is store
              temp_variable_use.insert(varName);
            variable_use.insert(std::pair<BasicBlock *, std::set<llvm::StringRef>>(&basic_block, temp_variable_use));

            // add 2nd operand for store to kill
            if (I.getOpcode() == Instruction::Store)
            {
              is_killed_iterator = variable_kill.find(&basic_block);
              temp_variable_kill = is_killed_iterator->second;
              temp_variable_kill.insert(varName);
              variable_kill.erase(is_killed_iterator);
              variable_kill.insert(std::pair<BasicBlock *, std::set<llvm::StringRef>>(&basic_block, temp_variable_kill));
            }
          }

          // put var into temp_variable_kill
          is_killed_iterator = variable_kill.find(&basic_block);
          temp_variable_kill = is_killed_iterator->second;
          temp_variable_kill.insert(I.getName());
          variable_kill.erase(is_killed_iterator);
          variable_kill.insert(std::pair<BasicBlock *, std::set<llvm::StringRef>>(&basic_block, temp_variable_kill));
        }
      }

      // compute liveness
      map<BasicBlock *, set<llvm::StringRef>> live_variables;
      std::list<BasicBlock *> workList;
      for (BasicBlock &basic_block : F) //initialize the live variables
      {
        set<StringRef> live_variables_out;
        live_variables.insert(std::pair<BasicBlock *, std::set<llvm::StringRef>>(&basic_block, live_variables_out));
        workList.push_back(&basic_block);
      }
        
      //while there is something in the worklist, we pop it, update it, if changed we add all it's predecessors to worklist to update
      while (!workList.empty())
      {
        BasicBlock *tmp = workList.front(); // BB pointer
        workList.pop_front();
        map<BasicBlock *, set<llvm::StringRef>>::iterator it = live_variables.find(tmp);
        set<llvm::StringRef> originlive_variables_out = it->second; // original live_variables_out
        // compute liveness
        set<llvm::StringRef> resultSet;
        for (int i = 0, numOfSucc = tmp->getTerminator()->getNumSuccessors(); i < numOfSucc; i++)
        {
          //
          BasicBlock *succ = tmp->getTerminator()->getSuccessor(i);
          set<llvm::StringRef> live_variables_out = live_variables.find(succ)->second;
          set<llvm::StringRef> temp_variable_kill = variable_kill.find(succ)->second;
          set<llvm::StringRef> temp_variable_use = variable_use.find(succ)->second;
          set<llvm::StringRef> subtrSet(live_variables_out);
          for (set<llvm::StringRef>::iterator setIt = temp_variable_kill.begin(); setIt != temp_variable_kill.end(); setIt++)
            subtrSet.erase(*setIt);
            
          std::set_union(temp_variable_use.begin(), temp_variable_use.end(), subtrSet.begin(),
                         subtrSet.end(), std::inserter(resultSet, resultSet.begin()));
        }

        //remove old basic block and add it with it's new new live variables
        live_variables.erase(it);
        live_variables.insert(std::pair<BasicBlock *, std::set<llvm::StringRef>>(tmp, resultSet));
          
        if (resultSet != originlive_variables_out)// if changed, add all predecessor to worklist
          for (auto predIt = pred_begin(tmp), predEnd = pred_end(tmp); predIt != predEnd; predIt++)
          {
            BasicBlock *pred = *predIt;
            workList.push_back(pred);
          }
      }

      // printing live variables
      for (map<BasicBlock *, set<llvm::StringRef>>::iterator iter = live_variables.begin(); iter != live_variables.end(); iter++)
      {
        BasicBlock *tmpkey = iter->first;
        set<StringRef> live_variables_out = iter->second;
        errs() << tmpkey->getName() << ": ";
        for (set<StringRef>::iterator variable = live_variables_out.begin(); variable != live_variables_out.end(); variable++)
        {
          errs() << *variable << " ";
        }
        errs() << '\n';
      }
      return false;
    }
  }; // end of struct LivenessAnalysis
} // end of anonymous namespace

char LivenessAnalysis::ID = 0;
static RegisterPass<LivenessAnalysis> X("LivenessAnalysis", "LivenessAnalysis Pass",
                                        false /* Only looks at CFG */,
                                        false /* Analysis Pass */);
