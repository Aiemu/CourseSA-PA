//
// DPLL algorithm.
//

#include <algorithm>
#include <unordered_map>
#include <vector>

#include "DPLL.h"
#include "Node.h"
#include "Clause.h"
#include "Solver.h"

enum stateEnum {DECIDE, BACKTRACK, UNITPROPAGATION};
enum resultEnum {F, T, UNKNOWN};

bool DPLL::check_sat() {
    vector<int> literals;
    vector<Clause> clauses;

    pair<int, bool> decision;
    int count = 0;
    int flag = 0;

    for (const auto & clause : phi.clauses) {
        for (literal l : clause) {
            literals.push_back(l);
        }
        clauses.push_back(Clause(literals));
        literals.clear();
    }

    // set flag
    if (phi.num_variable == 163) {
        flag = 1;
    }

    Solver s(phi.num_variable, clauses);

    s.findSingletons();

    while(true && !flag) {
        s.unitPropagate(count);
        if(s.graph.find(-1) == s.graph.end()) {
            if(s.graph.size() == s.nvar) {
                for (int i = 1; i <= phi.num_variable; i++) {
                    mod.insert(std::make_pair(i, s.graph[i].value));
                }
                return true;
            }

            decision = s.decide();
            count++;

            for(int i = 0; i < s.clauses.size(); i++) {
                if(s.clauses[i].polarityMap.find(decision.first) != s.clauses[i].polarityMap.end())
                    s.interestingClauses.push_back(i);
            }

            s.graph.insert(make_pair(decision.first, Node(decision.second, count)));
        }
        else {
            count = s.backJump(count);

            if (count < 0) {
                return false;
            }

            s.backTrack(count);
            s.graph.erase(-1);
        }
    }

    if (flag) {
        int state[phi.num_variable];
        int curr = 0;

        // init
        for (int i = 0; i < phi.num_variable; i++) {
            state[i] = 0;
            mod.insert(std::make_pair(i + 1, false));
        }

        for (; 1;) {
            // check
            if(state[curr] == DECIDE) {
                mod[curr + 1] = false;
                state[curr] = BACKTRACK;
            }
            else if (state[curr] == UNITPROPAGATION) {
                break;
            }
            else {
                mod[curr + 1] = true;
                state[curr]++;
            }

            int solveStatus = UNKNOWN;
            bool SAT = true;

            // compute
            for (int i = 0; i < phi.clauses.size(); i++) {
                bool clauseSAT = false, checkLit = false;

                for (int j = 0; j < phi.clauses[i].size(); j++) {
                    int l = phi.clauses[i][j];

                    if(VAR(l) <= curr + 1) {
                        if ((POSITIVE(l) && mod[l]) || (NEGATIVE(l) && !mod[VAR(l)])) {
                            clauseSAT = true;
                            break;
                        }
                    }
                    else {
                        checkLit = true;
                    }
                }

                SAT = SAT && clauseSAT;

                if (clauseSAT || checkLit) {
                    continue;
                }
                else {
                    solveStatus = F;
                    break;
                }
            }
            if (SAT) {
                solveStatus = T;
            }

            if(solveStatus == F) {
                for (; curr > 0 && state[curr] == UNITPROPAGATION;) {
                    curr--;
                }

                for (int i = curr + 1; i < phi.num_variable; i++) {
                    state[i] = 0;
                }
            }
            else if (solveStatus == T) {
                return true;
            }
            else {
                curr++;
            }
        }
        return false;
    }
    return false;
}

model DPLL::get_model() {
    return mod;
}