//
// Created by zengz17 on 2020/3/11.
//

#ifndef SOLVER_H
#define SOLVER_H

#include <iostream>
#include <string>
#include <vector>
#include <stack>
#include <unordered_set>
#include <deque>
#include <unordered_map>
#include "Clause.h"
#include "Node.h"
using namespace std;

class Solver {
public:
    int nvar;

    deque<int> interestingClauses;
    unordered_map<int, Node> graph;
    vector<Clause> clauses;

    pair<int, bool> decide();
    void backTrack(int);
    void unitPropagate(int);
    int backJump(int);

    void findSingletons();
    void moveWatch(int);
    pair<int, bool> unitRule(Clause);
    int pickClause(int);

    Solver(int, vector<Clause>);
    ~Solver();
};

#endif
