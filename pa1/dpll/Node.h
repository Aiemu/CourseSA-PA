//
// Created by zengz17 on 2020/3/11.
//

#ifndef NODE_H
#define NODE_H

#include <unordered_set>

class Node {
public:
    bool value;
    int d;

    std::unordered_set<int> children;
    std::unordered_set<int> parents;

    Node();
    Node(bool, int);
};

#endif

