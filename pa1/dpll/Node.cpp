//
// Created by zengz17 on 2020/3/11.
//

#include "Node.h"

Node :: Node() {}

Node :: Node(bool assignedValue,int depth) {
    value = assignedValue;
    d = depth;
}