#ifndef DFA_H
#define DFA_H
#include "node.h"
#include <vector>
#include <set>
using namespace std;

class dfa
{
public:
	dfa(node* st);
	void Eclosure(set<node*>& x);
	void printDFA();
	vector<node> getNodeVector();
	node * start;
	vector<node> nodeVec;//存放DFA的容器
	vector<node> endNode;
};
#endif