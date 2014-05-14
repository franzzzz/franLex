#ifndef NODE_H
#define NODE_H
#include <map>
using namespace std;

class node;
typedef multimap<char,node*>::iterator mulit;
typedef multimap<char,node*> myMul;


class node
{
public:
	node();
	void Addoutstate(char ch,node* nd);
	node(int state, bool accepttag);
	bool IsAccepted();
	void SetAccept(bool tag);
	mulit GetNextStates(char ch);
	int GetState();
	multimap<char,node*> getMultimap();
	void setNextState(myMul next);
	void Setstate(int state);

	int label;
	bool accepted;
	multimap<char,node*> outstate;

};
#endif