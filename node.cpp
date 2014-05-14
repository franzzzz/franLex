#pragma warning(disable:4786)
#include <map>
#include "node.h"

node::node()
{
	label = 0;
	accepted = false;
}

node::node(int state, bool accepttag)
{
	label = state;
	accepted = accepttag;
}

void node::Addoutstate(char ch,node* nd)
{
	outstate.insert(make_pair(ch,nd));//不存在，添加
}

bool node::IsAccepted()
{
	return accepted;
}

void node::SetAccept(bool tag)
{
	accepted = tag;
}

mulit node::GetNextStates(char ch)
{
	int num = outstate.count(ch);
	multimap<char,node*>::iterator it;
	return it;
}

int node::GetState()
{
	return label;
}

multimap<char,node*> node::getMultimap()
{
	return outstate;
}

void node::setNextState(myMul next)
{
	outstate = next;
}

void node::Setstate(int state)
{
	label = state;
}
