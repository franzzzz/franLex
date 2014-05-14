#pragma warning(disable:4786)
#include <vector>
#include <set>
#include <iostream>
#include <queue>
#include "dfa.h"

using namespace std;
extern map<int,string> nfaterstatetoaction;//NFA终态到ACTION的对应关系表
extern map<int ,string>TerStateActionTable;    //dfa终态到action的对应关系表

dfa::dfa(node* st)
{
	set<node*> i0;
	queue< set<node*> > nodeQueue;//存放原来NFA的节点集合集
	
	i0.insert(st);
    Eclosure(i0);//找到最初NFA节点的e-closure闭包
	nodeQueue.push(i0);//将经过e-closure闭包之后的集合集i0放入队列中
	
	start = new node(0,st->accepted);

	node* currentNode = start;

	set<node*>  subset;
	int xuhao=1;//序号
	set<node*> temp;
	multimap<char,node*>  row;
	set<char> zifuji;//字符集
	multimap<set<node*> , node*> suoyin;/////{q0}->I0,索引
	

	//利用容器suoyin存放进行合并e-closure闭包之后的新的DFA节点
	//suoyin里的数据类型是pair<set<node*>,node*>类型
	//set<node*>参数传入合并e-closure后，原来节点q0通过e-closure后达到的节点集合
	//node*存放新的节点指针
	//例如：
	//suoyin---set<node*>------node*
	//	   1   {q0,q1,q3,q4}    I0
    suoyin.insert(pair<set<node*> , node*>(i0,start));

    nodeVec.push_back(*start);//存放DFA节点

	//////////利用表格确定化过程/////////////////////////

	
	do{
			row.clear();
			temp = nodeQueue.front();
            Eclosure(temp);
   			currentNode=(*(suoyin.find(temp))).second;
			zifuji.clear();
			////////////////////创建字符集，便于构造NFA-TO-DFA表格中的字符////////////////////////////
			for (set<node*>::iterator nodePointer = temp.begin();nodePointer !=temp.end();nodePointer++)
			{
            //         cout<<(*nodePointer)->label<<endl;
					for (myMul::iterator mit =  (*nodePointer)->outstate.begin();mit!=(*nodePointer)->outstate.end();mit++ )
				{
					if (((*mit).first)!=1 )  //not e-edge
					{
                      row.insert(pair<char,node*>((*mit).first,(*mit).second));///copy multimap
                      zifuji.insert((*mit).first);
					}
                     					
				}

			}

// 			cout<<"=================所有的字符集中的字符================="<<endl;
//  			for (set<char>::iterator i=zifuji.begin();i!=zifuji.end();i++)
//  			{
//  				cout<<*i<<" ";
//  			}
 		
// 			cout<<"======================================================"<<endl;
			//////////  划分子集  //////////             
			multimap<char,node*>::iterator mit3;

			myMul m1;//容器，存放构造出新的DFA边上的char型字符，以及对应的节点
			         //multi<char,node*>
			m1.clear();
			for(set<char>::iterator ziit=zifuji.begin();ziit!=zifuji.end();ziit++)
			{
				   
				   subset.clear();
                   mit3=row.find(*ziit);//在容器row中查找包含(*ziit)字符的所有节点
				for (int i=0;i<row.count(*ziit);i++)
				{
					subset.insert((*mit3).second);//在子集subset中插入包含字符(*ziit)的节点
					mit3++;
				}
				
				Eclosure(subset);//对子集subset中节点求E-closure
                if (suoyin.find(subset) == suoyin.end())//在索引中没有找到不存在此子集
                {
                     nodeQueue.push(subset);//创建新的DFA节点

					 bool isaccepted=false;//新的DFA节点的初始状态是：非终态，false
					 int nfaPoint;
                     for (set<node*>::iterator nodePointer = subset.begin();nodePointer !=subset.end();nodePointer++)
					 {
						 if ((*nodePointer)->accepted)
						 {  
							 /////////只要一个是终态，子集所确定的新节点就是终态/////
							 isaccepted=true;
                             nfaPoint = (*nodePointer)->label;
							 break;
						 }
					 }

					 node* newNode = new  node(xuhao,isaccepted);
					 if (isaccepted)//如果是终态
					 {
						 map<int,string>::iterator mit4 = nfaterstatetoaction.find(nfaPoint);//在ACTION的容器中找到对应的状态
						 if(nfaterstatetoaction.count(nfaPoint) != 0)
						 {
							  TerStateActionTable.insert(pair<int,string>(xuhao,(*mit4).second));//往容器中插入节点
							                                                                //节点包括DFA新节点的状态，即序号；以及节点

						 }
						
					 }
					 xuhao++;
					 suoyin.insert(pair<set<node*> , node*>(subset,newNode));
					 
                }
                
			
				if (subset.size()!=0)
				{	
				
				m1.insert(pair<char,node*>(*ziit,(*(suoyin.find(subset))).second));			
              
				}
			}

			currentNode->setNextState(m1);//对新节点的outstate进行赋值

			myMul::iterator mit1 = currentNode->outstate.begin();
			for (int j=0;j<currentNode->outstate.size();j++)
			{
				mit1++;//更新mit1,以便下次循环使用
			}

			nodeVec.push_back(*currentNode);
			nodeQueue.pop();
			
	}
	while(!nodeQueue.empty());
}

void dfa::Eclosure(set<node*>& x)
{
	queue<node*> findQueue;
	
	for (set<node*>::iterator nodePointer = x.begin();nodePointer !=x.end();nodePointer++)
	{
		findQueue.push(*nodePointer);	
		
	}
// 	ostream_iterator<node*> output(cout, " ");
// 	copy(x.begin(),x.end(),output);
// 	
// 	cout<<endl;
	
    node* currentNode;
	do 
	{
		currentNode = findQueue.front();
		
		myMul::iterator mit =  currentNode->outstate.find(1);
// 		cout<<"Test....."<<endl
// 			<<(*mit).first<<endl
// 			<<(*mit).second<<endl;
// 		return;
// 		cout<<"=================="<<endl
// 			<<"Test ...."<<endl;
// 		cout<<currentNode->outstate.count(1)<<endl;
// 		return;
		//对myseulex.txt中的每一个RE进行消除0x01边
// 		int count = 0;
		for (int i=0;i<currentNode->outstate.count(1);i++ )
		{
			if (x.find((*mit).second) == x.end())
			{
/*				cout<<"+++++++"<<(char)(*mit).first<<endl;*/
// 				cout<<(*mit).second.label<<endl;
// 				return;
				x.insert((*mit).second);
				findQueue.push((*mit).second);
			}
			mit++;
// 	        count++;
		}
// 		cout<<count<<endl;
		findQueue.pop();
		
	} while (!findQueue.empty());
}

void dfa::printDFA()
{
	node * currentNode =start;	
	queue<node*> printQueue;
	printQueue.push(start);
	set<node*> printed;
	
	do 
	{
		currentNode=printQueue.front();
		
		printed.insert(currentNode);
		
		myMul::iterator mit = currentNode->outstate.begin();
		for (int i=0;i<currentNode->outstate.size();i++)
		{
			if (printed.count((*mit).second) == 0)
			{
				printQueue.push((*mit).second);
			}
			mit++;
		}
		printQueue.pop();
} while (!printQueue.empty());
}

vector<node> dfa::getNodeVector()
{
	return nodeVec;
}