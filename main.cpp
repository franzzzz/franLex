#pragma warning(disable:4786)
#include <iostream>
#include <fstream>
#include <map>
#include <string>
#include <stack>
#include <vector>
#include "node.h"
#include "dfa.h"
using namespace std;

//定义宏////
#define BEGIN	65535
#define DEF_BEGIN	65536   //to identify %{，定义部分起始符号
#define DEF_END		65537   //to identify %}，定义部分终止符号
#define SEGMENT_ID	65538	//to identify %%，规则部分标识符
#define MYERROR		65539

////定义数据结构/////
typedef struct nfa
{
	node * start;
	vector<node*> terminal;//终结点
}nfa;


////定义全局变量////
ifstream infile;
ofstream outfile;

int lineNum = 0;//输入文件myseulex.txt的行号
int stateindex = 0;//表达下一个可用的表示状态的标志
int returnstate;//表示NFA结束的状态数目

map<string,string> idreTable;//存储正规表达式的Map数组
map<int,string> nfaterstatetoaction;//NFA终态到ACTION的对应关系表
map<int ,string>TerStateActionTable;    //dfa终态到action的对应关系表
map<int,string> mindfareturn;

vector<nfa> nfaTable;         //各正规表达式对应的nfa暂存地
vector<node> lastdfa;

set<char> char_set;//DFA用到的字符集

nfa lastnfa;//代表整个合并之后的NFA


////函数主体////

//检测meseulex.txt的定义、规则等部分的标识符
int checkFlag(char ch)
{
	if(ch == '%')
	{
		char cnext = infile.get();
		switch(cnext)
		{
		case '{':
			return DEF_BEGIN;
		case '}':
			return DEF_END;
		case '%':
			return SEGMENT_ID;
		default:
			infile.seekg(-1,ios::cur);//在文件的当前位置停止
			break;
		}
	}
	return MYERROR;
}

//判断是否是合法字符
bool IsLetterNum(char ch)
{
	if ((ch<='9'&&ch>='0')||(ch<='z'&&ch>='a')||(ch<='Z'&&ch>='A'))
	{
		return true;
	}
	return false;
}


//对正规表达式进行处理使其只有|、*、(、)等特殊符号，代换{}等
bool CompleteRE(string &re)
{
	//假设[]不能嵌套
	int intcount;
	string strRes="";
	string temp;
	map<string,string>::iterator iter;
	int i=0;
	int j;
	int offset;
	char ch=re[i];
	while(ch!=' ')
	{
		switch(ch)
		{
		case '[':
			
			strRes.append(1,'(');
			ch=re[++i];
			continue;
			break;
		case ']':
			strRes.append(1,')');   
			ch=re[++i];
			break;
		case '-':
			{
				char before=re[i-1];
				char after=re[i+1];
				strRes.erase(strRes.length()-1,1);
				if (IsLetterNum(re[i-2]))
				{
					strRes.append(1,'|');
				}
				while (before<after)
				{
					strRes.append(1,before);
					strRes.append(1,'|');
					before++;
				}
				strRes.append(1,after);
				ch=re[i+2];
				i=i+2;				
				break;
			}	
		case '{':
			offset=re.find_first_of('}',i);
			for (j=i+1;j<offset;j++)
			{
				temp.append(1,re[j]);
			}
			iter=idreTable.find(temp);
			intcount=idreTable.count(temp);
			if (intcount<=0)
			{
				return false;
			}
			if (iter!=idreTable.end())
			{
				strRes.append(1,'(');
				strRes.append(iter->second);
				strRes.append(1,')');
			}
			temp="";
			i=offset;
			//跳过'}'
			ch=re[++i];//必须及时清空ch和temp变量，否则会影响下面的字符分析
			break;
		case '"':
			offset=re.find_first_of('"',i+1);
			temp=re.substr(i+1,offset-i-1);
			strRes.append(1,'(');
			strRes.append(temp);
			strRes.append(1,')');
			i=offset;
			ch=re[++i];
			break;
		case '+':
			strRes.append(1,re[i-1]);   //将a+的形式转为aa*
			strRes.append(1,'^');
			ch=re[++i];
		default:
			strRes.append(1,ch);
			ch=re[++i];
			break;
		}
	}
	re=strRes;
	return true;
}

//将如果*、)、. 、字符后面是字符或(则在此符号后加'@'  并以'#'结束 ，配合ChangeRe(string)使用
string PreConcat(string re)
{
	string strRes = " ";
	for(int i=0;i<re.length()-1;i++)
	{
		char ch=re[i];
		strRes.append(1,ch);
		if(ch!= '|' && ch != '(')
		{
			char temp = re[i+1];
			if(' ' != temp && '^' != temp && '|'!=temp && ')'!=temp)
				strRes.append(1,'@');
		}
	}
	strRes.append(1,'#');
	//strRes+=' ';
	return strRes;
}

//设置分隔符的优先级
int Precendence(char c)
{
	if ('#'==c)
	{
		return 0;
	}
	else if ('|'==c)
	{
		return 1;
	}
	else if ('.' == c)
		return 2;
	else if ('@'==c)
	{
		return 3;
	}
	else if ('^'==c)
	{
		return 4;
	}
	else{
		return 0;
	}
}

//将RE转化成后缀表达式
string ChangeRe(string re1)
{
	//对re1进行预处理，添加连接符'@'，以及以#结束 
	string re=PreConcat(re1);
	string strRes;
	int i,j;
	i=j=0;
	stack<char> tempS;
	tempS.push('#');
	char ch=re[i];
	while(ch!='#')
	{
		if (ch==' ')
			ch=re[++i];
		else if ('('==ch)
		{
			tempS.push(ch);
			ch=re[++i];
		}
		else if (')'==ch)
		{
			if (re.size()==2)
			{
				strRes.append(1,ch);
			}
			else{
				while(tempS.top()!='(')
				{
					strRes.append(1,tempS.top());
					tempS.pop();
				}
				tempS.pop();  //delete the right parenthesis
			}
			ch=re[++i];
		}
		else if ('@'==ch||'^'==ch||'|'==ch)
		{

			char w=tempS.top();
			while(Precendence(w)>=Precendence(ch))
			{
				strRes.append(1,w);
				tempS.pop();
				w=tempS.top();
			}
			tempS.push(ch);
			ch=re[++i];
		}
		else
		{
			strRes.append(1,ch);
			ch=re[++i];
		}
	}
	
	while(tempS.top()!='#')
	{
		strRes.append(1,tempS.top());
		tempS.pop();
	}
	tempS.pop();
	strRes.append(1,'\0');
	 return strRes;
}

bool notIsmetaElement(char ch)
{
	if(ch == '|' || ch == '@' || ch == '^')
		return false;
	return true;
}

//构造NFA
void CreateNFA(string re)
{
	//strsufix 为后缀表达式,有0x01表示epsilon
	string strsufix;
	strsufix=ChangeRe(re);//得到表达式的后缀形式

	strsufix+=" ";

	stack<nfa> nfalist;//构造NFA的节点列表
	nfa nfatemp;//NFA节点构造过程中的临时节点
	nfa nfatemp1;//NFA节点构造过程中临时节点，是nfatemp节点的下一个节点
	nfa resnfa;
    int i=0;
	char ch=strsufix[i];	
	while(ch!=' ')
	{
	  if (notIsmetaElement(ch))//当为字符或者'@'字符时
	  {
		  node* temp=new node(stateindex++,false);//临时节点，表示状态节点，初始为不可接受
		  node* temp1=new node(stateindex++,true);//临时节点，下一个状态节点，初始化为可接受
		  temp->Addoutstate(ch,temp1);
		  nfatemp.start=temp;
		  nfatemp.terminal.clear();
		  (nfatemp.terminal).push_back(temp1);
		  nfalist.push(nfatemp);
		  returnstate=temp1->GetState();
	  }
	  else                              
	  {
		  switch(ch)
		  {
		  case '^':
			  {
				  nfatemp=nfalist.top();
				  nfalist.pop();
				  node *temp=new node(stateindex++,false);
				  node* temp1=new node(stateindex++,true);
				  node* lastnod=nfatemp.terminal[0];
				  lastnod->SetAccept(false);
				  lastnod->Addoutstate(0x01,nfatemp.start);
				  lastnod->Addoutstate(0x01,temp1);
			
                  temp->Addoutstate(0x01,nfatemp.start);
				  temp->Addoutstate(0x01,temp1);
				  resnfa.start=temp;
                  resnfa.terminal.clear();
				  resnfa.terminal.push_back(temp1);
				  nfalist.push(resnfa);
			
				  returnstate=temp1->GetState();
				  break;
			  }
		  case '|'://或运算的NFA合并
			  {
				  nfatemp=nfalist.top();
				  nfalist.pop();
				  nfatemp1=nfalist.top();
				  nfalist.pop();
				  node *temp=new node(stateindex++,false);
				  node* temp1=new node(stateindex++,true);
		
				  temp->Addoutstate(0x01,nfatemp1.start);
				  temp->Addoutstate(0x01,nfatemp.start);
				  node* lastnode1=nfatemp.terminal[0];
				  node* lastnode2=nfatemp1.terminal[0];
                  
				  lastnode1->SetAccept(false);
				  lastnode2->SetAccept(false);
                  lastnode2->Setstate(nfatemp1.terminal[0]->GetState());
				  lastnode1->Setstate(nfatemp.terminal[0]->GetState());
				  lastnode1->Addoutstate(0x01,temp1);
				  lastnode2->Addoutstate(0x01,temp1);				  
				  resnfa.start=temp;
				  resnfa.terminal.clear();
				  resnfa.terminal.push_back(temp1);
				  nfalist.push(resnfa);
				  returnstate=temp1->GetState();
				  break;
			  }
		  case '@':
			  {
				  nfatemp=nfalist.top();
				  nfalist.pop();
				  nfatemp1=nfalist.top();
				  nfalist.pop();
				  (nfatemp1.terminal[0])->SetAccept(false);
				  node* lastnode1=nfatemp1.terminal[0];
				  node* lastnode2=nfatemp.terminal[0];
				  lastnode2->Setstate(nfatemp.terminal[0]->GetState());
				  lastnode1->Setstate(nfatemp1.terminal[0]->GetState());
				  //将第一个nfa的终点与第二个dfa的起始点合并
				  multimap<char,node*> a=nfatemp.start->getMultimap();
				  for (mulit it=a.begin();it!=a.end();it++)
				  {
					  lastnode1->Addoutstate((*it).first,(*it).second);
				  }
			
				  resnfa.start=nfatemp1.start;
				  resnfa.terminal.clear();
				  resnfa.terminal.push_back(lastnode2);
				  nfalist.push(resnfa);
			
				  returnstate=lastnode2->GetState();
				  break;
			  }
		  default:
			  {
				  cerr<<"Create NFA error for string "<<re<<" !"<<endl;
				  return;
			  }
		  }
	  }
	  ch=strsufix[++i];
	  nfatemp.start=NULL;
	  nfatemp.terminal.clear();
	  nfatemp1.start=NULL;
	  nfatemp1.terminal.clear();
	  resnfa.start=NULL;
	  resnfa.terminal.clear();
	}
	nfaTable.push_back(nfalist.top());
	nfalist.pop();

}

//讲每个正规表达式RE的NFA合并成整体的NFA
//开始的节点指向第一个表达式NFA的开始，结束是最后一个节点的终止节点
//lastnfa代表整个合并之后的NFA
void JoinNFA()
{
	node* temp=new node(stateindex++,false);
	nfa nfa1;
	nfa nfa2;
	if (nfaTable.size()==0)
	{
		cout<<"the table is null"<<endl;
		cout<<"line2"<<endl;
		return;
	}
	if (nfaTable.size()==1)
	{
		lastnfa=(nfaTable[0]);
		cout<<"line3"<<endl;
	}
	else
	{
		for (int i=0;i<nfaTable.size();i++)
		{
			nfa1=nfaTable[i];
			temp->Addoutstate(0x01,nfa1.start);
			nfa2.terminal.push_back(nfa1.terminal[0]);
		}
		nfa2.start=temp;
		lastnfa=nfa2;
	}
}


//获得DFA的字符集
void getcharset(vector<node> nodeset)
{
	node temp;
	for(int i=1;i<nodeset.size();i++)
	{
		temp = nodeset[i];
		multimap<char,node*> mulmap = temp.getMultimap();

		for(mulit map_it = mulmap.begin();map_it!=mulmap.end();map_it++)
		{
			if(map_it->first != 0x01)
				char_set.insert((map_it)->first);
		}
	}

// 	for (set<char>::iterator it=char_set.begin();it!=char_set.end();it++)
// 		cout<<*it<<" ";
// 
// 	cout<<endl;
 		
}

//得到非终态节点的集合
void GetNonTerminalset(vector<node> dfanode,deque<set<int> > &mydeque,vector<set<int> > &test)
{
	set<int> res;
	bool acceptted;
	for (int i=1;i<dfanode.size();i++)
	{
		acceptted=dfanode[i].IsAccepted();
		if (!acceptted)
		{
			res.insert(dfanode[i].GetState());
		}
	}
	mydeque.push_back(res);
	test.push_back(res);
}

void addtoset(set<int> &par1,int par2)
{
	par1.insert(par2);
}

//将terminal 按照其返回值不同进行分解成不同的集合
void partitionter(vector<node>dfanode,deque<set<int> > &myqueue,vector<set<int> > &test)
{   //对终态节点分解
	map<string,set<int> >::iterator it;
	map<string,set<int> > str_set;
	map<int,string>::iterator int_str;
	for (int i=0;i<dfanode.size();i++)
	{
		if (dfanode[i].IsAccepted())//如果dfanode[i]的状态是终态节点，则将该节点的状态数插入到新的集合中，对应于终态节点的返回动作
		{
			int_str=TerStateActionTable.find(dfanode[i].GetState());
			if (int_str!=TerStateActionTable.end())
			{
				it=str_set.find(int_str->second);
				if (it!=str_set.end())//
				{
					addtoset(it->second,dfanode[i].GetState());
				}
				else
				{
					//不在str_set中则添加新的
					set<int> temp;
					temp.insert(dfanode[i].GetState());
					str_set.insert(make_pair(int_str->second,temp));
					
				}
			}
		}
	}
	//根据返回值分解后插入到队列中
	for (it=str_set.begin();it!=str_set.end();it++)
	{
		test.push_back(it->second);
		myqueue.push_back(it->second);
	}
}

void addtoset1(map<int,set<int> > &par1,int par2,int setid)
{
	map<int,set<int> >::iterator it;
	it=par1.find(setid);
	set<int> *set_int;
	if (it!=par1.end())
	{
		set_int=&(it->second);
		set_int->insert(par2);
		
	}
	else
	{
		set<int> temp;
		temp.clear();
		temp.insert(par2);
		par1.insert(make_pair(setid,temp));
	}
}

int getSetid(int state,vector< set<int> > vecset,int n)  //从第i个元素找出state对应的id
{
	int Intres=-1;
	set<int> current;
	for (int i=n;i<vecset.size();i++)
	{
		current=vecset[i];
		set<int>::iterator it;
		it=current.find(state);
		if (it!=current.end())
		{
			return i;
		}
	}
	return Intres;  // 没有找到
}

bool equalsets(set<int>par1,set<int>par2)//判断两个集合是否相等
{
	set<set<int> > temp;
	temp.insert(par1);
	temp.insert(par2);
	if (temp.size()==2)//有两个元素说明两个集合不同
	{
		return false;
	}
	else
	{
		return true;
	}
}

void deletefromset(vector<set<int> > &testset,set<int> current)
{
	vector<set<int> >::iterator it;
	for(it=testset.begin();it!=testset.end();it++)
	{
		if (equalsets((*it),current))
		{
			testset.erase(it);
			return;
		}
	}
	
}

bool isterofmin(set<int> int_set,vector<node> dfanode,int &state)//判断子集是否是最小化的终结点,由于终态不可能与非终态在一个子集中故只需知道第一个点的情况就可
{
	//state 表示返回此集合对应dfa的终态状态值
	set<int>::iterator it=int_set.begin();
	map<int,string>::iterator mapit;
	for (set<int>::iterator myit=int_set.begin();myit!=int_set.end();myit++)
	{
		mapit=TerStateActionTable.find((*myit));
		if (mapit!=TerStateActionTable.end())
		{
			state=mapit->first;
			break;
		}
	}
	if (it!=int_set.end())
	{
		return dfanode[(*it)].IsAccepted();
	}
	else
	{
		return false;
	}
}

//根据划分的子集和dfanode 构造最小的dfa，start为dfa起始状态的子集索引号
void generateDFA(vector< set<int> >vecset,vector<node> dfanode,int start)
{
	//用vecset的下标表示mindfa的状态 
	bool acceptted;
	node* tempnode;
    //vector<node*> mymindfa;
	node my=dfanode[0];
	
	
	deque<int> states;//保存lastdfa中对应dfanode中的状态
	//先生成节点
	for (int i=0;i<vecset.size();i++)
	{
		int mystate=-100;                          
		acceptted=isterofmin(vecset[i],dfanode,mystate);
        tempnode=new node(i,acceptted);
		lastdfa.push_back(*tempnode);
		if (mystate!=-100)                //mystate 对应于TerStateActionTable中的int
		{                    
			states.push_back(mystate);
		}
		
	}
    
	
	//添加后继状态
	int nextstate;
	int setid;
    for (int k=0;k<lastdfa.size();k++)
    {
		node* temp=&(lastdfa[k]);
		//对应dfa的返回值与minidfa的返回值
		map<int,string>::iterator mapintstring;
		if (temp->IsAccepted()) //终态对应
		{
			mapintstring=TerStateActionTable.find(states.front());
			
			if (mapintstring!=TerStateActionTable.end())
			{
				mindfareturn.insert(make_pair(temp->GetState(),mapintstring->second));
			}
			else
			{
				cout<<states.front()<<endl;
				cout<<"dfa terminal error!"<<endl;
			}
			states.pop_front();
		}
		for (set<char>::iterator char_it=char_set.begin();char_it!=char_set.end();char_it++)
		{
			char ch=(*char_it);
			set<int> tempset=vecset[k];
			for (set<int>::iterator set_it=tempset.begin();set_it!=tempset.end();set_it++)
			{
				int myte=*set_it;
				node mytempnode=dfanode[(*set_it)];
				multimap<char,node*> mul=mytempnode.getMultimap();
				mulit mult_mapit=mul.find(ch);
				if (mult_mapit!=mul.end())
				{
					nextstate=(mult_mapit->second)->GetState();
                    setid=getSetid(nextstate,vecset,0);
					if (setid<0)
					{
						cout<<"the error found in k= "<<k<<endl;
						cout<<"error found in check nextid"<<endl;
						return;
					}
					temp->Addoutstate(ch,&(lastdfa[setid]));
					break;
				}
			}
		}
    }
}

//最小化DFA
void Minidfa(vector<node> dfanode)
{
	dfanode.erase(dfanode.begin());
	//结果保存，采用自顶向下的方法进行子集的划分
	vector< set<int> > lastset;
	//vector< set<int> >resdfa;
	deque< set<int> > flag;//存放非终态节点的集合
	vector< set<int> > testset;
	set<int> currentset;
	set<int>::iterator setit;
	int start=0;                     //标记起始节点所在的子集在lastset中的索引
    set<int> t;
    t.insert(start);
	lastset.push_back(t);    //the start node set
	testset.push_back(t);     //test whether which set the current node move by ch;
	GetNonTerminalset(dfanode,flag,testset);  
	//将terminal 按照其返回值不同进行分解成不同的集合
    partitionter(dfanode,flag,testset);
	int i=0;
	cout<<"circle num\tdeque size\t test set size\tfinal set size"<<endl;
	while(!flag.empty())
	{
		cout<<i++<<"\t"<<flag.size()<<"\t"<<testset.size()<<"\t"<<lastset.size()<<endl;
		currentset=flag.front();
		int cursize=currentset.size();
		flag.pop_front();
		if (currentset.size()<=1)  //只有一个状态的节点不能再进行子集的划分
		{
			lastset.push_back(currentset);
			continue;
		}
        
        bool terminal=false;//用于判断currentset是不是最终的终结状态;如果经过所有的字符后他产生的自己数为0则表示可以认为是终态

		for (set<char>::iterator charit=char_set.begin();charit!=char_set.end();charit++)
		{
			if (terminal)
			{
				break;
			}
			char ch=(*charit);
			map<int,set<int> >tempres;
			tempres.clear();
			int setid=-100;
			for (set<int>::iterator node_it=currentset.begin();node_it!=currentset.end();node_it++)
			{
				node curnode;
				curnode=dfanode[(*node_it)];
				int curstate=curnode.GetState();
				multimap<char,node*> mymulmap;
				mulit mulmapit;
				mymulmap=curnode.getMultimap();
				mulmapit=mymulmap.find(ch);
				int mycount=mymulmap.count(ch);
				if (mycount<1)     //当前节点经过ch无后继结点
				{
					setid=-1;
					addtoset1(tempres,curstate,setid);
				}
				else
				{
					node* nextnode=mulmapit->second;
					int state1=nextnode->GetState();
					setid=getSetid(state1,testset,0);
					addtoset1(tempres,curstate,setid);
					
				}
			}
			//经过一个字符后可能有新的子集产生，先与原来的比较，如果是新的则testset中
			map<int,set<int> >::iterator int_set_mapit;
			set<int> int_set;
			if (tempres.size()>1)
			{
				deletefromset(testset,currentset);
				for (int_set_mapit=tempres.begin();int_set_mapit!=tempres.end();int_set_mapit++)
				{
					int_set=int_set_mapit->second;
					int setsize=int_set.size();
					if (int_set.size()>0)
					{
						flag.push_back(int_set);
						testset.push_back(int_set);
						terminal=true;
					}
				}
			}
			
		}
		if (!terminal)
		{
			lastset.push_back(currentset);
		}
		
	}
	for (int p=0;p<lastset.size();p++)
	{
		set<int> setint=lastset[p];
		cout<<"The ";
		cout<<p;
		cout<<" subset has nodes:"<<endl;
		for (set<int>::iterator printit=setint.begin();printit!=setint.end();printit++)
		{
			cout<<(*printit)<<"\t";
		}
		cout<<endl;
	}
	//以上完成了对大的状态集合进行子集的划分，下面由这些子集构造最终dfa的节点;
	cout<<"subset partition finished....."<<endl;
	generateDFA(lastset,dfanode,start);
}

//for test print dfa state;
void printdfastate(vector<node> par)
{
	cout<<endl;
	for(int i=0;i<par.size();i++)
	{
		node temp=par[i];
		cout<<par[i].GetState()<<"\t"<<par[i].IsAccepted()<<endl;
		
	}
	cout<<endl;
}

void GenerateCode(vector<node> dfanode)//to generate code according to DFA
{
    //对语言的编写要求是个识别的表达式之间要加空白符

    outfile<<"using namespace std;"<<endl;
	outfile<<"const int START="<<dfanode[0].GetState()<<";"<<endl;      
	outfile<<"const int MYERROR=65537;"<<endl;
	outfile<<endl;
	//yytext is the string needed to be recognized,n is the total states of nfa
	outfile<<"string analysis(string yytext)\n";   
	outfile<<"{\n";///////////////////{
	outfile<<"\tint state=START;\n";
	outfile<<"\tint i=0;\n";
	outfile<<"\tchar ch=yytext[i];\n";
	//outfile<<"\tint N=n+1 //N表示串长加1，为与状态数保持一致\n";
	outfile<<"\twhile(i<=yytext.length())\n";
	outfile<<"\t{\n";//////////////////{
	outfile<<"\t\tswitch(state)\n";
	outfile<<"\t\t{\n";//////////////////{
	for (int i=0;i<dfanode.size();i++)   //对每一个dfa状态都有一个case
	{
		int flagofelseif=0;
		outfile<<"\t\tcase "<<dfanode[i].GetState()<<":\n";
	
		outfile<<"\t\t\t{\n";//////////////////////{
		if (dfanode[i].IsAccepted())
		{
			outfile<<"\t\t\t\tif(i==yytext.length())\n";//已经识别完成打印出相应得动作
			outfile<<"\t\t\t\t{\n";///////////////////{
			map<int,string>::iterator it;
			//it=TerStateActionTable.find(dfanode[i].GetState());
			it=mindfareturn.find(dfanode[i].GetState());
			//if (it!=TerStateActionTable.end())
			if (it!=mindfareturn.end())
			{
				int length=((*it).second).length();
				outfile<<"\t\t\t\t\t"<<((*it).second).substr(1,length-2)<<endl;
				outfile<<"\t\t\t\t\tbreak;\n";
			    outfile<<"\t\t\t\t}\n";///////////////////if(i==yytext.length){---}
			}
			
		}
		multimap<char,node*> mymap=dfanode[i].getMultimap();
		multimap<char,node*>::iterator tempit;

		//cout<<"hanshu  "<<mymap.size()<<endl;

		for (tempit=mymap.begin();tempit!=mymap.end();tempit++)
		{
			outfile<<"\t\t\t\t";
			if (flagofelseif==0)
			{
				outfile<<"if";
				flagofelseif++;
			}
			else
			{
				outfile<<"else if";
			}
			outfile<<"(ch=='"<<tempit->first<<"')\n";
			outfile<<"\t\t\t\t{\n";////////////if(ch='*'){
			outfile<<"\t\t\t\t\tstate="<<(tempit->second)->GetState()<<";\n";
			outfile<<"\t\t\t\t\tbreak;\n";
			outfile<<"\t\t\t\t}\n";//////if(ch='*'){----}
			
		}
		if (mymap.size()>0)
		{
			outfile<<"\t\t\t\telse\n";
			outfile<<"\t\t\t\t{\n";
			outfile<<"\t\t\t\t\treturn \"MYERROR\";\n";
			outfile<<"\t\t\t\t}\n";
		}
		outfile<<"\t\t\t\tbreak;\n";
		outfile<<"\t\t\t}\n";/////////case 1:{------}
	}
	outfile<<"\t\t\tdefault:\n";
	outfile<<"\t\t\t\treturn \"MYERROR\";\n";
	outfile<<"\t\t}\n";
	outfile<<"\t\tch=yytext[++i];  //ch is the next letter to be recongnized\n" ;
	outfile<<"\t}\n";
	outfile<<"\treturn \"MYERROR\";\n";
	outfile<<"\n}";
}

void main()
{
	string infilename;
	string outfilename;
	cout<<"Please input the lex program file name:"<<endl;
	infilename = "myseulex.txt";
	//infilename = "test.txt";
	cout<<"Please input the lex analysis file name:"<<endl;
	outfilename = "yyseulex.cpp";
	//outfilename = "yytest.cpp";
    infile.open(infilename.c_str(),ios::in);
	outfile.open(outfilename.c_str(),ios::out);

	cout<<"Analysing Beginning......"<<endl;
	if(infile.good() == false)
	{
		cout<<"Open file error!"<<endl;
		return;
	}
	
	/////////////////////定义段的分析////////////////////////
	char c = infile.get();
    int state = checkFlag(c);
	if(state != DEF_BEGIN)
	{
		cout<<"Please check the formation of the input file!"<<endl;
		return;
	}
	while (!infile.eof() && state != DEF_END)//文件未结束并且定义段没有结束
	{
		c = infile.get();
		if(c == '\t' || c == ' ')
			continue;//是空格、tab等无用字符
		if(c == '%')
		{
			state = checkFlag(c);
			continue;
		}
		if(c == '\n')
			lineNum ++;
		outfile.put(c);
	}
	cout<<"The definition segment finished!"<<endl;
	//////////////////////////////////////////////////////////////////////////////
	/////////////////////////////开始进行正规表达式RE的分析////////////////////////
	infile.get();//读入换行符
	pair<string,string> strpair;//使用pair结构组
	state = BEGIN;
	while (!infile.eof() && state != SEGMENT_ID)//在规则段和定义段之间的RE表达式
	{
		c = infile.get();
		if(c == '%')
		{
			state = checkFlag(c);
			if(state == MYERROR)
			{
				cout<<"There is an error in line "<<lineNum<<endl;
				return ;
			}
			continue;
		}
		else
			infile.seekg(-1,ios::cur);//如果不是%符号，则在原文件位置不动
		string id,re;//id是正规表达式的含义即关键字，re是正规表达式
		infile>>id>>re;
		cout<<id<<" "<<re<<endl;
		re+=" ";
		//cout<<id<<" "<<re<<endl;
		strpair.first = id;
		CompleteRE(re);//必须在此进行先一部的RE处理，否则很坑爹！！
		strpair.second = re;
		idreTable.insert(strpair);
		lineNum++;
		infile.get();//读入换行符
	}
	cout<<"The Regular Express segment finished!"<<endl;
	///////////////////////////////////////////////////////////////////////
	/////////////////////////开始分析规则段////////////////////////////////
	infile.get();
	state = BEGIN;
	while(!infile.eof() && state != SEGMENT_ID)//在规则段中查找
	{
		c = infile.get();
		if(c == '%')
		{
			state = checkFlag(c);
			if(state == MYERROR)
			{
				cout<<"There is an error in line "<<lineNum<<endl;
				return;
			}
			continue;
		}
		else
			infile.seekg(-1,ios::cur);
		string onestr;
		string re,action;//定义RE和动作
		getline(infile,onestr);//整行读取，并存在onestr中
		lineNum ++;

		//读取正规表达式RE
		string delim ="\t";
		int offset = onestr.find_first_of(delim);
		re = onestr.substr(0,offset);
		re+=" ";
		if(re == "return")
			cout<<"return!!!"<<endl;
		if(!CompleteRE(re))
		{
			cout<<"Regular Express Error!"<<endl;
			return;
		}
		while(onestr[offset] == '\t' || onestr[offset]== ' ')
			offset++;

    	action = onestr.substr(offset,onestr.size()-offset+1);
		//	cout<<offset<<"\t"<<onestr.size()-offset+1<<endl;
	    //cout<<ChangeRe(re)<<endl;//打印成为后缀字符串的正规表达式
// 		if(re == "(/=)")
// 			cout<<"haha"<<endl;
      
		CreateNFA(re);
		cout<<"The Regular express "<<endl;
		cout<<re<<endl;
		cout<<"\t refers to state label "<<returnstate<<endl;
		nfaterstatetoaction.insert(make_pair(returnstate,action));	
	}
	cout<<"The rules segment finished!"<<endl;
	cout<<endl;
	JoinNFA();//讲单个RE的NFA合并成整体NFA
	
	///////////////NFA TO DFA//////////////////
	cout<<"Create DFA......"<<endl;

	dfa myDfa(lastnfa.start);
// 	lastdfa = myDfa.getNodeVector();
// 	printdfastate(lastdfa);
    


	map<int,string>::iterator printaction;
	//////////////最小化DFA///////////////////
	cout<<"\n\nMininizing the DFA......"<<endl;
	getcharset(myDfa.nodeVec);
// 	for(int i=0;i<myDfa.nodeVec.size();i++)
// 	{
// 		cout<<myDfa.nodeVec[i].GetState()<<" "<<myDfa.nodeVec[i].IsAccepted()<<"\t";
// 		multimap<char,node*> maptemp = myDfa.nodeVec[i].getMultimap();
// 		multimap<char,node*>::iterator maptempit;
// 		for(maptempit= maptemp.begin();maptempit != maptemp.end();maptempit++)
// 		{
// 			cout<<maptempit->first<<" ";
// 		}
// 
// 
// 	
// 
// 
// 		cout<<endl;
// 	}
// 	return;
	Minidfa(myDfa.nodeVec);
   
	cout<<"Generating code......."<<endl;
	cout<<endl;
	cout<<"Please waiting............."<<endl;
	cout<<endl;

	GenerateCode(lastdfa);
	cout<<endl;

	c = infile.get();

	while(!infile.eof())
	{
		outfile.put(c);
		c = infile.get();
		
	}
	infile.close();
	outfile.close();
	cout<<"The terminal of the program....."<<endl;
	system("pause");
    	return ;
}