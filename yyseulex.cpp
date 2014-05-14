
#include<iostream>
#include<string>
#include<stdio.h>
#include"yytype.h"
using namespace std;
const int START=0;
const int MYERROR=65537;

string analysis(string yytext)
{
	int state=START;
	int i=0;
	char ch=yytext[i];
	while(i<=yytext.length())
	{
		switch(state)
		{
		case 0:
			{
				if(ch==' ')
				{
					state=2;
					break;
				}
				else
				{
					return "MYERROR";
				}
				break;
			}
		case 1:
			{
				break;
			}
		case 2:
			{
				if(i==yytext.length())
				{
					return "AUTO";
					break;
				}
				break;
			}
			default:
				return "MYERROR";
		}
		ch=yytext[++i];  //ch is the next letter to be recongnized
	}
	return "MYERROR";

}
void main()
{
        string s;
        while(true){
            cin>>s;
            cout<<analysis(s)<<endl;
        }
	return ;
}