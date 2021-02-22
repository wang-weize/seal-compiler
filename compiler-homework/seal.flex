 /*
  *  The scanner definition for seal.
  */

 /*
  *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
  *  output, so headers and global definitions are placed here to be visible
  * to the code in the file.  Don't remove anything that was here initially
  */
%{

#include <seal-parse.h>
#include <stringtab.h>
#include <utilities.h>
#include <stdint.h>
#include <stdlib.h>
#include<stdio.h>
#include<string.h>
#include<math.h>
/* The compiler assumes these identifiers. */
#define yylval seal_yylval
#define yylex  seal_yylex

/* Max size of string constants */
#define MAX_STR_CONST 256
#define YY_NO_UNPUT   /* keep g++ happy */

extern FILE *fin; /* we read from this file */

/* define YY_INPUT so we read from the FILE fin:
 * This change makes it possible to use this scanner in
 * the seal compiler.
 */
#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) \
	if ( (result = fread( (char*)buf, sizeof(char), max_size, fin)) < 0) \
		YY_FATAL_ERROR( "read() in flex scanner failed");

char string_buf[MAX_STR_CONST]; /* to assemble string constants */
char *string_buf_ptr;
bool error_include_zero = false;
bool error_huanhang = false;
char string_const[MAX_STR_CONST];
int string_const_len;
bool str_contain_null_char;

extern int curr_lineno;
extern int verbose_flag;

extern YYSTYPE seal_yylval;

/*
 *  Add Your own definitions here
 */
char* hexTOdec(char a[]){
  int len,t,i,j,sum=0;
  static char s[MAX_STR_CONST];
  static char ssr[MAX_STR_CONST];

	len = strlen(a);
	for(i=2; i<len; i++){
			if( a[i]>='0' && a[i]<='9' )
				t = a[i] - '0';
			else if( a[i]>='a' && a[i]<='f' )
				t = a[i] - 'a' + 10; 
			else
				t = a[i] - 'A' + 10;
			sum = sum * 16 + t;
		
  }

  i = 0, j = 0;
  while ( sum > 0 ) { s[i++] = sum % 10 + '0'; sum /= 10; }
  s[i] = '\0';
  i = i - 1;
  while (i >= 0) { ssr[j++] = s[i--]; }
  ssr[j] = '\0';
  return ssr;
}


char* Str_remove(char a[])
{
  int i, len = strlen(a);

  static char b[MAX_STR_CONST];

  for( i = 0; i < len-1; i++){
    b[i] = a[i];
  }

  b[i] = '\0';
  
  return b;
}

/* 替换字符串中特征字符串为指定字符串,想错了没神魔用 */
char* ReplaceStr(char *sSrc, char *sMatchStr, char *sReplaceStr)  
{  
    int  StringLen;  
    static char caNewString[256];  
  
    char *FindPos = strstr(sSrc, sMatchStr);  
    if( (!FindPos) || (!sMatchStr) )  
        return sSrc;  
  
    while( FindPos )  
    {  
        memset(caNewString, 0, sizeof(caNewString));  
        StringLen = FindPos - sSrc;  
        strncpy(caNewString, sSrc, StringLen);  
        strcat(caNewString, sReplaceStr);  
        strcat(caNewString, FindPos + strlen(sMatchStr));  
        strcpy(sSrc, caNewString);  
  
        FindPos = strstr(sSrc, sMatchStr);  
    }  
   
   return caNewString;
} 
 /* wwww这个函数也没啥用了 */
char* antifuc_escape(char a[]){
    int i = 1;
    int j = 0;
    int len = strlen(a);

    for(i=1; i<len;i++)
    {
        if(a[i]=='\n' && a[i-1]=='\\'){
            for(j = i-1;j<len;j++)
            {
                a[j] = a[j+1];
            }
        }
        if(a[i]=='\\' && a[i-1]=='\\'){
            for(j = i-1;j<len;j++)
            {
                a[j] = a[j+1];
            }
        }
    }
    return a;
}

%}

%option noyywrap
%x COMMENT
%x STR1
%x STR2
 /*
  * Define names for regular expressions here.
  */

%%
 
 /*读注释，忽略*/
"/*"          { BEGIN COMMENT; }
<COMMENT>"\n" { curr_lineno++; }
<COMMENT>.    { }
<COMMENT>"*/" { BEGIN INITIAL; }
<COMMENT><<EOF>> {
  strcpy(seal_yylval.error_msg,"unmatched multiline annotation symbol:*/");
  BEGIN INITIAL;
  return(ERROR);
}
"//".*"\n"    { curr_lineno++; }
"*/" {
  strcpy(seal_yylval.error_msg,"unmatched multiline annotation symbol:*/");
  return(ERROR);
}
 /* character which has Value */
 "true" {
   seal_yylval.boolean = 1;
   return (CONST_BOOL);
 }
 "false" {
   seal_yylval.boolean = 0;
   return (CONST_BOOL);
 }

[0-9]+\.[0-9]+ {
  seal_yylval.symbol = floattable.add_string(yytext);
  return (CONST_FLOAT);
}

[0-9]+ {
  seal_yylval.symbol = inttable.add_string(yytext);
  return (CONST_INT);
}

0[xX][0-9a-fA-F]+ {
  yytext = hexTOdec(yytext);
  seal_yylval.symbol = inttable.add_string(yytext);
  return (CONST_INT);
}

` { BEGIN STR1; }
<STR1>[^\n\`] {
  yymore();
  if(yyleng > MAX_STR_CONST){
      strcpy(seal_yylval.error_msg,"the length of string is over MAX_STR_CONST=256");
	  BEGIN INITIAL;
	  return(ERROR);
    }

}
<STR1>\n     {curr_lineno++; yymore(); }
<STR1><<EOF>> {
    strcpy(seal_yylval.error_msg,"string not close");
    BEGIN INITIAL;
    return(ERROR);
}
<STR1>`     {
  yytext = Str_remove(yytext);
  seal_yylval.symbol = stringtable.add_string(yytext);
  BEGIN INITIAL;
  return (CONST_STRING);
}



\"	{
	memset(string_const, 0, sizeof string_const);
	string_const_len = 0;
  str_contain_null_char = false;
	BEGIN STR2;
}

<STR2><<EOF>>	{
	strcpy(seal_yylval.error_msg, "String not closed");
	BEGIN INITIAL; 
  return (ERROR);
}

<STR2>\\.		{
	if (string_const_len >= MAX_STR_CONST) {
		strcpy(seal_yylval.error_msg, "the length of string is over MAX_STR_CONST=256");
		BEGIN INITIAL; 
    return (ERROR);
	} 
	switch(yytext[1]) {
		case '\"': string_const[string_const_len++] = '\"'; break;
		case '\\': string_const[string_const_len++] = '\\'; break;
		case 'b' : string_const[string_const_len++] = '\b'; break;
		case 'f' : string_const[string_const_len++] = '\f'; break;
		case 'n' : string_const[string_const_len++] = '\n'; break;
		case 't' : string_const[string_const_len++] = '\t'; break;
		case '0' : string_const[string_const_len++] = 0; 
			   str_contain_null_char = true;
         break;
		default  : string_const[string_const_len++] = yytext[1];
	} 
}
 
<STR2>\\\n	{ 
  curr_lineno++; 
  string_const[string_const_len++] = yytext[1];
}

<STR2>\n {
  strcpy(seal_yylval.error_msg,
    "String with double quotation cannot start a new line directly");
  BEGIN INITIAL; 
  return (ERROR);
}

<STR2>\"	{ 
  if (string_const_len > 1 && str_contain_null_char) {
		strcpy(seal_yylval.error_msg, "String contains null character '\\0'");
		BEGIN INITIAL; 
    return (ERROR);
	}
	seal_yylval.symbol = stringtable.add_string(string_const);
	BEGIN INITIAL; 
  return (CONST_STRING);
}

<STR2>.	{
  if (string_const_len >= MAX_STR_CONST) {
		strcpy(seal_yylval.error_msg, "the length of string is over MAX_STR_CONST=256");
		BEGIN INITIAL; 
    return (ERROR);
	} 
  string_const[string_const_len++] = yytext[0]; 
}



 /* letter */
"\n" { curr_lineno++; }
"if"        {return (IF);}
"else"      {return (ELSE);}
"while"     {return (WHILE);}
"for"       {return (FOR);}
"break"     {return (BREAK);}
"continue"  {return (CONTINUE);}
"func"      {return (FUNC);}
"return"    {return (RETURN);}
"var"       {return (VAR);}
"struct"    {return (STRUCT);}
"=="        {return (EQUAL);}
"!="        {return (NE);}
"<="        {return (LE);}
">="        {return (GE);}
"&&"        {return (AND);}
"||"        {return (OR);}
"+"         {return ('+');}
"/"         {return ('/');}
"-"         {return ('-');}
"*"         {return ('*');}
"="         {return ('=');}
"<"         {return ('<');}
"~"         {return ('~');}
","         {return (',');}
";"         {return (';');}
":"         {return (':');}
"("         {return ('(');}
")"         {return (')');}
"{"         {return ('{');}
"}"         {return ('}');}
"%"         {return ('%');}
">"         {return ('>');}
"&"         {return ('&');}
"!"         {return ('!');}
"^"         {return ('^');}
"|"         {return ('|');}


 /* TYPE */
 Int|Float|String|Bool|Void {
   seal_yylval.symbol = idtable.add_string(yytext);
   return (TYPEID);
 }

 [a-z][_0-9a-zA-Z]* {
   seal_yylval.symbol = idtable.add_string(yytext);
   return(OBJECTID);
 }
 /*	
 *	Add Rules here. Error function has been given.
 */
[ ]+|\t+ {}
.	{
	strcpy(seal_yylval.error_msg, yytext); 
	return (ERROR); 
}

%%
