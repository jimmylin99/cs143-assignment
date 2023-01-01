/*
 *  The scanner definition for COOL.
 */

/*
 *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
 *  output, so headers and global definitions are placed here to be visible
 * to the code in the file.  Don't remove anything that was here initially
 */
%{
#include <cool-parse.h>
#include <stringtab.h>
#include <utilities.h>

/* The compiler assumes these identifiers. */
#define yylval cool_yylval
#define yylex  cool_yylex

/* Max size of string constants */
#define MAX_STR_CONST 1025
#define YY_NO_UNPUT   /* keep g++ happy */

extern FILE *fin; /* we read from this file */

/* define YY_INPUT so we read from the FILE fin:
 * This change makes it possible to use this scanner in
 * the Cool compiler.
 */
#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) \
	if ( (result = fread( (char*)buf, sizeof(char), max_size, fin)) < 0) \
		YY_FATAL_ERROR( "read() in flex scanner failed");

char string_buf[MAX_STR_CONST]; /* to assemble string constants */
char *string_buf_ptr;

extern int curr_lineno;
extern int verbose_flag;

extern YYSTYPE cool_yylval;

/*
 *  Add Your own definitions here
 */

int comment_nesting = 0;

%}

/*
 * Define names for regular expressions here.
 */

CLASS         [cC][lL][aA][sS][sS]
ELSE          [eE][lL][sS][eE]
FI            [fF][iI]
IF            [iI][fF]
IN            [iI][nN]
INHERITS      [iI][nN][hH][eE][rR][iI][tT][sS]
LET           [lL][eE][tT]
LOOP          [lL][oO][oO][pP]
POOL          [pP][oO][oO][lL]
THEN          [tT][hH][eE][nN]
WHILE         [wW][hH][iI][lL][eE]
CASE          [cC][aA][sS][eE]
ESAC          [eE][sS][aA][cC]
OF            [oO][fF]
DARROW        =>
NEW           [nN][eE][wW]
ISVOID        [iI][sS][vV][oO][iI][dD]
ASSIGN        "<-"
NOT           [nN][oO][tT]
LE            <=

TYPEID        [A-Z]+[a-zA-Z0-9_]*
OBJECTID      [a-z]+[a-zA-Z0-9_]*
DIGIT         [0-9]+
STRING        \042([^\042\\\n]|\\(.|\n))*\042
MISSINGSTR    \042([^\042\\\n]|\\(.|\n))*[\n]?
BOOL          t[rR][uU][eE]|f[aA][lL][sS][eE]
OPERATOR      [;:,.@~+*/~<=(){}]|"-"

%x COMMENT
%%

\n          { ++curr_lineno; }
[ \t\r\f\v]+  { /* ignore */ }
--.*[--]?     { /* ignore */ }

 /*
  *  Nested comments
  */


"(*"        { BEGIN(COMMENT); }
"*)"        {
  cool_yylval.error_msg = "Unmatched *)";
  return ERROR;
}
<COMMENT>{
  "(*" { ++comment_nesting; }
  "*)" { if (comment_nesting) --comment_nesting;
         else BEGIN(INITIAL); }
  \n   { ++curr_lineno; }
  .    /* ignore */
  <<EOF>> {
    cool_yylval.error_msg = "EOF in comment"; // problematic
    BEGIN(INITIAL);
    return ERROR;
  }
}

<<EOF>> {
  return 0;
}


 /*
  *  The multiple-character operators.
  */

{CLASS}     { return CLASS; }
{ELSE}      { return ELSE; }
{FI}        { return FI; }
{IF}        { return IF; }
{IN}        { return IN; }
{INHERITS}  { return INHERITS; }
{LET}       { return LET; }
{LOOP}      { return LOOP; }
{POOL}      { return POOL; }
{THEN}      { return THEN; }
{WHILE}     { return WHILE; }
{CASE}      { return CASE; }
{ESAC}      { return ESAC; }
{OF}        { return OF; }
{DARROW}		{ return DARROW; }
{NEW}       { return NEW; }
{ISVOID}    { return ISVOID; }
{ASSIGN}    { return ASSIGN; }
{NOT}       { return NOT; }
{LE}        { return LE; }
{OPERATOR}  { return yytext[0]; }

{BOOL}      { 
  cool_yylval.boolean = yytext[0]=='t'?true:false;
  return BOOL_CONST;
}

{TYPEID} {
    cool_yylval.symbol = stringtable.add_string(yytext);
    return TYPEID;
}

{OBJECTID} {
    cool_yylval.symbol = stringtable.add_string(yytext);
    return OBJECTID;
}

{DIGIT} {
    cool_yylval.symbol = inttable.add_string(yytext);
    return INT_CONST;
}

{MISSINGSTR} {
    for (int i = 0; i < yyleng; i ++) {
      if (yytext[i] == '\n')
        ++curr_lineno;
    }
    cool_yylval.error_msg = "Unterminated string constant";
    return ERROR;
}

{STRING} {
    char *s = (char *)malloc(yyleng-1);
    int k = 0;
    for (int i = 1; i <= yyleng-2; i ++) {
      if (yytext[i] == '\0') {
        cool_yylval.error_msg = "String contains escaped null character.";
        return ERROR;
      }
      if (yytext[i] == '\\') {
        if (i == yyleng-2) {
          /* should not occur, error */
          break;
        }
        switch (yytext[i+1]) {
          case 'b': s[k] = '\b'; break;
          case 't': s[k] = '\t'; break;
          case 'n': s[k] = '\n'; break;
          case 'f': s[k] = '\f'; break;
          case '\0': 
            cool_yylval.error_msg = "String contains escaped null character.";
            return ERROR;
          default:  s[k] = yytext[i+1];
            if (yytext[i+1] == '\n')
              ++curr_lineno;
        }
        i++;
      } else {
        s[k] = yytext[i];
      }
      k++;
    }
    s[++k]='\0';
    if (k - 1 > 1024) {
      cool_yylval.error_msg = "String constant too long";
      return ERROR;
    }
    cool_yylval.symbol = stringtable.add_string(s);
    return STR_CONST;
}

. {
  cool_yylval.error_msg = yytext;
  return ERROR;
}

 /*
  * Keywords are case-insensitive except for the values true and false,
  * which must begin with a lower-case letter.
  */


 /*
  *  String constants (C syntax)
  *  Escape sequence \c is accepted for all characters c. Except for 
  *  \n \t \b \f, the result is c.
  *
  */


%%
