structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val pos = ref 0
fun eof () = Tokens.EOF(!pos,!pos)
fun error (e,l : int,_) = TextIO.output (TextIO.stdOut, String.concat[
	"line ", (Int.toString l), ": ", e, "\n"
      ])

%%
%header (functor PropLexFunc(structure Tokens: Prop_TOKENS));
CAP=[A-Z];
alpha_dig=[a-z0-9];
alpha_dig_sp=[a-z0-9\ ];
s=[\ ];
ws = [\ \t];
%%
\n       => (Tokens.SEMI(!pos,!pos));
"NOT"	 => (Tokens.NOT(!pos,!pos));
"AND"	 => (Tokens.AND(!pos,!pos));
"OR"	 => (Tokens.OR(!pos,!pos));
"TRUE"	 => (Tokens.TRUE(!pos,!pos));
"FALSE"	 => (Tokens.FALSE(!pos,!pos));
"IFF" => (Tokens.IFF(!pos,!pos));
"IF" => (Tokens.IF(!pos,!pos));
"THEN" => (Tokens.THEN(!pos,!pos));
"ELSE" => (Tokens.ELSE(!pos,!pos));
({alpha_dig}|{CAP})|(({alpha_dig}|{CAP})({alpha_dig_sp}*{alpha_dig})) => (Tokens.ATOMM(yytext,!pos,!pos));
"("		 => (Tokens.LPAREN(!pos,!pos));
")"		 => (Tokens.RPAREN(!pos,!pos));
{ws}+    => (lex());