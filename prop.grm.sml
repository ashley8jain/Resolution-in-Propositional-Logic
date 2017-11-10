
functor PropLrValsFun (structure Token:TOKEN
            					structure Ast:AST) = 
struct
structure ParserData=
struct
structure Header = 
struct
open Ast


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\002\000\013\000\003\000\012\000\007\000\011\000\008\000\010\000\
\\010\000\009\000\014\000\008\000\000\000\
\\001\000\002\000\013\000\003\000\012\000\007\000\011\000\008\000\010\000\
\\014\000\008\000\000\000\
\\001\000\004\000\000\000\005\000\000\000\000\000\
\\001\000\006\000\015\000\011\000\023\000\000\000\
\\001\000\009\000\024\000\000\000\
\\029\000\000\000\
\\030\000\002\000\013\000\003\000\012\000\007\000\011\000\008\000\010\000\
\\010\000\009\000\014\000\008\000\000\000\
\\031\000\000\000\
\\032\000\000\000\
\\033\000\000\000\
\\034\000\000\000\
\\035\000\000\000\
\\036\000\000\000\
\\037\000\000\000\
\\038\000\000\000\
\\039\000\001\000\016\000\000\000\
\\040\000\001\000\016\000\000\000\
\\041\000\006\000\015\000\013\000\014\000\000\000\
\\042\000\012\000\026\000\000\000\
\\043\000\000\000\
\\044\000\006\000\015\000\000\000\
\"
val actionRowNumbers =
"\006\000\013\000\017\000\015\000\
\\012\000\005\000\007\000\001\000\
\\000\000\001\000\008\000\009\000\
\\000\000\001\000\001\000\003\000\
\\004\000\011\000\019\000\016\000\
\\014\000\000\000\010\000\018\000\
\\001\000\020\000\002\000"
val gotoT =
"\
\\001\000\005\000\002\000\026\000\003\000\004\000\004\000\003\000\
\\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\004\000\004\000\003\000\005\000\015\000\006\000\001\000\000\000\
\\001\000\016\000\003\000\004\000\004\000\003\000\005\000\002\000\
\\006\000\001\000\000\000\
\\003\000\004\000\006\000\017\000\000\000\
\\000\000\
\\000\000\
\\001\000\018\000\003\000\004\000\004\000\003\000\005\000\002\000\
\\006\000\001\000\000\000\
\\003\000\004\000\004\000\019\000\006\000\001\000\000\000\
\\003\000\004\000\006\000\020\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\023\000\003\000\004\000\004\000\003\000\005\000\002\000\
\\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\003\000\004\000\004\000\003\000\005\000\025\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\"
val numstates = 27
val numrules = 16
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle General.Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(List.map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | ATOMM of unit ->  (string) | TERM2_1 of unit ->  (Prop)
 | TERM3 of unit ->  (Prop) | TERM2 of unit ->  (Prop)
 | TERM of unit ->  (Prop) | START of unit ->  (Prop option)
 | EXP of unit ->  (Prop)
end
type svalue = MlyValue.svalue
type result = Prop option
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn (T 3) => true | _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 4) => true | _ => false
val showTerminal =
fn (T 0) => "AND"
  | (T 1) => "FALSE"
  | (T 2) => "TRUE"
  | (T 3) => "SEMI"
  | (T 4) => "EOF"
  | (T 5) => "OR"
  | (T 6) => "NOT"
  | (T 7) => "LPAREN"
  | (T 8) => "RPAREN"
  | (T 9) => "IF"
  | (T 10) => "THEN"
  | (T 11) => "ELSE"
  | (T 12) => "IFF"
  | (T 13) => "ATOMM"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 12) $$ (T 11) $$ (T 10) $$ (T 9) $$ (T 8) $$ (T 7) $$ (T 6) $$ 
(T 5) $$ (T 4) $$ (T 3) $$ (T 2) $$ (T 1) $$ (T 0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.EXP EXP1, EXP1left, EXP1right)) :: rest671)
) => let val  result = MlyValue.START (fn _ => let val  (EXP as EXP1)
 = EXP1 ()
 in (SOME EXP)
end)
 in ( LrTable.NT 1, ( result, EXP1left, EXP1right), rest671)
end
|  ( 1, ( rest671)) => let val  result = MlyValue.START (fn _ => (NONE
))
 in ( LrTable.NT 1, ( result, defaultPos, defaultPos), rest671)
end
|  ( 2, ( ( _, ( MlyValue.ATOMM ATOMM1, ATOMM1left, ATOMM1right)) :: 
rest671)) => let val  result = MlyValue.TERM (fn _ => let val  (ATOMM
 as ATOMM1) = ATOMM1 ()
 in (ATOM(ATOMM))
end)
 in ( LrTable.NT 2, ( result, ATOMM1left, ATOMM1right), rest671)
end
|  ( 3, ( ( _, ( _, TRUE1left, TRUE1right)) :: rest671)) => let val  
result = MlyValue.TERM (fn _ => (TOP))
 in ( LrTable.NT 2, ( result, TRUE1left, TRUE1right), rest671)
end
|  ( 4, ( ( _, ( _, FALSE1left, FALSE1right)) :: rest671)) => let val 
 result = MlyValue.TERM (fn _ => (BOTTOM))
 in ( LrTable.NT 2, ( result, FALSE1left, FALSE1right), rest671)
end
|  ( 5, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.EXP EXP1, _,
 _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = 
MlyValue.TERM (fn _ => let val  (EXP as EXP1) = EXP1 ()
 in (EXP)
end)
 in ( LrTable.NT 2, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 6, ( ( _, ( MlyValue.TERM2_1 TERM2_11, _, TERM2_11right)) :: ( _,
 ( _, NOT1left, _)) :: rest671)) => let val  result = MlyValue.TERM2_1
 (fn _ => let val  (TERM2_1 as TERM2_11) = TERM2_11 ()
 in (NOT(TERM2_1))
end)
 in ( LrTable.NT 5, ( result, NOT1left, TERM2_11right), rest671)
end
|  ( 7, ( ( _, ( MlyValue.TERM TERM1, TERM1left, TERM1right)) :: 
rest671)) => let val  result = MlyValue.TERM2_1 (fn _ => let val  (
TERM as TERM1) = TERM1 ()
 in (TERM)
end)
 in ( LrTable.NT 5, ( result, TERM1left, TERM1right), rest671)
end
|  ( 8, ( ( _, ( MlyValue.TERM2_1 TERM2_11, TERM2_11left, 
TERM2_11right)) :: rest671)) => let val  result = MlyValue.TERM2 (fn _
 => let val  (TERM2_1 as TERM2_11) = TERM2_11 ()
 in (TERM2_1)
end)
 in ( LrTable.NT 3, ( result, TERM2_11left, TERM2_11right), rest671)

end
|  ( 9, ( ( _, ( MlyValue.TERM2_1 TERM2_11, _, TERM2_11right)) :: _ ::
 ( _, ( MlyValue.TERM2 TERM21, TERM21left, _)) :: rest671)) => let
 val  result = MlyValue.TERM2 (fn _ => let val  (TERM2 as TERM21) = 
TERM21 ()
 val  (TERM2_1 as TERM2_11) = TERM2_11 ()
 in (AND(TERM2,TERM2_1))
end)
 in ( LrTable.NT 3, ( result, TERM21left, TERM2_11right), rest671)
end
|  ( 10, ( ( _, ( MlyValue.TERM2 TERM21, TERM21left, TERM21right)) :: 
rest671)) => let val  result = MlyValue.TERM3 (fn _ => let val  (TERM2
 as TERM21) = TERM21 ()
 in (TERM2)
end)
 in ( LrTable.NT 4, ( result, TERM21left, TERM21right), rest671)
end
|  ( 11, ( ( _, ( MlyValue.TERM2 TERM21, _, TERM21right)) :: _ :: ( _,
 ( MlyValue.TERM3 TERM31, TERM31left, _)) :: rest671)) => let val  
result = MlyValue.TERM3 (fn _ => let val  (TERM3 as TERM31) = TERM31
 ()
 val  (TERM2 as TERM21) = TERM21 ()
 in (OR(TERM3,TERM2))
end)
 in ( LrTable.NT 4, ( result, TERM31left, TERM21right), rest671)
end
|  ( 12, ( ( _, ( MlyValue.TERM3 TERM31, TERM31left, TERM31right)) :: 
rest671)) => let val  result = MlyValue.EXP (fn _ => let val  (TERM3
 as TERM31) = TERM31 ()
 in (TERM3)
end)
 in ( LrTable.NT 0, ( result, TERM31left, TERM31right), rest671)
end
|  ( 13, ( ( _, ( MlyValue.EXP EXP1, _, EXP1right)) :: _ :: ( _, ( 
MlyValue.TERM3 TERM31, _, _)) :: ( _, ( _, IF1left, _)) :: rest671))
 => let val  result = MlyValue.EXP (fn _ => let val  (TERM3 as TERM31)
 = TERM31 ()
 val  (EXP as EXP1) = EXP1 ()
 in (IMP(TERM3,EXP))
end)
 in ( LrTable.NT 0, ( result, IF1left, EXP1right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.EXP EXP1, _, EXP1right)) :: _ :: ( _, ( 
MlyValue.TERM3 TERM31, TERM31left, _)) :: rest671)) => let val  result
 = MlyValue.EXP (fn _ => let val  (TERM3 as TERM31) = TERM31 ()
 val  (EXP as EXP1) = EXP1 ()
 in (IFF(TERM3,EXP))
end)
 in ( LrTable.NT 0, ( result, TERM31left, EXP1right), rest671)
end
|  ( 15, ( ( _, ( MlyValue.TERM3 TERM32, _, TERM32right)) :: _ :: ( _,
 ( MlyValue.EXP EXP1, _, _)) :: _ :: ( _, ( MlyValue.TERM3 TERM31, _,
 _)) :: ( _, ( _, IF1left, _)) :: rest671)) => let val  result = 
MlyValue.EXP (fn _ => let val  TERM31 = TERM31 ()
 val  (EXP as EXP1) = EXP1 ()
 val  TERM32 = TERM32 ()
 in (ITE(TERM31,EXP,TERM32))
end)
 in ( LrTable.NT 0, ( result, IF1left, TERM32right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.START x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : Prop_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun AND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun FALSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun TRUE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun SEMI (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun OR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun NOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun IF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun THEN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun ELSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun IFF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun ATOMM (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.ATOMM (fn () => i),p1,p2))
end
end
