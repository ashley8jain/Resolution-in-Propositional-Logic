(* prop.sml *)

(* This file provides glue code for building the propulator using the
 * parser and lexer specified in prop.lex and prop.grm.
*)

structure Prop : sig
             val parse : string*string -> unit
                 end = 
struct

(* 
 * We apply the functors generated from prop.lex and prop.grm to produce
 * the PropParser structure.
 *)
open Ast
  (*structure PropLrVals =
    PropLrValsFun(structure Token = LrParser.Token)*)

    structure PropLrVals =
    PropLrValsFun(
      structure Token = LrParser.Token
      structure Ast = Ast)

  structure PropLex =
    PropLexFunc(structure Tokens = PropLrVals.Tokens)

  structure PropParser =
    Join(structure LrParser = LrParser
   structure ParserData = PropLrVals.ParserData
   structure Lex = PropLex)

(* 
 * We need a function which given a lexer invokes the parser. The
 * function invoke does this.
 *)

  fun invoke lexstream =
      let fun print_error (s,i:int,_) =
        TextIO.output(TextIO.stdOut,
          "Error, line " ^ (Int.toString i) ^ ", " ^ s ^ "\n")
       in PropParser.parse(0,lexstream,print_error,())
      end

(* 
 * Finally, we need a driver function that reads one or more expressions
 * from the standard input. The function parse, shown below, does
 * this. It runs the calculator on the standard input and terminates when
 * an end-of-file is encountered.
 *)

  fun parse(infile:string,outfile:string) = 
      let val inpStream = TextIO.openIn infile
        val outStream =  TextIO.openOut outfile
        val lexer = PropParser.makeLexer (fn _ =>
                                               (case TextIO.inputLine(inpStream)
                                                of SOME s => s
                                                 | _ => ""))
    val dummyEOF = PropLrVals.Tokens.EOF(0,0)
    val dummySEMI = PropLrVals.Tokens.SEMI(0,0)
    fun loop lexer =
        let val (result,lexer) = invoke lexer
      val (nextToken,lexer) = PropParser.Stream.get lexer
      val _ = case result
          of SOME r =>
        (TextIO.output(outStream,toPrefix(r) ^ "\n");TextIO.output(outStream,toPostfix(r) ^ "\n");print("cnf: "^toPrefix(make2cnf(r))^"\n");print("satisfiability: "^ Bool.toString(resolve(makeCnf((r))))^"\n"))
           | NONE => (TextIO.closeOut outStream)
         in if PropParser.sameToken(nextToken,dummyEOF) then ()
      else loop lexer
        end
       in loop lexer before TextIO.closeIn inpStream
      end

end (* structure Prop *)
