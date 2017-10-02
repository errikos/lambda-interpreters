package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the NB
 *  language of booleans and numbers found in Chapter 3 of
 *  the TAPL book.
 */
object Arithmetic extends StandardTokenParsers {
  lexical.reserved ++= List("true", "false", "0", "if", "then", "else", "succ", "pred", "iszero")

  import lexical.NumericLit

  /** term ::= 'true'
             | 'false'
             | 'if' term 'then' term 'else' term
             | '0' | '1' | '2' | ...
             | 'succ' term
             | 'pred' term
             | 'iszero' term
   */
  def term: Parser[Term] = (
      "true" ^^^ True
    | "false" ^^^ False
    | "if"~term~"then"~term~"else"~term ^^ {
        case "if"~cond~"then"~t1~"else"~t2 => If(cond, t1, t2)
      }
    | numericLit ^^ {
        case value => {
          var x:Term = Zero
          for (i <- 1 to value.toInt) { x = Succ(x) }
          x
        }
      }
    | "succ"~term ^^ { case "succ"~t => Succ(t) }
    | "pred"~term ^^ { case "pred"~t => Pred(t) }
    | "iszero"~term ^^ {case "iszero"~t => IsZero(t) }
  )

  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Return a list of at most n terms, each being one step of reduction. */
  def path(t: Term, n: Int = 64): List[Term] =
    if (n <= 0) Nil
    else
      t :: {
        try {
          path(reduce(t), n - 1)
        } catch {
          case NoReductionPossible(t1) =>
            Nil
        }
      }

  /** Perform one step of reduction, when possible.
   *  If reduction is not possible NoReductionPossible exception
   *  with corresponding irreducible term should be thrown.
   */
  def reduce(t: Term): Term = t match {
    case If(True, t1, t2) => t1
    case If(False, t1, t2) => t2
    case IsZero(Zero) => True
    case IsZero(Succ(_)) => False
    case Pred(Zero) => Zero
    case Pred(Succ(x)) => x
    case If(t1, t2, t3) => If(reduce(t1), t2, t3)
    case IsZero(t) => IsZero(reduce(t))
    case Pred(t) => Pred(reduce(t))
    case Succ(t) => Succ(reduce(t))
    case _ => throw new NoReductionPossible(t)
  }

  case class TermIsStuck(t: Term) extends Exception(t.toString)

  /** Perform big step evaluation (result is always a value.)
   *  If evaluation is not possible TermIsStuck exception with
   *  corresponding inner irreducible term should be thrown.
   */
  def eval(t: Term): Term =
    ???

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        for (t <- path(trees))
          println(t)
        try {
          print("Big step: ")
          println(eval(trees))
        } catch {
          case TermIsStuck(t) => println("Stuck term: " + t)
        }
      case e =>
        println(e)
    }
  }
}
