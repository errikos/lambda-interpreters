package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd")

  /** Term     ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] = // Left-associate applications
    chainl1(Term2, success(App(_: Term, _: Term)))

  def Term2: Parser[Term] = (
      "true" ^^^ True()
    | "false" ^^^ False()
    | "if"~Term2~"then"~Term2~"else"~Term2 ^^ {
      case "if"~cond~"then"~t1~"else"~t2 => If(cond, t1, t2)
      }
    | numericLit ^^ {
        value => {
          var x: Term = Zero()
          for (_ <- 1 to value.toInt) {
            x = Succ(x)
          }
          x
        }
      }
    | "pred"~Term ^^ { case "pred"~t => Pred(t) }
    | "succ"~Term ^^ { case "succ"~t => Succ(t) }
    | "iszero"~Term ^^ { case "iszero"~t => IsZero(t) }
    | ident ^^ (v => Var(v))
    | "\\"~ident~":"~Type~"."~Term ^^ { case "\\"~v~":"~tp~"."~t => Abs(v, tp, t) }
    | "("~>Term<~")"
  )

  /** Parser for types.
   *
   *  T ::= "Bool"
   *      | "Nat"
   *      | T "->" T
   *      | "(" T ")"
   */
  def Type: Parser[Type] = {
    rep1sep(Type2, "->") ^^ rightAssociateTypes
  }

  def Type2: Parser[Type] = (
      "Bool" ^^^ TypeBool
    | "Nat" ^^^ TypeNat
    | "("~>Type<~")"
  )

  /** Right-associate a list of parsed Types.
   *
   * @param typeList the list of parsed Types
   * @return         the right-associated TypeFun object
   */
  def rightAssociateTypes(typeList: List[Type]): Type = typeList match {
    case t :: Nil => t
    case t :: ts => TypeFun(t, rightAssociateTypes(ts))
  }

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString: String =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    case If(True(), t1, t2) => t1
    case If(False(), t1, t2) => t2
    case IsZero(Zero()) => True()
    case IsZero(Succ(_)) => False()
    case Pred(Zero()) => Zero()
    case Pred(Succ(nv)) => nv
//    case App(Abs(x, tp, t1), v2) => ???
    case _ => throw NoRuleApplies(t)
  }

  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type =
    ???

  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(Term)(tokens) match {
      case Success(trees, _) =>
        try {
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
