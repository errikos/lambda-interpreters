package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  untyped lambda calculus found in Chapter 5 of
 *  the TAPL book.
 */
object Untyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".")
  import lexical.Identifier

  /** t ::= x
          | '\' x '.' t
          | t t
          | '(' t ')'
   */
  def term: Parser[Term] = (
      chainl1(term2, success(App(_: Term, _: Term)))
  )

  def term2: Parser[Term] = (
      ident ^^ { case v => Var(v) }
    | "\\"~ident~"."~term ^^ { case "\\"~v~"."~t => Abs(v, t) }
    | "("~>term<~")"
  )

  /** Return the free variables in t.
   *
   *  @param t the given term.
   */
  def fv(t: Term): Set[String] = t match {
    case Var(v) => Set(v)
    case Abs(v, t) => fv(t) - v
    case App(t1, t2) => fv(t1) ++ fv(t2)
  }

  /** Object that generates fresh variables.
   *  Format is: "_%d" (in C-printf style).
   */
  object VarGen {
    private var cvar: Int = 0
    def getVar: String = {
      cvar += 1
      "_" + cvar.toString()
    }
  }

  /** <p>
   *    Alpha conversion: term <code>t</code> should be a lambda abstraction
   *    <code>\x. t</code>.
   *  </p>
   *  <p>
   *    All free occurences of <code>x</code> inside term <code>t/code>
   *    will be renamed to a unique name.
   *  </p>
   *
   *  @param t the given lambda abstraction.
   *  @return  the transformed term with bound variables renamed.
   */
  def alpha(t: Term): Term = t match {
    case Abs(v, t) => {
      val f = VarGen.getVar
      Abs(f, subst(t, v, Var(f)))
    }
    case _ => null  // This should never match.
  }

  /** Straight forward substitution method
   *  (see definition 5.3.5 in TAPL book).
   *  [x -> s]t
   *
   *  @param t the term in which we perform substitution
   *  @param x the variable name
   *  @param s the term we replace x with
   *  @return  the substituted term
   */
  def subst(t: Term, x: String, s: Term): Term = t match {
    case Var(v) if v == x => s
    case Var(v) if v != x => t
    case Abs(v, t) if v == x => t
    case Abs(v, t) if v != x && !fv(s).contains(v) => Abs(v, subst(t, x, s))
    case r @ Abs(v, t) if v != x && fv(s).contains(v) => {
      // α-reduction is needed
      alpha(r) match { case Abs(f, t) => Abs(f, subst(t, x, s)) }
    }
    case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
  }

  /** Term 't' does not match any reduction rule. */
  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Normal order (leftmost, outermost redex first).
   *
   *  @param t the initial term
   *  @return  the reduced term
   */
  def reduceNormalOrder(t: Term): Term = t match {
    case App(Abs(v, t1), t2) => subst(t1, v, t2)
    case App(t1, t2) => try { App(reduceNormalOrder(t1), t2) } catch {
      case NoReductionPossible(t1) => App(t1, reduceNormalOrder(t2))
    }
    case Abs(v, t) => Abs(v, reduceNormalOrder(t))
    case _ => throw new NoReductionPossible(t)
  }

  /** Call by value reducer. */
  def reduceCallByValue(t: Term): Term = t match {
    case App(t1, a @ Abs(v, t2)) => App(reduceCallByValue(t1), a)
    case App(t1, t2) => App(t1, reduceCallByValue(t2))
    case _ => throw new NoReductionPossible(t)
  }

  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the method that reduces a term by one step.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoReductionPossible(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        println("normal order: ")
        for (t <- path(trees, reduceNormalOrder))
          println(t)
        println("call-by-value: ")
        for (t <- path(trees, reduceCallByValue))
          println(t)

      case e =>
        println(e)
    }
  }
}
