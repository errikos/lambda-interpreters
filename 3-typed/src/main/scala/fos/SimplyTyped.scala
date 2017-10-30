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
    | "if"~Term~"then"~Term~"else"~Term ^^ {
        case "if"~cond~"then"~t1~"else"~t2 => If(cond, t1, t2) }
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
    | "let"~ident~":"~Type~"="~Term~"in"~Term ^^ {  // Parse and desugar "let" statement
        case "let"~v~":"~tp~"="~t1~"in"~t2 => App(Abs(v, tp, t2), t1) }
    | "{"~Term~","~Term~"}" ^^ { case "{"~t1~","~t2~"}" => TermPair(t1, t2) }
    | "fst"~Term ^^ { case "fst"~t => First(t) }
    | "snd"~Term ^^ { case "snd"~t => Second(t) }
    | "("~>Term<~")"
  )

  /** Parser for types.
   *
   *  T ::= "Bool"
   *      | "Nat"
   *      | T "->" T
   *      | "(" T ")"
   */
  def Type: Parser[Type] =
    rep1sep(PairType, "->") ^^ rightAssociateFun

  def PairType: Parser[Type] =
    rep1sep(BaseType, "*") ^^ rightAssociatePair

  def BaseType: Parser[Type] = (
      "Bool" ^^^ TypeBool
    | "Nat" ^^^ TypeNat
    | "("~>Type<~")"
  )

  /** Right-associate a list of parsed Types.
   *
   * @param typeList the list of parsed Types
   * @return         the right-associated TypeFun object
   */
  def rightAssociateFun[T](typeList: List[Type]): Type = typeList match {
    case t :: Nil => t
    case t :: ts => TypeFun(t, rightAssociateFun(ts))
  }

  def rightAssociatePair[T](typeList: List[Type]): Type = typeList match {
    case t :: Nil => t
    case t :: ts => TypePair(t, rightAssociatePair(ts))
  }

  /** Return the free variables in t.
    *
    *  Rules:
    *    FV(x) = { x }
    *    FV(λx.t) = FV(t) \ { x }
    *    FV(t1 t2) = FV(t1) ∪ FV(t2)
    *
    *  @param t the given term.
    */
  def fv(t: Term): Set[String] = t match {
    case If(t1, t2, t3) => fv(t1) ++ fv(t2) ++ fv(t3)
    case Pred(t1) => fv(t1)
    case Succ(t1) => fv(t1)
    case IsZero(t1) => fv(t1)
    case Var(v) => Set(v)
    case Abs(v, _, t1) => fv(t1) - v
    case App(t1, t2) => fv(t1) ++ fv(t2)
    // Pairs
    case TermPair(t1, t2) => fv(t1) ++ fv(t2)
    case First(t1) => fv(t1)
    case Second(t1) => fv(t1)
    case _ => Set()
  }

  /** Object that generates fresh variables.
    *  Format is: "_%d" (in C-printf style).
    */
  object VarGen {
    private var cvar: Int = 0
    def getVar: String = {
      cvar += 1
      "_" + cvar.toString
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
    case Abs(v, tp, t1) =>
      val f = VarGen.getVar // Get a fresh variable.
      Abs(f, tp, subst(t1, v, Var(f))) // Substitute v for f in t and return.
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
    case If(t1, t2, t3) => If(subst(t1, x, s), subst(t2, x, s), subst(t3, x, s))
    case Pred(t1) => Pred(subst(t1, x, s))
    case Succ(t1) => Succ(subst(t1, x, s))
    case IsZero(t1) => IsZero(subst(t1, x, s))
    case Var(v) if v == x => s
    case Var(v) if v != x => t
    case a @ Abs(v, _, _) if v == x => a
    case Abs(v, tp, t1) if v != x && !fv(s).contains(v) => Abs(v, tp, subst(t1, x, s))
    case r @ Abs(v, _, _) if v != x && fv(s).contains(v) =>  // α-reduction is needed
      alpha(r) match { case Abs(f, tp, t1) => Abs(f, tp, subst(t1, x, s)) }
    case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
    // Pairs
    case TermPair(t1, t2) => TermPair(subst(t1, x, s), subst(t2, x, s))
    case First(t1) => First(subst(t1, x, s))
    case Second(t1) => Second(subst(t1, x, s))
    case t1 => t1
  }

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    // Computation rules
    case If(True(), t1, _) => t1
    case If(False(), _, t2) => t2
    case IsZero(Zero()) => True()
    case IsZero(Succ(t1)) if isNumValue(t1) => False()
    case Pred(Zero()) => Zero()
    case Pred(Succ(nv)) => nv
    case App(Abs(x, _, t1), v2) if isValue(v2) => subst(t1, x, v2)
    // Congruence rules
    case If(t1, t2, t3) => If(reduce(t1), t2, t3)
    case IsZero(t1) => IsZero(reduce(t1))
    case Succ(t1) => Succ(reduce(t1))
    case Pred(t1) => Pred(reduce(t1))
    case App(v1, t2) if isValue(v1) => App(v1, reduce(t2))
    case App(t1, t2) => App(reduce(t1), t2)
    // Pairs
    case First(p @ TermPair(v1, _)) if isValue(p) => v1
    case Second(p @ TermPair(_, v2)) if isValue(p) => v2
    case First(p) => First(reduce(p))
    case Second(p) => Second(reduce(p))
    case TermPair(v1, t2) if isValue(v1) => TermPair(v1, reduce(t2))
    case TermPair(t1, t2) => TermPair(reduce(t1), t2)
    case _ => throw NoRuleApplies(t)
  }

  def isValue(t: Term): Boolean = t match {
    case True() => true
    case False() => true
    case Abs(_, _, _) => true
    case TermPair(v1, v2) if isValue(v1) && isValue(v2) => true
    case t1 => isNumValue(t1)
  }

  def isNumValue(t: Term): Boolean = t match {
    case Zero() => true
    case Succ(nv) => isNumValue(nv)
    case _ => false
  }

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type = t match {
    case True() => TypeBool
    case False() => TypeBool
    case Zero() => TypeNat
    case Pred(t1) if typeof(ctx, t1) == TypeNat => TypeNat
    case Succ(t1) if typeof(ctx, t1) == TypeNat => TypeNat
    case IsZero(t1) if typeof(ctx, t1) == TypeNat => TypeBool
    case If(t1, t2, t3) if typeof(ctx, t1) == TypeBool =>
      val tp2 = typeof(ctx, t2)
      val tp3 = typeof(ctx, t3)
      if (tp2 == tp3) tp2
      else throw TypeError(t, "parameter type mismatch: expected " + tp2 + ", found " + tp3)
    case Var(x) =>
      val o: Option[(String, Type)] = ctx find { case (s, _) => s == x }
      o.getOrElse(throw TypeError(t, "could not infer type for: " + t.toString)) match {
        case (_, tp) => tp
      }
    case Abs(x, tp1, t1) => TypeFun(tp1, typeof((x, tp1)::ctx, t1))
    case App(t1, t2) => (typeof(ctx, t1), typeof(ctx, t2)) match {
      case (TypeFun(t11, t12), tp) =>
        if (tp == t11) t12
        else throw TypeError(t, "parameter type mismatch: expected " + t11.toString + ", found " + tp.toString)
      case (tp1, _) => throw TypeError(t, "parameter type mismatch: expected Type -> Type, found " + tp1)
    }
    // Pairs
    case TermPair(t1, t2) => TypePair(typeof(ctx, t1), typeof(ctx, t2))
    case First(p) => typeof(ctx, p) match {
      case TypePair(tp1, _) => tp1
      case tp => throw TypeError(t, "pair type expected but " + tp.toString + " found")
    }
    case Second(p) => typeof(ctx, p) match {
      case TypePair(_, tp2) => tp2
      case tp => throw TypeError(t, "pair type expected but " + tp.toString + " found")
    }
    case _ => throw TypeError(t, "could not infer type for: " + t.toString)
  }

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString: String =
      msg + "\n" + t
  }

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
