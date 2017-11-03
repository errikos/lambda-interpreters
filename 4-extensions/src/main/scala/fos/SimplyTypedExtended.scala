package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTypedExtended extends  StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*", "+",
                              "=>", "|")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd", "fix", "letrec",
                              "case", "of", "inl", "inr", "as")


  /** Term     ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] =
    chainl1(SimpleTerm, success(App(_: Term, _: Term)))

  /** SimpleTerm ::= "true"
   *               | "false"
   *               | number
   *               | "succ" Term
   *               | "pred" Term
   *               | "iszero" Term
   *               | "if" Term "then" Term "else" Term
   *               | ident
   *               | "\" ident ":" Type "." Term
   *               | "(" Term ")"
   *               | "let" ident ":" Type "=" Term "in" Term
   *               | "{" Term "," Term "}"
   *               | "fst" Term
   *               | "snd" Term
   *               | "inl" Term "as" Type
   *               | "inr" Term "as" Type
   *               | "case" Term "of" "inl" ident "=>" Term "|" "inr" ident "=>" Term
   *               | "fix" Term
   *               | "letrec" ident ":" Type "=" Term "in" Term</pre>
   */
  def SimpleTerm: Parser[Term] = (
      "true" ^^^ True()
    | "false" ^^^ False()
    | numericLit ^^ {
        value => {
          var x: Term = Zero()
          for (_ <- 1 to value.toInt) x = Succ(x)
          x
        }
      }
    | "succ"~Term ^^ { case "succ"~term => Succ(term) }
    | "pred"~Term ^^ { case "pred"~term => Pred(term) }
    | "iszero"~Term ^^ { case "iszero"~term => IsZero(term) }
    | "if"~Term~"then"~Term~"else"~Term ^^ { case "if"~cond~"then"~t1~"else"~t2 => If(cond, t1, t2) }
    | ident ^^ { v => Var(v) }
    | "\\"~ident~":"~Type~"."~Term ^^ { case "\\"~v~":"~tp~"."~t => Abs(v, tp, t) }
    | "let"~ident~":"~Type~"="~Term~"in"~Term ^^ {  // Parse and desugar "let" statement
        case "let"~v~":"~tp~"="~t1~"in"~t2 => App(Abs(v, tp, t2), t1)
      }
    | "{"~Term~","~Term~"}" ^^ { case "{"~t1~","~t2~"}" => TermPair(t1, t2) }
    | "fst"~Term ^^ { case "fst"~t => First(t) }
    | "snd"~Term ^^ { case "snd"~t => Second(t) }
    | "inl"~Term~"as"~Type ^^ { case "inl"~t~"as"~tp => Inl(t, tp) }
    | "inr"~Term~"as"~Type ^^ { case "inr"~t~"as"~tp => Inl(t, tp) }
    | "case"~Term~"of"~"inl"~ident~"=>"~Term~"|"~"inr"~ident~"=>"~Term ^^ {
        case "case"~t1~"of"~"inl"~x1~"=>"~t2~"|"~"inr"~x2~"=>"~t3 => Case(t1, x1, t2, x2, t3)
      }
    | "fix"~Term ^^ { case "fix"~term => Fix(term) }
    | "letrec"~ident~":"~Type~"="~Term~"in"~Term ^^ { // Parse and desugar "letrec" statement
        case "letrec"~x~":"~tp~"="~t1~"in"~t2 => App(Abs(x, tp, t2), Fix(Abs(x, tp, t1)))
      }
    | "("~>Term<~")"
  )

  /** Type       ::= SimpleType [ "->" Type ]
   */
  def Type: Parser[Type] =
    ???

  /** SimpleType ::= BaseType [ ("*" SimpleType) | ("+" SimpleType) ]
   */
  def SimpleType: Parser[Type] =
    ???

  /** BaseType ::= "Bool" | "Nat" | "(" Type ")"
   */
  def BaseType: Parser[Type] =
    ???


  /** Call by value reducer. */
  def reduce(t: Term): Term =
    throw NoRuleApplies(t)

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString: String = msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[Pair[String, Type]]

  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type =
    throw TypeError(t, "could not infer type for: " + t.toString)

  def typeof(t: Term): Type = try {
    typeof(Nil, t)
  } catch {
    case err @ TypeError(_, _) =>
      Console.println(err)
      null
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
          println("parsed: " + trees)
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
