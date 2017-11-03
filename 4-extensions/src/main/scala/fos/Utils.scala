package fos

object Utils {

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



}
