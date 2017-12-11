package fos

object Infer {
  case class TypeScheme(params: List[TypeVar], tp: Type)
  type Env = List[(String, TypeScheme)]
  type Constraint = (Type, Type)

  case class TypeError(msg: String) extends Exception(msg)

  object TypeVarGen {
    private var cvar: Int = 0
    def getTypeVar: TypeVar = {
      cvar += 1
      TypeVar("_" + cvar.toString)
    }
  }

  def collect(env: Env, t: Term): (Type, List[Constraint]) = t match {
    // true, false, zero
    case True() => (BoolType, List.empty)
    case False() => (BoolType, List.empty)
    case Zero() => (NatType, List.empty)
    // pred, succ, iszero
    case Pred(term) =>
      val (typename, constraints) = collect(env, term)
      (NatType, List.empty ++ (constraints.toSet + ((typename, NatType))))
    case Succ(term) =>
      val (typename, constraints) = collect(env, term)
      (NatType, List.empty ++ (constraints.toSet + ((typename, NatType))))
    case IsZero(term) =>
      val (typename, constraints) = collect(env, term)
      (BoolType, List.empty ++ (constraints.toSet + ((typename, NatType))))
    case If(t1, t2, t3) =>  // if ... then ... else ...
      // Γ ⊢ t1: T1 | C1    Γ ⊢ t2 : T2 | C2
      //          Γ ⊢ t3 : T3 | C3
      // C = C1 ∪ C2 ∪ C3 ∪ {T1=Bool, T2=T3}
      // ------------------------------------
      //  Γ ⊢ if t1 then t2 else t3 : T2 | C

      // collect typenames and constraints from t1, t2 and t3
      // Γ ⊢ t1: T1 | C1,  Γ ⊢ t2: T2 | C2,  Γ ⊢ t3: T3 | C3
      val (typename1, constraints1) = collect(env, t1)
      val (typename2, constraints2) = collect(env, t2)
      val (typename3, constraints3) = collect(env, t3)
      // form new constraints
      // C = C1 ∪ C2 ∪ C3 ∪ {T1=Bool, T2=T3}
      val new_constraints: Set[Constraint] = Set((typename1, BoolType), (typename2, typename3))
      val constraints = constraints1.toSet union constraints2.toSet union constraints3.toSet union new_constraints
      (typename2, List.empty ++ constraints)
    case Var(x) =>  // variable
      val o: Option[(String, TypeScheme)] = env find { case (s, _) => s == x }
      o.getOrElse(throw TypeError("Could not collect type for: " + t)) match {
        case (_, ts) => (ts.tp, List.empty)
      }
    case Abs(v, tp, term) =>  // abstractions
      val vtp: Type = tp match {
        //  Γ, x : X ⊢ t : T2 | C
        //       X is fresh
        // -----------------------
        // Γ ⊢ λx. t : X -> T2 | C
        case EmptyTypeTree() => TypeVarGen.getTypeVar  // type not declared

        //    Γ, x : T1 ⊢ t : T2 | C
        // ----------------------------
        // Γ ⊢ λx: T1. t : T1 -> T2 | C
        case dtp => dtp.tpe  // type declared
      }
      val (typename2, constraints) = collect((v, TypeScheme(List.empty, vtp))::env, term)
      (FunType(vtp, typename2), constraints)
    case App(t1, t2) =>  // application
      //  Γ ⊢ t1 : T1 | C1    Γ ⊢ t2 : T2 | C2
      // X is fresh, C = C1 ∪ C2 ∪ {T1=T2 -> X}
      // --------------------------------------
      //         Γ ⊢ t1 t2 : X | C

      // collect typenames and constraints from t1 and t2
      // Γ ⊢ t1 : T1 | C1,  Γ ⊢ t2 : T2 | C2
      val (typename1, constraints1) = collect(env, t1)
      val (typename2, constraints2) = collect(env, t2)
      // form new constraints
      // X is fresh, C = C1 ∪ C2 ∪ {T1=T2 -> X}
      val tp = TypeVarGen.getTypeVar
      val new_constraints: Set[Constraint] = Set((typename1, FunType(typename2, tp)))
      val constraints = constraints1.toSet union constraints2.toSet union new_constraints
      (tp, List.empty ++ constraints)
    case _ => throw TypeError("Could not collect type and constraints")
  }

  /** Unify (solve) the constraints in the given constraint list.
    *
    * @param c the constraint list.
    * @return a "sigma" function, which accepts a Type and returns a new Type, without type variables.
    */
  def unify(c: List[Constraint]): Type => Type =
    // apply_substitution is being curried, expects one type, returns its substitution
    apply_substitution(unify_map(c))

  private def unify_map(c: List[Constraint]): Map[Type, Type] = c match {
    case Nil => Map.empty
    case constraint :: tail => constraint match {
      case (s, t) if s == t => unify_map(tail)
      case (s @ TypeVar(x), t) if !occurs_in(x, t) =>
        compose_subs(unify_map(replace_in_constraints(tail, x, t)), Map(s -> t))
      case (s, t @ TypeVar(x)) if !occurs_in(x, s) =>
        compose_subs(unify_map(replace_in_constraints(tail, x, s)), Map(t -> s))
      case (FunType(s1, s2), FunType(t1, t2)) => unify_map((s1, t1) :: (s2, t2) :: tail)
      case (s, t) => throw TypeError("Could not unify: %s with %s".format(s, t))
    }
  }

  /** Substitution composition (see TAPL p. 318).
    *
    * @param sigma the first substitution.
    * @param gamma the second substitution.
    * @return the composition of sigma and gamma.
    */
  private def compose_subs(sigma: Map[Type, Type], gamma: Map[Type, Type]): Map[Type, Type] = {
    gamma.map {
      case (x, t) => (x, apply_substitution(sigma)(t))
    } ++
      sigma.filter {
        case (x, _) if !(gamma contains x) => true
        case _ => false
      }
  }

  /** Given a type, return its substitution as given by the unifier.
    *
    * @param sub the unifier to use for the substitution
    * @param tp the input type (the type to substitute)
    * @return the resulting type given by sub (the unifier)
    */
  private def apply_substitution(sub: Map[Type, Type])(tp: Type): Type = tp match {
    case FunType(t1, t2) => FunType(apply_substitution(sub)(t1), apply_substitution(sub)(t2))
    case t @ TypeVar(_) if sub contains t => sub(t)
    case t => t
  }

  /** Occurs check.
    * Checks whether x exists in FV(t), where FV(t) is the set of type variables in t.
    *
    * @param x the type variable name to check.
    * @param t the type to check against
    * @return a Boolean indicating whether x occurs in t.
    */
  private def occurs_in(x: String, t: Type): Boolean = t match {
    case FunType(t1, t2) => occurs_in(x, t1) || occurs_in(x, t2)
    case TypeVar(y) => x == y
    case _ => false
  }

  /** Replace: type variable with name x,
    * with: type nt,
    * in: constraint list c.
    *
    * @param c the constraint list in which the replacement will take place.
    * @param x the name of the type variable to replace.
    * @param nt the new type.
    * @return the updated constraint list, where all occurrences of x have been replaced with nt.
    */
  private def replace_in_constraints(c: List[Constraint], x: String, nt: Type): List[Constraint] = {
    c.map {
      case (t1, t2) => (replace_in_type(t1, x, nt), replace_in_type(t2, x, nt))
    }
  }

  /** Replace: type variable with name x,
    * with: type nt,
    * in: type tp.
    *
    * @param tp the type in which the replacement will take place.
    * @param x the name of the type variable to replace.
    * @param nt the new type.
    * @return the updated type, where all occurrences of x have been replaced with nt.
    */
  private def replace_in_type(tp: Type, x: String, nt: Type): Type = tp match {
    case FunType(t1, t2) => FunType(replace_in_type(t1, x, nt), replace_in_type(t2, x, nt))
    case TypeVar(v) if x == v => nt
    case o => o
  }

}
