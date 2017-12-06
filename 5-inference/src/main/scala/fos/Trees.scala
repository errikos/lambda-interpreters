package fos

import scala.util.parsing.input.Positional

abstract class Term extends Positional

case class True() extends Term {
  override def toString = "true"
}

case class False() extends Term {
  override def toString = "false"
}

case class Zero() extends Term {
  override def toString = "0"
}

case class Succ(t: Term) extends Term {
  override def toString: String = "succ " + t
}

case class Pred(t: Term) extends Term {
  override def toString: String = "pred " + t
}

case class IsZero(t: Term) extends Term {
  override def toString: String = "iszero " + t
}

case class If(cond: Term, t1: Term, t2: Term) extends Term {
  override def toString: String = "if " + cond + " then " + t1 + " else " + t2
}

case class Var(name: String) extends Term {
  override def toString: String = name
}

case class Abs(v: String, tp: TypeTree, t: Term) extends Term {
  override def toString: String = "(\\" + v + ":" + tp + "." + t + ")"
}

case class App(t1: Term, t2: Term) extends Term {
  override def toString: String = t1.toString + (t2 match {
    case App(_, _) => " (" + t2.toString + ")" // left-associative
    case _         => " " + t2.toString
  })
}
case class Let(x: String, tp: TypeTree, v: Term, t: Term) extends Term {
  override def toString: String = "let " + x + ":" + tp + " = " + v + " in " + t
}

// Note that TypeTree is distinct from Type.
// The former is how types are parsed, the latter is how types are represented.
// We need this distinction because:
// 1) There are type vars, which can't be written by our users, but are needed by the inferencer.
// 2) There are empty types, which can be written, but aren't directly supported by the inferencer.
abstract class TypeTree extends Positional {
  def tpe: Type
}

case class BoolTypeTree() extends TypeTree {
  override def tpe: BoolType.type = BoolType
  override def toString: String = "Bool"
}

case class NatTypeTree() extends TypeTree {
  override def tpe: NatType.type = NatType
  override def toString = "Nat"
}

case class FunTypeTree(t1: TypeTree, t2: TypeTree) extends TypeTree {
  override def tpe = FunType(t1.tpe, t2.tpe)
  override def toString: String = (t1 match {
    case FunTypeTree(_, _) => "(" + t1 + ")" // right-associative
    case _             => t1.toString
  }) + "->" + t2
}

case class EmptyTypeTree() extends TypeTree {
  override def tpe = throw new UnsupportedOperationException
  override def toString = "_"
}
