package viper.HHLVerifier.typing

import viper.HHLVerifier.management.PrettyPrinter

/** Parent for all types */
sealed trait Type {
  override def toString: String = {
    PrettyPrinter.formatType(this)
  }
}

/** Unknown Type, used as default before a type was determined */
case class UnknownType() extends Type
/** Integer type */
case class IntType() extends Type
/** Boolean type */
case class BoolType() extends Type

/** State type */
case class StateType() extends Type
/** TODO: Complete this */
case class StmtBlockType() extends Type

/**
 * Sequence type
 * @param sType type of contained elements
 */
case class SeqType(sType: Type) extends Type

/**
 * Set type
 * @param sType type of contained elements
 */
case class SetType(sType: Type) extends Type

/**
 * Map type
 * @param kType type of keys
 * @param vType type of values
 */
case class MapType(kType: Type, vType: Type) extends Type
