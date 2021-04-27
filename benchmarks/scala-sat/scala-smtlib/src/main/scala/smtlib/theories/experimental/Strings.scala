package smtlib
package theories
package experimental

import trees.Terms._
import Operations._

object Strings {

  /** The strings and format are taken from here:
    * http://cvc4.cs.nyu.edu/wiki/Strings#Examples
    */

  private val StringConcat    = "str.++"
  private val StringLength    = "str.len"
  private val StringAt        = "str.at"
  private val StringSubstring = "str.substr"
  private val StringInRegex   = "str.in.re"
  private val StringToRegex   = "str.to.re"
  
  private val StringContains    = "str.contains"
  private val StringIndexOf     = "str.indexof"
  private val StringReplace     = "str.replace"
  private val StringPrefixOf    = "str.prefixof"
  private val StringSuffixOf    = "str.suffixof"
  private val StringStringToInt = "str.to.int"
  private val StringIntToString = "int.to.str"
  
  private val RegexConcat      = "re.++"
  private val RegexUnion       = "re.union"
  private val RegexInter       = "re.inter"
  private val RegexKleeneStar  = "re.*"
  private val RegexKleeneCross = "re.+"
  private val RegexKleeneOpt   = "re.opt"
  private val RegexRange       = "re.range"
  private val RegexLoop        = "re.loop"
  private val RegexLoop2       = "re.loop2"
  private val RegexEmpty       = "re.nostr"
  private val RegexAllChar     = "re.allchar"
  
  
  object StringSort {
    def apply(): Sort = {
      Sort(Identifier(SSymbol("String")))
    }
    def unapply(sort: Sort): Boolean = sort match {
      case Sort(Identifier(SSymbol("String"), Seq()), Seq()) => true
      case _ => false
    }
  }

  object StringLit {
    def apply(value: String): Term = SString(value)
    def unapply(term: Term): Option[String] = term match {
      case SString(value) => Some(value)
      case _ => None
    }
  }

  /** Length of string. */
  object Length extends Operation1 { override val name = StringLength }

  /** String concatenation takes at least 2 arguments. */
  object Concat extends OperationN2 { override val name = StringConcat }
  
  /** Character in String. First argument is a string term and second is a natural number. The index is starting from 0. */
  object At extends Operation2 { override val name = StringAt }
  
  /** Substring given string, start and length/offset */
  object Substring extends Operation3 { override val name = StringSubstring }
  
  /** Membership Constraint where first arg is a string term and second a regular expression. */
  object InRegex extends Operation2 { override val name = StringInRegex }
  
  /** String to Regular Expression Conversion.
    * The statement turns a regular expression that only contains a string s.
    */
  object ToRegex extends Operation1 { override val name = StringToRegex }
  
  object Regex {
    /** Membership constraint. See [InRegex]. */
    val In = InRegex
    /** Membership constraint. See [ToRegex]. */
    val To = ToRegex
    
    lazy val Star   = KleeneStar
    lazy val *      = KleeneStar
    lazy val Cross  = KleeneCross
    lazy val Plus   = KleeneCross
    lazy val +      = KleeneCross
    lazy val ?      = Opt
    lazy val NoStr  = Empty
    
    /** Regular Expression Concatenation. */
    object Concat extends OperationN2 { override val name = RegexConcat }
    /** Regular Expression Alternation. */
    object Union extends OperationN2 { override val name = RegexUnion }
    /** Regular Expression Intersection. */
    object Inter extends OperationN2 { override val name = RegexInter }
    /** Regular Expression Kleene-Star (equivalent to Loop(r, 0)) */
    object KleeneStar extends Operation1 { override val name = RegexKleeneStar }
    /** Regular Expression Kleene-Cross (equivalent to Loop(r, 1)) */
    object KleeneCross extends Operation1 { override val name = RegexKleeneCross }
    /** Regular Expression Option marker (equivalent to Loop(r, 0, 1)) */
    object Opt extends Operation1 { override val name = RegexKleeneOpt }
    /** Regular Expression Range where arguments s, t are single characters in double quotes, e.g. "a", "b". It returns a regular expression that contains any character between s and t.*/
    object Range extends Operation2 { override val name = RegexRange }
    
    /** Regular Expression Loop with arguments (r, l, u) where r is a regular expression, l is a non-negative constant integer, and u is an optional non-negative constant integer. It returns a regular expression that contains at least l repetitions of r and at most u repetitions of r. If l >= u, it returns exactly l repetitions of r.*/
    object Loop {
      def apply(r: Term, minRepetitions: Term, maxRepetitions: Term): Term =
        FunctionApplication(
          QualifiedIdentifier(Identifier(SSymbol(RegexLoop))),
          Seq(r, minRepetitions, maxRepetitions)
        )
      def apply(r: Term, minRepetitions: Term): Term =
        FunctionApplication(
          QualifiedIdentifier(Identifier(SSymbol(RegexLoop))),
          Seq(r, minRepetitions)
        )
      def unapplySeq(term: Term): Option[Seq[Term]] = term match {
        case FunctionApplication(
          QualifiedIdentifier(
            Identifier(SSymbol(RegexRange), Seq()),
            None
          ), seqTerm) if seqTerm.length == 2 || seqTerm.length == 3 => Some(seqTerm)
        case _ => None
      }
    }
    
    /** Empty Regular Expression */
    object Empty extends Operation0 { override val name = RegexEmpty }
    
    /** All characters Regular Expression */
    object AllChar extends Operation0 { override val name = RegexAllChar }
  }

  /**
    Following functions are under the --strings-exp option. They are under active refinement. Once they are stable, we will move them to the default mode. Please let us know when you have some suggestions.
  */
  object Experimental {
    /** String Contain. Arguments (s,t) where s and t are string terms. It returns true if the string s contains the string t. This function determines whether the string t can be found within the string s, returning true or false as appropriate. */
    object Contains extends Operation2 { override val name = StringContains }
    
    /** String IndexOf. Arguments (s, t, i) where s is a string, t is a non-empty string and i is a non-negative integer. This function returns the position of the first occurrence of the specified value t in the string s after the index i. It returns -1 if the value to search for never occurs. */
    object IndexOf extends Operation3 { override val name = StringIndexOf }
     
    /** String Replacement. Arguments (s, t1, t2) where s, t1 and t2 are string terms, t1 is non-empty. This function searches the string s for the specified value t1, and returns a new string where the first occurrence of the specified value t1 is replaced by the string t2. */
    object Replace extends Operation3 { override val name = StringReplace }
    
    /** String PrefixOf. Arguments (s, t) where s and t are string terms. It returns true if the string s is a prefix of the string t. */
    object PrefixOf extends Operation2 { override val name = StringPrefixOf }
    
    /** String SuffixOf. Arguments (s, t) where s and t are string terms. It returns true if the string s is a suffix of the string t. */
    object SuffixOf extends Operation2 { override val name = StringSuffixOf }
    
    /** String To Integer Conversion. Argument s where s is a string term. It returns the corresponding natural number if s is valid; otherwise, it returns -1. */
    object StringToInt extends Operation1 { override val name = StringStringToInt }
    
    /** Integer To String Conversion. Argument s where i is an integer term. It returns the corresponding string if i is a natural number; otherwise, it returns an empty string. */
    object IntToString extends Operation1 { override val name = StringIntToString }
  }
}
