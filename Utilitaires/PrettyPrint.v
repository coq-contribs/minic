(* ============================================================================
 *        File: PrettyPrint.v
 *     Content: Concentre toutes les declarations de syntaxe comme
 *            : les fichiers ppml de CtCoq
 *   Directory: 
 *    Language: coq
 *      Author: Emmanuel LEDINOT
 *  Time-stamp: <98/11/09 13:39:07 el>
 *     Created:  98/10/01 06:32:02 el
 * ========================================================================= *)

(* ========================================================================= *)

Set Implicit Arguments.
Unset Strict Implicit.

Notation "'If' c1 'then' c2 'else' c3" :=
  match c1 with
  | left _ => c2
  | right _ => c3
  end (at level 1, c1, c2, c3 at level 9).
