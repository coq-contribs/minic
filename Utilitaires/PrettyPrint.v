(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


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
