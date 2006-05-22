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


(* Require Linear. *)
Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.

(* This file contains functions for deciding some property P, 
   that is, functions whose codomain is of the form {P}+{~P}. *)

(***************************************************************************)
Section Pair_Decidable.
Variable A B : Set.
Variable eqA : forall x y : A, {x = y} + {x <> y}.
Variable eqB : forall x y : B, {x = y} + {x <> y}.
Hint Resolve eqA eqB: Scade.
Lemma pairEqDec : forall x y : A * B, {x = y} + {x <> y}.
decide equality.
Qed.
End Pair_Decidable.
(***************************************************************************)
Lemma eq_bool_dec : forall b1 b2 : bool, {b1 = b2} + {b1 <> b2}.
decide equality.
Qed.
(***************************************************************************)

Hint Resolve pairEqDec: Scade.