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