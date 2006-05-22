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


Require Import Bool.
Require Export ZArith.
Require Import Peano_dec.

Require Import PrettyPrint.
Require Import SimplDecl.

Set Implicit Arguments.
Unset Strict Implicit.

(**************************************************************************)
(* This file contains the domain of interpretation for MiniC expressions  *)
(**************************************************************************)


(**************************************************************************)
(*             Basic types directly borrowed from Coq's library           *)
(**************************************************************************)

Definition c_boolVal := bool.
Definition c_boolEq : c_boolVal -> c_boolVal -> c_boolVal := eqb.
Definition c_boolDiseq (b1 b2 : c_boolVal) : c_boolVal := negb (eqb b1 b2).
Definition c_boolOr : c_boolVal -> c_boolVal -> c_boolVal := orb.
Definition c_boolAnd : c_boolVal -> c_boolVal -> c_boolVal := andb.
Definition c_boolXor : c_boolVal -> c_boolVal -> c_boolVal := xorb.
Definition c_boolNot : c_boolVal -> c_boolVal := negb.
Definition c_true : c_boolVal := true.
Definition c_false : c_boolVal := false.

(**************************************************************************)

(* Positive integers: necessary for the for(i=n;i>0;i--) instruction *)

Definition c_natVal := nat.
Definition c_natPlus : c_natVal -> c_natVal -> c_natVal := plus.
Definition c_natMinus : c_natVal -> c_natVal -> c_natVal := minus.
Definition c_natMult : c_natVal -> c_natVal -> c_natVal := mult.
Definition c_natEq : forall x y : c_natVal, {x = y} + {x <> y} := eq_nat_dec.
Definition c_natLt (n1 n2 : c_natVal) : c_boolVal :=
  If (le_lt_dec n1 n2) then c_false else c_true.
Definition c_natGt (n1 n2 : c_natVal) : c_boolVal :=
  If (le_gt_dec n1 n2) then c_false else c_true.
Definition c_natLe (n1 n2 : c_natVal) : c_boolVal :=
  If (le_gt_dec n1 n2) then c_true else c_false.
Definition c_natGe (n1 n2 : c_natVal) : c_boolVal :=
  If (le_ge_dec n1 n2) then c_true else c_false.

(**************************************************************************)

(*
Definition  c_intVal   := Z.
Definition  c_intPlus  : c_intVal -> c_intVal -> c_intVal := Zplus.
Definition  c_intMinus : c_intVal -> c_intVal -> c_intVal := Zminus.
Definition  c_intInv   : c_intVal -> c_intVal             := Zopp.
Definition  c_intMult  : c_intVal -> c_intVal -> c_intVal := Zmult.
Parameter c_intDiv   : c_intVal -> c_intVal -> c_intVal.
Parameter c_intMod   : c_intVal -> c_intVal -> c_intVal.
Parameter c_intPow   : c_intVal -> c_intVal -> c_intVal.
Definition  c_intEq    : (x,y:c_intVal){x=y}+{~x=y}        := Z_eq_dec.
Definition  c_intLt    : c_intVal -> c_intVal -> c_boolVal := Zlt_bool.
Definition  c_intGt    : c_intVal -> c_intVal -> c_boolVal := Zgt_bool.
Definition  c_intLe    : c_intVal -> c_intVal -> c_boolVal := Zle_bool.
Definition  c_intGe    : c_intVal -> c_intVal -> c_boolVal := Zge_bool.
*)

(**************************************************************************)
(*   Basic types axiomatized for the efficiency fo the MiniC interpreter  *)
(**************************************************************************)

(* Integers *)

Parameter c_intVal : Set.
Parameter c_intZero : c_intVal.
Parameter c_intSucc : c_intVal -> c_intVal.

Parameter c_intPlus : c_intVal -> c_intVal -> c_intVal.
Parameter c_intMinus : c_intVal -> c_intVal -> c_intVal.
Parameter c_intMns : c_intVal -> c_intVal.
Parameter c_intMult : c_intVal -> c_intVal -> c_intVal.

Parameter c_intDiv : c_intVal -> c_intVal -> c_intVal.
Parameter c_intMod : c_intVal -> c_intVal -> c_intVal.
Parameter c_intPow : c_intVal -> c_intVal -> c_intVal.

Parameter c_intEq : c_intVal -> c_intVal -> c_boolVal.
Parameter c_intDiseq : c_intVal -> c_intVal -> c_boolVal.
Parameter c_intLt : c_intVal -> c_intVal -> c_boolVal.
Parameter c_intGt : c_intVal -> c_intVal -> c_boolVal.
Parameter c_intLe : c_intVal -> c_intVal -> c_boolVal.
Parameter c_intGe : c_intVal -> c_intVal -> c_boolVal.

(**************************************************************************)

(* Reals *)

Parameter c_realVal : Set.
Parameter c_realPlus : c_realVal -> c_realVal -> c_realVal.
Parameter c_realMinus : c_realVal -> c_realVal -> c_realVal.
Parameter c_realMns : c_realVal -> c_realVal.
Parameter c_realMult : c_realVal -> c_realVal -> c_realVal.
Parameter c_realDiv : c_realVal -> c_realVal -> c_realVal.
Parameter c_realPow : c_realVal -> c_intVal -> c_realVal.
Parameter c_realEq : c_realVal -> c_realVal -> c_boolVal.
Parameter c_realDiseq : c_realVal -> c_realVal -> c_boolVal.
Parameter c_realLt : c_realVal -> c_realVal -> c_boolVal.
Parameter c_realGt : c_realVal -> c_realVal -> c_boolVal.
Parameter c_realLe : c_realVal -> c_realVal -> c_boolVal.
Parameter c_realGe : c_realVal -> c_realVal -> c_boolVal.
Parameter c_realOfInt : c_intVal -> c_realVal.
Parameter c_intOfReal : c_realVal -> c_intVal.

(**************************************************************************)

(* Characters *)

Parameter c_charVal : Set.
Parameter c_charEq : c_charVal -> c_charVal -> c_boolVal.
Parameter c_charDiseq : c_charVal -> c_charVal -> c_boolVal.
Parameter c_charLt : c_charVal -> c_charVal -> c_boolVal.
Parameter c_charGt : c_charVal -> c_charVal -> c_boolVal.
Parameter c_charLe : c_charVal -> c_charVal -> c_boolVal.
Parameter c_charGe : c_charVal -> c_charVal -> c_boolVal.

Parameter atoi : c_charVal -> c_intVal.
Parameter itoa : c_intVal -> c_charVal.

(**************************************************************************)

(* Memory addresses *)

Parameter address : Set.
Parameter baseAddress : address.
Parameter newAddress : address -> address.

(* jumps n positions from the address adrs *)
Fixpoint shiftToAddress (adrs : address) (n : nat) {struct n} : address :=
  match n with
  | O => adrs
  | S m => shiftToAddress (newAddress adrs) m
  end.

(**************************************************************************)
(**************************************************************************)

Parameter c_ident : Set.
Parameter c_identEq : forall x y : c_ident, {x = y} + {x <> y}.

Parameter c_typeIdent : Set.
Parameter c_typeIdentEq : forall x y : c_typeIdent, {x = y} + {x <> y}.

(**************************************************************************)
(*       The universe of values that a MiniC expression may denote        *)
(**************************************************************************)

Inductive c_basicValue : Set :=
  | C_InjBool : c_boolVal -> c_basicValue
  | C_InjNat : c_natVal -> c_basicValue
  | C_InjInt : c_intVal -> c_basicValue
  | C_InjReal : c_realVal -> c_basicValue
  | C_InjChar : c_charVal -> c_basicValue
  | C_InjAddress : address -> c_basicValue
                   (* stands for garbage in memory *)
  | C_NoVal : c_basicValue. 

Parameter c_basicValueEq : forall x y : c_basicValue, {x = y} + {x <> y}.


(* The structure of arrays and record types is preserved, so that 
   the translation of Lustre values into MiniC values is a injective 
   function *)
Inductive c_value : Set :=
  | C_ValBasic : c_basicValue -> c_value
  | C_ValTuple : list c_value -> c_value
  | C_ValStruct : sdecl c_ident c_value -> c_value.

(* Coercions and functions on the universe of values *)
Coercion C_InjBool : c_boolVal >-> c_basicValue.
Coercion C_InjInt : c_intVal >-> c_basicValue.
Coercion C_InjNat : c_natVal >-> c_basicValue.
Coercion C_InjReal : c_realVal >-> c_basicValue.
Coercion C_InjChar : c_charVal >-> c_basicValue.
Coercion C_InjAddress : address >-> c_basicValue.
Coercion C_ValBasic : c_basicValue >-> c_value.


Parameter c_valueEq : forall x y : c_value, {x = y} + {x <> y}.

(**************************************************************************)
(**************************************************************************)