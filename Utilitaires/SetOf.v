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


Require Import Relation_Operators.

Require Import PrettyPrint.
Require Import List.
Require Import ListDefs.
Require Export ListSet.

Set Implicit Arguments.
Unset Strict Implicit.

Section Finite_Sets.
Variable A B : Type.
Variable decA : forall x y : A, {x = y} + {x <> y}.
Variable decB : forall x y : B, {x = y} + {x <> y}.

Definition setOf (A : Type) : Type := set A.
Definition Member (x : A) (s : setOf A) : Prop := set_In x s.
Definition set_memDec (x : A) (s : setOf A) :
  {Member x s} + {~ Member x s} := set_In_dec decA x s.
Definition set_empty : setOf A := empty_set A.
Definition set_singleton (x : A) : setOf A := one x.
Lemma set_isEmpty : forall s : setOf A, {s = set_empty} + {s <> set_empty}.
intro s; case s; [ left; reflexivity | right; discriminate ].
Defined.

Definition set_image (f : A -> B) (s : setOf A) : setOf B := set_map decB f s.

Definition set_cardinal (s : setOf A) : nat := length s.
Definition set_fold (C : Type) (f : A -> C -> C) (s : setOf A) 
  (c : C) : C := fold_right f c s.

Definition Included (s1 s2 : setOf A) : Prop := incl s1 s2.
Hint Unfold Included: fsets.

Definition StIncluded (s1 s2 : setOf A) : Prop :=
  Included s1 s2 /\ ~ Included s2 s1.
Hint Unfold StIncluded: fsets.
Hint Unfold Member: fsets.

End Finite_Sets.

Section Union_On_Family.
Variable A B : Type.
Variable decB : forall x y : B, {x = y} + {x <> y}.
Definition set_imageUnion (f : A -> setOf B) (s : setOf A) : 
  setOf B := set_fold (fun x s => set_union decB (f x) s) s (set_empty B).
Definition set_mapUnion (f : A -> setOf B) (l : list A) : 
  setOf B := fold_right (fun x s => set_union decB (f x) s) (set_empty B) l.
End Union_On_Family.


Section Topological_Sort. 
(* Topological sort for a connected graph. *)

(* Nodes domain. *) 
Variable A : Set.

(* The finite set of nodes of the graph. *) 
Variable dom : setOf A.
(* Gives the neighborhood of each node *) 
Variable f : A -> setOf A.
Hypothesis
  fIsClosed :
    forall x : A,
    Member x dom -> forall y : A, Member y (f x) -> Member y dom.

(* The transitive closure of R is the pre-order *)
Definition OccursRelUp (x y : A) : Prop := Member x (f y).
Definition OccursRelDown (x y : A) : Prop := OccursRelUp y x.
Definition OccursRelUpT : A -> A -> Prop := clos_trans A OccursRelUp.
Definition OccursRelDownT : A -> A -> Prop := clos_trans A OccursRelDown.

(* Hummm.... this seems not to specify a PARTIAL order but a total one *)
Inductive IsSorted (R : A -> A -> Prop) : list A -> Prop :=
  | NilIsSorted : IsSorted R nil
  | OneIsSorted : forall x : A, IsSorted R (x :: nil)
  | ConsIsSorted :
      forall (x y : A) (l : list A),
      R x y -> IsSorted R (y :: l) -> IsSorted R (x :: y :: l).

Parameter topoSort : bool -> setOf A -> (A -> setOf A) -> list A.

Axiom
  topoSortSetIncludedInDom :
    forall (b : bool) (x : A), In x (topoSort b dom f) -> Member x dom.

Axiom topoSortUpIsSorted : IsSorted OccursRelUp (topoSort true dom f).

Axiom topoSortDownIsSorted : IsSorted OccursRelDown (topoSort false dom f).

Parameter transClosure : setOf A -> (A -> setOf A) -> list A -> list A.

Axiom
  transClosureSetIncludedInDom :
    forall (l : list A) (x : A),
    (forall y : A, In x l -> Member x dom) ->
    In x (transClosure dom f l) -> Member x dom.

Definition transClosureFrom (dom : setOf A) (f : A -> setOf A) 
  (x : A) : list A := transClosure dom f (set_singleton x).
End Topological_Sort. 
