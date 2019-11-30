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


Require Import ZArith.
Require Import Bool.
Require Import Exceptions.
Require Import PrettyPrint.

(*================================================================*)
(*   To be added to the file PolyList.v of Coq theories           *)
(*================================================================*)

Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.

Section ForAll_Properties.
Variable A B C D : Set.
Variable P : A -> Prop.
Variable R : A -> B -> Prop.
Variable T : A -> B -> C -> Prop.
Variable V : A -> B -> C -> D -> Prop.

Inductive ForAll : list A -> Prop :=
  | ForAllNil : ForAll nil
  | ForAllCons :
      forall x : A, P x -> forall l : list A, ForAll l -> ForAll (x :: l).

(* TODO: Define ForAlln in terms of ForAll, using currying and uncurrying *)
Inductive ForAll2 : list A -> list B -> Prop :=
  | ForAll2Nil : ForAll2 nil nil
  | ForAll2Cons :
      forall (x1 : A) (x2 : B),
      R x1 x2 ->
      forall (l1 : list A) (l2 : list B),
      ForAll2 l1 l2 -> ForAll2 (x1 :: l1) (x2 :: l2).

Inductive ForAll3 : list A -> list B -> list C -> Prop :=
  | ForAll3Nil : ForAll3 nil nil nil
  | ForAll3Cons :
      forall (x1 : A) (x2 : B) (x3 : C),
      T x1 x2 x3 ->
      forall (l1 : list A) (l2 : list B) (l3 : list C),
      ForAll3 l1 l2 l3 -> ForAll3 (x1 :: l1) (x2 :: l2) (x3 :: l3).

Inductive ForAll4 : list A -> list B -> list C -> list D -> Prop :=
  | ForAll4Nil : ForAll4 nil nil nil nil
  | ForAll4Cons :
      forall (x1 : A) (x2 : B) (x3 : C) (x4 : D),
      V x1 x2 x3 x4 ->
      forall (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
      ForAll4 l1 l2 l3 l4 ->
      ForAll4 (x1 :: l1) (x2 :: l2) (x3 :: l3) (x4 :: l4).

(*************************************************************************)
Variable Pl : list A -> Prop.
Inductive ForAllLeft : list A -> list A -> Prop :=
  | ForAllLeftNil : forall l : list A, ForAllLeft l nil
  | ForAllLeftCons :
      forall (l1 l2 : list A) (x : A),
      Pl l1 -> ForAllLeft (x :: l1) l2 -> ForAllLeft l1 (x :: l2).

(*************************************************************************)
Variable Pd : A -> list A -> Prop.

Inductive ForAllDep : list A -> Prop :=
  | ForAllDepNil : ForAllDep nil
  | ForAllDepCons :
      forall (x : A) (l : list A),
      Pd x l -> ForAllDep l -> ForAllDep (x :: l).
(*************************************************************************)

End ForAll_Properties.

Section Exists_Properties.
Variable A : Set.
Variable P : A -> Prop.
Inductive Exists : list A -> Prop :=
  | ExistsHere : forall x : A, P x -> forall l : list A, Exists (x :: l)
  | ExistsFurtherOn :
      forall (x : A) (l : list A), Exists l -> Exists (x :: l).

Variable decP : forall x : A, {P x} + {~ P x}.
Lemma existsDec : forall l : list A, {Exists l} + {~ Exists l}.
 simple induction l.
 right; red in |- *; intro abs; inversion abs.
 intros a l0 hypind; case (decP a).
 intro pa; left; apply ExistsHere; assumption.
 case hypind.
 intro el0; left; apply ExistsFurtherOn; assumption.
 intros notel0 notpa; right; red in |- *; intro abs; inversion abs.
 absurd (P a); assumption.
 absurd (Exists l0); assumption.
Qed.
End Exists_Properties.

Hint Resolve ForAllNil ForAllCons ExistsHere ExistsFurtherOn: Scade.

Section Decide_ForAll_And_Exists_Properties.
Variable A : Set.
Variable P : A -> Prop.
Variable decP : forall x : A, {P x} + {~ P x}.

Definition forAll (l : list A) : bool :=
  fold_right (fun a r => If (decP a) then r else false) true l.

Lemma forAllDec :
 forall l : list A, {ForAll (fun x => P x) l} + {Exists (fun x => ~ P x) l}.
simple induction l; intros.
auto with Scade.
case H; intros.
case (decP a); auto with Scade.
auto with Scade.
(*
Realizer forAll.
Repeat Program;Auto with Scade.
*)
Defined.
End Decide_ForAll_And_Exists_Properties.

Section Filter.
Variable A : Set.
Variable P : A -> Prop.
Variable p : A -> bool.

Fixpoint filter (l : list A) : list A :=
  match l with
  | nil => nil (A:=A)
  | a :: t => if p a then a :: filter t else filter t
  end.

Variable decP : forall x : A, {P x} + {~ P x}.
Fixpoint filterDec (l : list A) : list A :=
  match l with
  | nil => nil (A:=A)
  | a :: t => If (decP a) then (a :: filterDec t) else (filterDec t)
  end.
End Filter.

Section Fold_Left_i_Recursor.
Variable A B : Set.
Variable f : Z -> A -> B -> A.
Fixpoint fold_left_i (l : list B) : Z -> A -> A :=
  fun z a0 =>
  match l with
  | nil => a0
  | b :: t => fold_left_i t (z + 1)%Z (f z a0 b)
  end.
End Fold_Left_i_Recursor.

Section Search.
Variable A B : Set.
Variable exception : B.
Fixpoint search (n : nat) (l : list A) {struct l} : 
 exc A B :=
  match n, l with
  | O, nil => excRaise A exception
  | O, x :: l' => excValue B x
  | S m, nil => excRaise A exception
  | S m, x :: t => search m t
  end.
End Search.

Section Fold_Right_i_Recursor.
Variable A B : Set.
Variable f : Z -> B -> A -> A.
Variable a0 : A.
Fixpoint fold_right_i (l : list B) : Z -> A :=
  fun z =>
  match l with
  | nil => a0
  | b :: t => f z b (fold_right_i t (z + 1)%Z)
  end.
End Fold_Right_i_Recursor.

Section Map2.
Variable A B C : Set.
Variable f : A -> B -> C.
Fixpoint map2 (la : list A) : list B -> list C :=
  fun lb =>
  match la, lb with
  | nil, _ => nil (A:=C)
  | _, nil => nil (A:=C)
  | a :: la1, b :: lb1 => f a b :: map2 la1 lb1
  end.
End Map2.

Section Map3.
Variable A B C D : Set.
Variable f : A -> B -> C -> D.
Fixpoint map3 (la : list A) : list B -> list C -> list D :=
  fun lb lc =>
  match la, lb, lc with
  | nil, _, _ => nil (A:=D)
  | _, nil, _ => nil (A:=D)
  | _, _, nil => nil (A:=D)
  | a :: la1, b :: lb1, c :: lc1 => f a b c :: map3 la1 lb1 lc1
  end.
End Map3.

Section Sum_List.
Definition addList (l : list nat) : nat := fold_right plus 0 l.
End Sum_List.

Section Map_i.
Variable A B : Set.
Variable f : Z -> A -> B.
Fixpoint map_i (l : list A) : Z -> list B :=
  fun z =>
  match l with
  | nil => nil (A:=B)
  | a :: t => f z a :: map_i t (z + 1)%Z
  end.
End Map_i.

Section Map_with_Index.
Variable A B index : Set.
Variable baseIndex : index.
Variable newIndex : index -> index.
Variable f : index -> A -> B.
Fixpoint mapIndexFrom (l : list A) : index -> list B :=
  fun i =>
  match l with
  | nil => nil (A:=B)
  | a :: t => f i a :: mapIndexFrom t (newIndex i)
  end.
Definition mapIndex (l : list A) : list B := mapIndexFrom l baseIndex.
End Map_with_Index.



Section Tabulate.
Variable A : Set.
Variable new : A -> A.
Variable n : nat.

Fixpoint tabulate (n : nat) : A -> list A :=
  fun a =>
  match n with
  | O => nil (A:=A)
  | S m => a :: tabulate m (new a)
  end.

End Tabulate.

Section List_Zip.
Variable A B : Set.
Fixpoint zip (l1 : list A) : list B -> list (A * B) :=
  fun l2 =>
  match l1, l2 with
  | a :: lr1, b :: lr2 => (a, b) :: zip lr1 lr2
  | _, _ => nil (A:=A * B)
  end.
End List_Zip.

Section List_Equality.
Variable A : Set.
Variable eqA : forall x y : A, {x = y} + {x <> y}.
Lemma listEq : forall l1 l2 : list A, {l1 = l2} + {l1 <> l2}.
decide equality.
Qed.

Variable B : Set.
Variable f : A -> B -> bool.
Fixpoint listEqBool (l1 : list A) : list B -> bool :=
  fun l2 =>
  match l1, l2 with
  | nil, nil => true
  | t1 :: lt1, t2 :: lt2 => if f t1 t2 then listEqBool lt1 lt2 else false
  | _, _ => false
  end.
End List_Equality.

Section Singleton.
Variable A : Type.
Definition one (x : A) : list A := x :: nil. 
End Singleton.

Section Decide_Include.
Variable A : Set.
Variable eqA : forall x y : A, {x = y} + {x <> y}.

Definition inclDec : forall l1 l2 : list A, {incl l1 l2} + {~ incl l1 l2}.
fix inclDec 1; intros l1 l2.
  case l1.
   left; unfold incl in |- *; intros a abs; inversion abs.
    intros a l.
      case (In_dec eqA a l2).
        intros ain; case (inclDec l l2).
              intros H; left; apply incl_cons; auto.
              unfold incl in |- *; intro H; right; red in |- *; intro;
               apply H.
        intros; apply H0; simpl in |- *; auto.
    right; unfold incl in |- *; red in |- *; intro H;
     (apply n; apply H; simpl in |- *; auto).
Defined.
End Decide_Include.
Hint Resolve listEq: datatypes.

Section Iter.
Variable A B S : Set.
Variable f : A -> S -> B * S.

Definition list_modifState (a : A) (p : list B * S) : 
  list B * S := let (l1, s0) := p in let (x1, s1) := f a s0 in (x1 :: l1, s1).

Fixpoint list_visit (l : list A) : list B * S -> list B * S :=
  fun ds =>
  match l with
  | nil => ds
  | a :: l0 => list_modifState a (list_visit l0 ds)
  end.

Definition iter_right (d : list A) (s : S) : list B * S :=
  list_visit d (nil, s).

End Iter.

Section Map_And_Concat.
Variable A B : Set.
Definition mapAndConcatRight (f : A -> list B) (l : list A) : 
  list B := fold_right (fun x l1 => f x ++ l1) nil l.

Definition mapAndConcatLeft (f : A -> list B) (l : list A) : 
  list B := fold_left (fun l1 x => l1 ++ f x) l nil.
End Map_And_Concat.
