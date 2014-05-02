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


(* Blocks of association lists (several keys are packed for the same data).
   It follows the specification of Dictionary.v 

   We assume that there is only one pair for each key in the
   association list. This is not controlled by the constructor
   operations, but a predicate enables to state this assumption.   
*)

Require Export List.
Require Import ListDefs.
Require Import PrettyPrint.
Require Import Exceptions.


Set Implicit Arguments.
Unset Strict Implicit.

Section Block_Of_Variables_Declaration.

Variable Key : Set.
Variable eqKeyDec : forall x y : Key, {x = y} + {x <> y}.
Variable Data : Set.
Notation castedKeyList := (list Key * Data)%type (only parsing).

Definition bdecl := list (list Key * Data).

Definition bdecl_empty : bdecl := nil.

Definition bdecl_addone (m : bdecl) (k : Key) (d : Data) : bdecl :=
  (k :: nil, d) :: m.


(* Gets the data associated to a key k *)
Fixpoint bdecl_map (m : bdecl) : Key -> exc Data Key :=
  fun k =>
  match m with
  | nil => excRaise Data k
  | (kl, v1) :: l1 =>
      If (In_dec eqKeyDec k kl) then (excValue Key v1) else (bdecl_map l1 k)
  end.

(* Gets the data and the list of keys associated to a key k *)
Fixpoint bdecl_mapk (m : bdecl) : Key -> exc (list Key * Data) Key :=
  fun k =>
  match m with
  | nil => excRaise (list Key * Data) k
  | (kl, v1) :: l1 =>
      If (In_dec eqKeyDec k kl) then (excValue Key (kl, v1))
      else (bdecl_mapk l1 k)
  end.

(* Auxiliary: 
   gets the data and the list of keys associated to a list of keys k *)
Fixpoint bdecl_mapl (m : bdecl) :
 list Key -> exc (list Key * Data) (list Key) :=
  fun k =>
  match m with
  | nil => excRaise (list Key * Data) k
  | (kl, v1) :: l1 =>
      If (listEq eqKeyDec k kl) then (excValue (list Key) (kl, v1))
      else (bdecl_mapl l1 k)
  end.

(* Adds a new entry if it is not already in the list *)
Definition bdecl_add (m : bdecl) (k : list Key) (d : Data) : bdecl :=
  try v = (bdecl_mapl m k) in m with k1 => ((k, d) :: m).

(* Auxiliary *) 
   Fixpoint bdecl_semiMap (m : bdecl) :
    list Key -> exc (list Key * Data) (list Key) :=
     fun k =>
     match m with
     | nil => excRaise (list Key * Data) k
     | (kl, v1) :: l1 =>
         If (inclDec eqKeyDec k kl) then (excValue (list Key) (kl, v1))
         else (bdecl_semiMap l1 k)
     end.
(* Adds a two new lists of entries k1 and k2 if k1 it is not already
   in the list. *)
Definition bdecl_addJoin (m : bdecl) (k1 k2 : list Key) 
  (d : Data) : bdecl :=
  try v = (bdecl_semiMap m k1) in m with k1 =>
  (let newk := k1 ++ k2 in (newk, d) :: m).


Definition bdecl_addShdw (m : bdecl) (k : list Key) 
  (d : Data) : bdecl := (k, d) :: m.

Definition bdecl_union (m1 m2 : bdecl) : bdecl :=
  fold_right (fun (p : list Key * Data) d => bdecl_add d (fst p) (snd p)) m2 m1.



Section Bdecl_Filter.
Variable p : list Key -> Data -> bool.
Definition bdecl_filter (m : bdecl) : bdecl :=
  filter (fun x : list Key * Data => p (fst x) (snd x)) m.
End Bdecl_Filter.

Definition bdecl_toList (m : bdecl) : list (Key * Data) :=
  fold_right (fun (kld : list Key * Data) l => map (fun k => (k, snd kld)) (fst kld) ++ l) nil m.

Definition bdecl_toLists (m : bdecl) : list (list Key * Data) := m.

Definition bdecl_domain (m : bdecl) : list Key :=
  fold_right (fun kld l => fst kld ++ l) nil m.

Definition bdecl_codomain (m : bdecl) : list Data :=
  map (fun p : list Key * Data => snd p) m.

(*
Section Iterate_On_Data.
Variable f : Data -> Data.
Definition bdecl_image : bdecl -> bdecl :=
 [m](map [p:(list Key)*Data]let (x,y) = p in (x,(f y))  m).
End Iterate_On_Data.
*)

Definition bdecl_AssocValIs (m : bdecl) (k : Key) (d : Data) : Prop :=
  exists lk : list Key, In k lk /\ In (lk, d) m.

Definition bdecl_IsDefined (m : bdecl) (k : Key) : Prop :=
  exists d : Data, bdecl_AssocValIs m k d.

Theorem bdecl_mapkSpec :
 forall (m : bdecl) (k : Key),
 {lkd : list Key * Data | In k (fst lkd) /\ In (fst lkd, snd lkd) m} +
 {k1 : Key | k = k1 /\ ~ bdecl_IsDefined m k1}.
intros m k; elim m.
right; exists k; split; auto.
unfold bdecl_IsDefined, bdecl_AssocValIs in |- *; red in |- *;
 intros (d, (lk, (H1, H2))); auto.
intros (lk, d) lm H.
case (In_dec eqKeyDec k lk); intro.
left; exists (lk, d); split; simpl in |- *; intros; auto.
case H.
intros (lkd, (H1, H2)).
left; exists lkd; split; simpl in |- *; auto.
intros (k1, (H1, H2)).
right; exists k; split; auto.
rewrite H1; red in |- *; intro.
apply H2; inversion H0.
inversion H3.
case H4; clear H4; intros H5 H6.
red in |- *.
exists x; red in |- *.
exists x0; split; auto.
simpl in H6.
case H6; clear H6; intros; trivial.
case n.
rewrite H1.
replace lk with x0; trivial.
injection H4; auto.
Defined.

Definition bdecl_decIsDefined :
  forall (m : bdecl) (k : Key),
  {bdecl_IsDefined m k} + {~ bdecl_IsDefined m k}.
intros m k.
unfold bdecl_IsDefined in |- *; unfold bdecl_AssocValIs in |- *.
case (bdecl_mapkSpec m k).
intros ((lk, d), (H1, H2)); eauto with datatypes.
unfold bdecl_IsDefined in |- *; unfold bdecl_AssocValIs in |- *;
 intros (k1, (eqk1, H)); rewrite eqk1; auto with datatypes.
Defined.


Section Well_Formed.
Variable P : bdecl -> Data -> Prop.

Definition NotRepeated : list Key -> Prop := ForAllDep (fun x l => ~ In x l).

Inductive bdecl_WellFormed : bdecl -> Prop :=
  | bdecl_WellFormedNil : bdecl_WellFormed bdecl_empty
  | bdecl_WellFormedCons :
      forall (x : list Key) (d : Data) (m : bdecl),
      P m d ->
      x <> nil ->
      NotRepeated x ->
      ForAll (fun k => ~ bdecl_IsDefined m k) x ->
      bdecl_WellFormed (bdecl_add m x d).

End Well_Formed.

End Block_Of_Variables_Declaration.

Section Iteration_On_Blocks_Of_Declarations.

Variable Key Data1 Data2 : Set.
Variable eqKeyDec : forall x y : Key, {x = y} + {x <> y}.
Let dico1 := bdecl Key Data1.
Let dico2 := bdecl Key Data2.

Variable h : Data1 -> Data2.

Fixpoint bdecl_image (l : dico1) : dico2 :=
  match l with
  | nil => bdecl_empty Key Data2
  | p :: l0 => let (k, x) := p in bdecl_addShdw (bdecl_image l0) k (h x)
  end.

Variable S : Set.
Variable f : Data1 -> S -> Data2 * S.

Definition bdecl_modifState (p : list Key * Data1) 
  (ds0 : dico2 * S) : dico2 * S :=
  let (d, s0) := ds0 in
  let (k, x0) := p in let (x1, s1) := f x0 s0 in (bdecl_addShdw d k x1, s1).

Fixpoint bdecl_visit (l : dico1) : dico2 * S -> dico2 * S :=
  fun ds =>
  match l with
  | nil => ds
  | p :: l0 => bdecl_modifState p (bdecl_visit l0 ds)
  end.

Definition bdecl_iter_right (d : dico1) (s : S) : dico2 * S :=
  bdecl_visit d (bdecl_empty Key Data2, s).

Variable g : list Key -> Data1 -> S -> S.
Definition bdecl_fold_left (d : dico1) (s : S) : S :=
  fold_left
    (fun (s : S) (p : list Key * Data1) => let (k, d) := p in g k d s) d s.
Definition bdecl_fold_right (d : dico1) (s : S) : S :=
  fold_right
    (fun (p : list Key * Data1) (s : S) => let (k, d) := p in g k d s) s d.

End Iteration_On_Blocks_Of_Declarations.

