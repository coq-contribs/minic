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


(* Axiomatisation of a hash table where the elements are ordered. *)

Require Import List.
Require Import ListDefs.
(* Require Extraction. *)
Require Import Exceptions.

Set Implicit Arguments.
Unset Strict Implicit.

Section Dictionary_Specification.

Variable Key : Set.
Variable keyEqDecide : forall k1 k2 : Key, {k1 = k2} + {k1 <> k2}.

Variable Data : Set.

Parameter dictionary : Set -> Set -> Set.

Notation dico := (dictionary Key Data) (only parsing).

Definition dico_result : Set := exc Data Key.
Definition dico_def (d : Data) : dico_result := Value Key d. 
Definition dico_unDef (k : Key) : dico_result := Error Data k. 
Coercion Local dico_def : Data >-> dico_result. 

Parameter dico_empty : dictionary Key Data.
Parameter
  dico_addShdw : dictionary Key Data -> Key -> Data -> dictionary Key Data.
Parameter dico_map : dictionary Key Data -> Key -> dico_result.
Parameter
  dico_union :
    dictionary Key Data -> dictionary Key Data -> dictionary Key Data.
Parameter dico_rmv : dictionary Key Data -> Key -> dictionary Key Data.
(* dico_toList should list the elements respecting a certain order! *)
Parameter dico_toList : dictionary Key Data -> list (Key * Data).
Parameter
  dico_filter :
    (Key -> Data -> bool) -> dictionary Key Data -> dictionary Key Data.

Axiom
  dico_AddShdw1 :
    forall (m : dictionary Key Data) (k : Key) (d : Data),
    dico_map (dico_addShdw m k d) k = d.

Axiom
  dico_AddShdw2 :
    forall (m : dictionary Key Data) (k1 k2 : Key) (d : Data),
    k1 <> k2 -> dico_map (dico_addShdw m k1 d) k2 = dico_map m k2.

Axiom dico_Empty : forall k : Key, dico_map dico_empty k = dico_unDef k.

Axiom
  dico_Remove :
    forall (m : dictionary Key Data) (k1 k2 : Key) (d : Data),
    k1 <> k2 -> dico_map (dico_rmv m k1) k2 = dico_map m k2.

Axiom
  dico_Filter :
    forall (p : Key -> Data -> bool) (m : dictionary Key Data),
    dico_toList (dico_filter p m) =
    filter (fun x => p (fst x) (snd x)) (dico_toList m).
 
Definition dico_AssocValIs (m : dictionary Key Data) 
  (k : Key) (d : Data) : Prop := dico_map m k = d.

Definition dico_IsDefined (m : dictionary Key Data) 
  (k : Key) : Prop := exists d : Data, dico_AssocValIs m k d.

Definition dico_decIsDefined :
  forall (m : dictionary Key Data) (k : Key),
  {dico_IsDefined m k} + {~ dico_IsDefined m k}.
intros m k.
unfold dico_IsDefined in |- *.
unfold dico_AssocValIs in |- *.
case (dico_map m k).
intro d; left; split with d; auto.
intro d; right; (red in |- *; intro abs); elim abs; (intros; discriminate).
Defined.


Axiom
  dico_AppIntro1 :
    forall (m1 m2 : dictionary Key Data) (k : Key) (d : Data),
    ~ dico_IsDefined m2 k ->
    dico_AssocValIs m1 k d -> dico_AssocValIs (dico_union m1 m2) k d.

Axiom
  dico_AppIntro2 :
    forall (m1 m2 : dictionary Key Data) (k : Key) (d : Data),
    dico_AssocValIs m2 k d -> dico_AssocValIs (dico_union m1 m2) k d.

Axiom
  dico_AppElim :
    forall (m1 m2 : dictionary Key Data) (k : Key) (d : Data),
    dico_AssocValIs (dico_union m1 m2) k d ->
    dico_AssocValIs m1 k d \/ dico_AssocValIs m2 k d.

Axiom
  dico_ToList1 :
    forall (m : dictionary Key Data) (k : Key) (d : Data),
    dico_AssocValIs m k d -> In (k, d) (dico_toList m).

Axiom
  dico_ToList2 :
    forall (m : dictionary Key Data) (k : Key) (d : Data),
    In (k, d) (dico_toList m) -> dico_AssocValIs m k d.

Definition dico_add (m : dictionary Key Data) (k : Key) 
  (d : Data) : dictionary Key Data :=
  try d = (dico_map m k) in m with x_ => (dico_addShdw m k d).

Definition dico_domain (d : dictionary Key Data) : 
  list Key := map (fun p => fst p) (dico_toList d).

Definition dico_codomain (d : dictionary Key Data) : 
  list Data := map (fun p => snd p) (dico_toList d).

Definition dico_fromList (l : list (Key * Data)) : 
  dictionary Key Data :=
  fold_right (fun p d => dico_addShdw d (fst p) (snd p)) dico_empty l.

(* Properties *)

Hint Unfold dico_IsDefined dico_AssocValIs: Scade.

Hint Resolve dico_AddShdw1 dico_AddShdw2 dico_Empty dico_ToList1 dico_ToList1
  dico_ToList2: Scade.


Lemma DeclaredEmpty : forall k : Key, ~ dico_IsDefined dico_empty k.
unfold dico_IsDefined in |- *.
red in |- *; intros k (d, H).
absurd (dico_AssocValIs dico_empty k d);
 [ unfold dico_AssocValIs in |- *; rewrite dico_Empty; discriminate
 | assumption ].
Defined.

Lemma DeclaredAdd1 :
 forall (m : dictionary Key Data) (k : Key) (d : Data),
 dico_IsDefined (dico_addShdw m k d) k.
intros m k d; exists d; auto with *.   	    
Defined.

Lemma DeclaredAdd2 :
 forall (m : dictionary Key Data) (k1 k2 : Key) (d : Data),
 dico_IsDefined m k1 -> k1 <> k2 -> dico_IsDefined (dico_addShdw m k2 d) k1.
unfold dico_IsDefined in |- *; unfold dico_AssocValIs in |- *;
 intros m k1 k2 d1 (d2, H) diseq; exists d2; rewrite <- H; 
 auto with *.
Defined.

Lemma DeclaredAdd3 :
 forall (m : dictionary Key Data) (k1 k2 : Key) (d : Data),
 dico_IsDefined (dico_addShdw m k2 d) k1 -> k1 = k2 \/ dico_IsDefined m k1.
unfold dico_IsDefined in |- *; unfold dico_AssocValIs in |- *.
intros m k1 k2.
case (keyEqDecide k1 k2); auto with *.
intros diseq d1 (d2, H); right; exists d2; rewrite <- H; symmetry  in |- *;
 auto with *.
Defined.

Lemma DeclaredAdd4 :
 forall (m : dictionary Key Data) (k1 k2 : Key) (d : Data),
 ~ dico_IsDefined (dico_addShdw m k2 d) k1 ->
 k1 <> k2 /\ ~ dico_IsDefined m k1.
unfold dico_IsDefined in |- *; unfold dico_AssocValIs in |- *.
intros m k1 k2 d Hi.
case (keyEqDecide k1 k2).
intro H; rewrite <- H in Hi.
absurd (dico_IsDefined (dico_addShdw m k1 d) k1); trivial.
apply DeclaredAdd1.
split; trivial. 
red in |- *; intros (d0, eqm); apply Hi.
exists d0; rewrite <- eqm; auto with *.
Defined.


Lemma declaredDecidable :
 forall (m : dictionary Key Data) (k : Key),
 {dico_IsDefined m k} + {~ dico_IsDefined m k}.

unfold dico_IsDefined in |- *; unfold dico_AssocValIs in |- *.
intros m k.
case (dico_map m k);
 [ intro d; left; exists d; auto with * | intro k1; right ].
red in |- *; intros (d, H); discriminate H.
Defined.

End Dictionary_Specification.

(* Morphisms on dictionaries *)


Section Dictionary_Iteration.
(*
Fixpoint dico_visit_right [l:(list (Key*Data))] :  S -> dico*S := 
 [s]Cases l of 
       nil             => (dico_empty,s)
    | (cons (k,x0) l0) =>
        let (d0,s0) = (dico_visit l0 s) in 
        let (x1,s1) = (f x0 s0)  
        in  ((dico_addShdw k x1),s1)
    end.
*)

Variable Key1 Key2 Data1 Data2 : Set.
Let dico11 := dictionary Key1 Data1.
Let dico12 := dictionary Key1 Data2.
Let dico22 := dictionary Key2 Data2.

Variable h1 : Key1 -> Key2.
Variable h2 : Data1 -> Data2.

Fixpoint dico_imageFromList12 (l : list (Key1 * Data1)) : dico12 :=
  match l with
  | nil => dico_empty Key1 Data2
  | p :: l0 =>
      let (k, x) := p in dico_addShdw (dico_imageFromList12 l0) k (h2 x)
  end.
Fixpoint dico_imageFromList22 (l : list (Key1 * Data1)) : dico22 :=
  match l with
  | nil => dico_empty Key2 Data2
  | p :: l0 =>
      let (k, x) := p in dico_addShdw (dico_imageFromList22 l0) (h1 k) (h2 x)
  end.

Definition dico_image (d1 : dico11) : dico12 :=
  dico_imageFromList12 (dico_toList d1).

Definition dico_image2 (d1 : dico11) : dico22 :=
  dico_imageFromList22 (dico_toList d1).

Variable S : Set.
Variable f : Data1 -> S -> Data2 * S.

Definition modif (p : Key1 * Data1) (ds0 : dico12 * S) : 
  dico12 * S :=
  let (d, s0) := ds0 in
  let (k, x0) := p in let (x1, s1) := f x0 s0 in (dico_addShdw d k x1, s1).

Fixpoint dico_visit (l : list (Key1 * Data1)) : dico12 * S -> dico12 * S :=
  fun ds =>
  match l with
  | nil => ds
  | p :: l0 => modif p (dico_visit l0 ds)
  end.

Definition dico_iter_right (d : dico11) (s : S) : dico12 * S :=
  dico_visit (dico_toList d) (dico_empty Key1 Data2, s).

Variable g : Key1 -> Data1 -> S -> S.
Definition dico_fold_left (d : dico11) (s : S) : S :=
  fold_left (fun (s : S) (p : Key1 * Data1) => let (k, d) := p in g k d s)
    (dico_toList d) s.

Definition dico_fold_right (d : dico11) (s : S) : S :=
  fold_right (fun (p : Key1 * Data1) (s : S) => let (k, d) := p in g k d s) s
    (dico_toList d).

End Dictionary_Iteration.



(*
Extract Constant  dictionary   => "Dico.t".
Extract Constant  dico_empty   => "Dico.empty".
Extract Constant  dico_addShdw => "Dico.addShdw".
Extract Constant  dico_map     => "Dico.map".
Extract Constant  dico_toList  => "Dico.toList".
*)
