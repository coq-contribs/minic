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


(* Simple association lists (one key for data).  It is an open
   extension of Dictionary.v implemented with associating lists.
   The order of the elements in the list IS relevant (for the 
   operations sdecl_fold).

   We assume that there is only one pair for each key in the
   association list. This is not controlled by the constructor
   operation addShdw, but a predicate enables to state this
   assumption.

   
*)

Require Export List.
Require Import ListDefs.
Require Import PrettyPrint.
Require Export Exceptions.

Set Implicit Arguments.
Unset Strict Implicit.

Section Simple_Declaration_Environment.

Variable Key : Set.
Variable eqKeyDec : forall x y : Key, {x = y} + {x <> y}.
Hint Resolve eqKeyDec: Scade.

Variable Data : Set.
Variable eqDataDec : forall x y : Data, {x = y} + {x <> y}.
Hint Resolve eqDataDec: Scade.

Definition sdecl := list (Key * Data).

Definition sdecl_empty : sdecl := nil.

Fixpoint sdecl_map (m : sdecl) : Key -> exc Data Key :=
  fun k =>
  match m with
  | nil => excRaise Data k
  | (k1, v1) :: l1 =>
      If (eqKeyDec k k1) then (excValue Key v1) else (sdecl_map l1 k)
  end.

(* Gets the data and the list of keys associated to a key k *)
Fixpoint sdecl_mapk (m : sdecl) : Key -> exc (Key * Data) Key :=
  fun k =>
  match m with
  | nil => excRaise (Key * Data) k
  | (k1, v1) :: l1 =>
      If (eqKeyDec k k1) then (excValue Key (k1, v1)) else (sdecl_mapk l1 k)
  end.

Definition sdecl_add (m : sdecl) (k : Key) (d : Data) : sdecl :=
  try v = (sdecl_map m k) in m with k1 => ((k, d) :: m).

Definition sdecl_addShdw (m : sdecl) (k : Key) (d : Data) : sdecl :=
  (k, d) :: m.

Definition sdecl_union (m1 m2 : sdecl) : sdecl :=
  fold_right (fun p d => sdecl_add d (fst p) (snd p)) m2 m1.

Definition sdecl_app (m1 m2 : sdecl) : sdecl :=
  fold_right (fun p d => sdecl_addShdw d (fst p) (snd p)) m2 m1.

Section Have_Entry.

Definition SndEqual (d : Data) (p : Key * Data) := snd p = d.
Lemma sndEqualDec :
 forall (d : Data) (p : Key * Data), {SndEqual d p} + {~ SndEqual d p}.
intros d p; case (eqDataDec (snd p) d); auto.
Qed.

Definition HaveEntry (m : sdecl) (d : Data) : Prop := Exists (SndEqual d) m.

Definition sdecl_haveEntry (m : sdecl) (d : Data) :
  {HaveEntry m d} + {~ HaveEntry m d} := existsDec (sndEqualDec d) m.
End Have_Entry.

Definition sdecl_zip (lk : list Key) (ld : list Data) : sdecl :=
  map2 (fun (x : Key) (y : Data) => (x, y)) lk ld.

Section Sdecl_Filter.
Variable p : Key -> Data -> bool.
Definition sdecl_filter (m : sdecl) : sdecl :=
  filter (fun x => p (fst x) (snd x)) m.
End Sdecl_Filter.

Fixpoint sdecl_chng (m : sdecl) : Key -> Data -> exc sdecl Key :=
  fun k d =>
  match m with
  | nil => excRaise sdecl k
  | kd :: m1 =>
      If (eqKeyDec (fst kd) k) then (excValue Key ((k, d) :: m))
      else try m : _ = (sdecl_chng m1 k d) in (excValue Key (kd :: m))
  end.

Fixpoint sdecl_rmv (m : sdecl) : Key -> sdecl :=
  fun k =>
  match m with
  | nil => sdecl_empty
  | kd :: m1 =>
      If (eqKeyDec (fst kd) k) then (sdecl_rmv m1 k)
      else (sdecl_add (sdecl_rmv m1 k) (fst kd) (snd kd))
  end.

Definition sdecl_toList (m : sdecl) : list (Key * Data) := m.
Definition sdecl_fromList (l : list (Key * Data)) : sdecl := l.

(* Warning: needs to check that the sdecl does not have multiple
   entries.
Definition sdecl_AssocValIs : sdecl -> Key -> Data -> Prop := 
  [m][k][d](In (k,d) m).
*)

Definition sdecl_AssocValIs (m : sdecl) (k : Key) (d : Data) : Prop :=
  sdecl_map m k = Value Key d.

Definition sdecl_IsDefined (m : sdecl) (k : Key) : Prop :=
  exists d : Data, sdecl_AssocValIs m k d.

Definition sdecl_domain (sd : sdecl) : list Key :=
  map (fun p : Key * Data => fst p) sd.

Definition sdecl_codomain (sd : sdecl) : list Data :=
  map (fun p : Key * Data => snd p) sd.

Theorem sdecl_mapkSpec :
 forall (m : sdecl) (k : Key),
 {lkd : Key * Data | k = fst lkd /\ sdecl_AssocValIs m k (snd lkd)} +
 {k1 : Key | k = k1 /\ ~ sdecl_IsDefined m k1}.
intros m k0; elim m; intros.
right; exists k0; split; auto.
unfold sdecl_IsDefined, sdecl_AssocValIs in |- *.
red in |- *; intros (d, H); discriminate H.
case a; clear a; intros k1 b.
case (eqKeyDec k0 k1); intro.
left; exists (k0, b).
split; auto.
unfold sdecl_AssocValIs in |- *; simpl in |- *.
case (eqKeyDec k0 k1).
auto.
intros; absurd (k0 = k1); assumption.
case H; intros (a', (H1, H2)).
left; exists a'; split; auto.
unfold sdecl_IsDefined, sdecl_AssocValIs in |- *.
simpl in |- *.
case (eqKeyDec k0 k1); intro; auto.
intros; absurd (k0 = k1); assumption.
right; exists k0; split; auto.
unfold sdecl_IsDefined, sdecl_AssocValIs in |- *.
red in |- *; simpl in |- *.
case (eqKeyDec k0 k1); intro.
intros; absurd (k0 = k1); assumption.
intro; apply H2; rewrite <- H1; assumption.
Defined.

Section Well_Formed.
Variable P : Key -> Data -> Prop.
(* There are no multiple entries in the association list *)
Inductive sdecl_WellFormed : sdecl -> Prop :=
  | sdecl_WellFormedNil : sdecl_WellFormed sdecl_empty
  | sdecl_WellFormedCons :
      forall (x : Key) (d : Data) (m : sdecl),
      P x d ->
      ~ sdecl_IsDefined m x ->
      sdecl_WellFormed m -> sdecl_WellFormed (sdecl_addShdw m x d).
End Well_Formed.

End Simple_Declaration_Environment.

Section Iteration_On_Simple_Blocks_Of_Declarations.

Variable Key1 Key2 Data1 Data2 : Set.
Variable eqKey1Dec : forall x y : Key1, {x = y} + {x <> y}.

Let dico1 := sdecl Key1 Data1.
Let dico2 := sdecl Key1 Data2.

Variable h11 : Key1 -> Key2.
Variable h12 : Data1 -> Data2.
Variable h22 : Key1 -> Data1 -> Data2.

(* Only transforms the data *)
Fixpoint sdecl_image (l : dico1) : dico2 :=
  match l with
  | nil => sdecl_empty Key1 Data2
  | p :: l0 => let (k, x) := p in sdecl_addShdw (sdecl_image l0) k (h12 x)
  end.

(* Transfroms both key and data *)
Let dico22 := sdecl Key2 Data2.
Fixpoint sdecl_image2 (l : dico1) : dico22 :=
  match l with
  | nil => sdecl_empty Key2 Data2
  | p :: l0 =>
      let (k, x) := p in sdecl_addShdw (sdecl_image2 l0) (h11 k) (h22 k x)
  end.

(* Performing a transformation with side effects *)
Variable S : Set.
Variable f : Data1 -> S -> Data2 * S.

Definition sdecl_modifState (p : Key1 * Data1) (ds0 : dico2 * S) :
  dico2 * S :=
  let (d, s0) := ds0 in
  let (k, x0) := p in let (x1, s1) := f x0 s0 in (sdecl_addShdw d k x1, s1).

Fixpoint sdecl_visit (l : dico1) : dico2 * S -> dico2 * S :=
  fun ds =>
  match l with
  | nil => ds
  | p :: l0 => sdecl_modifState p (sdecl_visit l0 ds)
  end.

Definition sdecl_iter_right (d : dico1) (s : S) : dico2 * S :=
  sdecl_visit d (sdecl_empty Key1 Data2, s).


(*************************************************)

Variable g : Key1 -> Data1 -> S -> S.
Definition sdecl_fold_left (d : dico1) (s : S) : S :=
  fold_left (fun (s : S) (p : Key1 * Data1) => let (k, d) := p in g k d s) d
    s.
Definition sdecl_fold_right (d : dico1) (s : S) : S :=
  fold_right (fun (p : Key1 * Data1) (s : S) => let (k, d) := p in g k d s) s
    d.

End Iteration_On_Simple_Blocks_Of_Declarations.

Section Generic_Predicates.
Variable Key1 Key2 : Set.
Variable Data1 Data2 : Set.

Variable P1 : Key1 -> Data1 -> Prop.
Variable P2 : Key1 -> Key2 -> Data1 -> Data2 -> Prop.

Definition ForAllEntry (env1 : sdecl Key1 Data1) : Prop :=
  ForAll (fun p1 : Key1 * Data1 => P1 (fst p1) (snd p1)) env1.

Definition ForAllEntry2 (env1 : sdecl Key1 Data1) (env2 : sdecl Key2 Data2) :
  Prop :=
  ForAll2
    (fun (p1 : Key1 * Data1) (p2 : Key2 * Data2) =>
     let (k1, d1) := p1 in let (k2, d2) := p2 in P2 k1 k2 d1 d2) env1 env2.

End Generic_Predicates.

Section Remapping_Values.
Variable Key1 : Set.
Variable Data1 : Set.
Variable eqKey1Dec : forall x y : Key1, {x = y} + {x <> y}.
Let dico1 := sdecl Key1 Data1.
Definition sdecl_remap (s : dico1) (k : Key1) (d : Data1) : dico1 :=
  sdecl_image2 (fun x => x) (fun k1 d1 => If (eqKey1Dec k k1) then d else d1)
    s.
End Remapping_Values.
