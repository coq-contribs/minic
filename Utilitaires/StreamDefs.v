(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA        LRI-CNRS        ENS-CNRS                *)
(*              Rocquencourt         Orsay          Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.2                                 *)
(*                               May 1st 1998                               *)
(*                                                                          *)
(****************************************************************************)
(*                                Streams.v                                 *)
(****************************************************************************)

(* -------------------------------------------------------------------------*)
(*          Modified because of name clashes on map and ForAll              *)
(*                      with their list counterpart                         *)
(* -------------------------------------------------------------------------*)

Require Import TheoryList.

Set Implicit Arguments.
Unset Strict Implicit.

Section Streams. (* The set of streams : definition *)

Variable A : Set.

CoInductive Stream : Set :=
    Cons : A -> Stream -> Stream.


Definition hd (x : Stream) := match x with
                              | Cons a _ => a
                              end.

Definition tl (x : Stream) := match x with
                              | Cons _ s => s
                              end.


Fixpoint Str_nth_tl (n : nat) : Stream -> Stream :=
  fun s : Stream => match n with
                    | O => s
                    | S m => Str_nth_tl m (tl s)
                    end.

Definition Str_nth (n : nat) (s : Stream) : A := hd (Str_nth_tl n s).


Lemma unfold_Stream :
 forall x : Stream, x = match x with
                        | Cons a s => Cons a s
                        end. 
Proof.
  intro x.
  case x.
  trivial.
Qed.

Lemma tl_nth_tl :
 forall (n : nat) (s : Stream), tl (Str_nth_tl n s) = Str_nth_tl n (tl s).
Proof.
  simple induction n; simpl in |- *; auto.
Qed.
Hint Resolve tl_nth_tl: datatypes v62.

Lemma Str_nth_tl_plus :
 forall (n m : nat) (s : Stream),
 Str_nth_tl n (Str_nth_tl m s) = Str_nth_tl (n + m) s.
simple induction n; simpl in |- *; intros; auto with datatypes.
rewrite <- H.
rewrite tl_nth_tl; trivial with datatypes.
Qed.

Lemma Str_nth_plus :
 forall (n m : nat) (s : Stream),
 Str_nth n (Str_nth_tl m s) = Str_nth (n + m) s.
intros; unfold Str_nth in |- *; rewrite Str_nth_tl_plus;
 trivial with datatypes.
Qed.

(* Extensional Equality between two streams  *)

CoInductive EqSt : Stream -> Stream -> Prop :=
    eqst :
      forall s1 s2 : Stream,
      hd s1 = hd s2 -> EqSt (tl s1) (tl s2) -> EqSt s1 s2.

(* A coinduction principle *)

Ltac coinduction proof :=
  cofix proof;
   (intros; (constructor; [ clear proof | try (apply proof; clear proof) ])).


(* Extensional equality is an equivalence relation *)


Theorem EqSt_reflex : forall s : Stream, EqSt s s.
coinduction ipattern:EqSt_reflex.
reflexivity.
Qed.

Theorem sym_EqSt : forall s1 s2 : Stream, EqSt s1 s2 -> EqSt s2 s1.
coinduction ipattern:Eq_sym.
case H; intros; symmetry  in |- *; assumption.
case H; intros; assumption.
Qed.


Theorem trans_EqSt :
 forall s1 s2 s3 : Stream, EqSt s1 s2 -> EqSt s2 s3 -> EqSt s1 s3.
coinduction ipattern:Eq_trans.
transitivity (hd s2).
case H; intros; assumption.
case H0; intros; assumption.
apply (Eq_trans (tl s1) (tl s2) (tl s3)).
case H; trivial with datatypes.
case H0; trivial with datatypes.
Qed.

(* 
The definition given is equivalent to require the elements at each position to be equal 
*)

Theorem eqst_ntheq :
 forall (n : nat) (s1 s2 : Stream), EqSt s1 s2 -> Str_nth n s1 = Str_nth n s2.
unfold Str_nth in |- *; simple induction n.
intros s1 s2 H; case H; trivial with datatypes.
intros m hypind.
simpl in |- *.
intros s1 s2 H.
apply hypind.
case H; trivial with datatypes.
Qed.

Theorem ntheq_eqst :
 forall s1 s2 : Stream,
 (forall n : nat, Str_nth n s1 = Str_nth n s2) -> EqSt s1 s2.
coinduction ipattern:Equiv2.
apply (H 0).
intros n; apply (H (S n)).
Qed.

Section Stream_Properties.

Variable P : Stream -> Prop.

Inductive Exists : Stream -> Prop :=
  | Here : forall x : Stream, P x -> Exists x
  | Further : forall x : Stream, ~ P x -> Exists (tl x) -> Exists x.

CoInductive ForAllS : Stream -> Prop :=
    forallS : forall x : Stream, P x -> ForAllS (tl x) -> ForAllS x.

End Stream_Properties.

End Streams.

Section Map.

Variable A B C : Set.
Variable f : A -> B.

CoFixpoint mapStr  : Stream A -> Stream B :=
  fun s : Stream A => Cons (f (hd s)) (mapStr (tl s)).

Variable g : A -> B -> C.

CoFixpoint mapStr2  : Stream A -> Stream B -> Stream C :=
  fun sa sb => Cons (g (hd sa) (hd sb)) (mapStr2 (tl sa) (tl sb)).

End Map.


Section Others.

Variable A B C : Set.
Variable a : A.

CoInductive ForAllStr (P : A -> Prop) : Stream A -> Prop :=
    DefForAllStr :
      forall sa : Stream A,
      P (hd sa) -> ForAllStr P (tl sa) -> ForAllStr P sa.

CoInductive ForAllStr2 (P : A -> B -> Prop) : Stream A -> Stream B -> Prop :=
    DefForAllStr2 :
      forall (sa : Stream A) (sb : Stream B),
      P (hd sa) (hd sb) -> ForAllStr2 P (tl sa) (tl sb) -> ForAllStr2 P sa sb.

CoFixpoint l_ListOfStr2StrOfLists  : list (Stream A) -> Stream (list A) :=
  fun ls =>
  let lh := map (fun s : Stream A => hd s) ls in
  let ltl := map (fun s : Stream A => tl s) ls in
  Cons lh (l_ListOfStr2StrOfLists ltl).

(* A REVOIR *)
Parameter
  l_streamOfLists2ListOfStreams :
    A -> nat -> Stream (list A) -> list (Stream A).


Fixpoint mapCons (lh : list A) : list (Stream A) -> list (Stream A) :=
  fun ltls =>
  match lh, ltls with
  | nil, _ => nil (A:=Stream A)
  | h :: tlh, nil => nil (A:=Stream A)
  | h :: tlh, htls :: tltls =>
      let hs := Cons h htls in let tls := mapCons tlh tltls in hs :: tls
  end.
End Others.

Section Extend_Some_Function_Pointwise.
Variable A B C D : Set.
Variable f : A -> B.
Variable g : A -> B -> C.
Variable h : A -> B -> C -> D.
Variable k : list A -> A.

CoFixpoint extend  : Stream A -> Stream B :=
  fun s => Cons (f (hd s)) (extend (tl s)).

CoFixpoint extend2  : Stream A -> Stream B -> Stream C :=
  fun s1 s2 => Cons (g (hd s1) (hd s2)) (extend2 (tl s1) (tl s2)).

CoFixpoint extend3  : Stream A -> Stream B -> Stream C -> Stream D :=
  fun s1 s2 s3 =>
  Cons (h (hd s1) (hd s2) (hd s3)) (extend3 (tl s1) (tl s2) (tl s3)).

CoFixpoint extendNTo1  : list (Stream A) -> Stream A :=
  fun lsv =>
  let heads := map (fun x => hd x) lsv in
  let tails := map (fun x => tl x) lsv in Cons (k heads) (extendNTo1 tails).

End Extend_Some_Function_Pointwise.


Section Extend_Some_Relationship_Pointwise.
Variable A B C : Set.
Variable R1 : A -> Prop.
Variable R2 : A -> B -> Prop.
Variable R3 : A -> B -> C -> Prop.

CoInductive Extend1 : Stream A -> Prop :=
    ExtendCons1 :
      forall s1 : Stream A, R1 (hd s1) -> Extend1 (tl s1) -> Extend1 s1.

CoInductive Extend2 : Stream A -> Stream B -> Prop :=
    ExtendCons2 :
      forall (s1 : Stream A) (s2 : Stream B),
      R2 (hd s1) (hd s2) -> Extend2 (tl s1) (tl s2) -> Extend2 s1 s2.

CoInductive Extend3 : Stream A -> Stream B -> Stream C -> Prop :=
    ExtendCons3 :
      forall (s1 : Stream A) (s2 : Stream B) (s3 : Stream C),
      R3 (hd s1) (hd s2) (hd s3) ->
      Extend3 (tl s1) (tl s2) (tl s3) -> Extend3 s1 s2 s3.

End Extend_Some_Relationship_Pointwise.
 
Section Extend_Some_Dependent_Relationship_Pointwise.
Variable A B C : Set.
Variable R : A -> A -> Prop.

CoInductive ExtendFrom : A -> Stream A -> Prop :=
    ExtendFromCons :
      forall (a : A) (s1 : Stream A),
      R a (hd s1) -> ExtendFrom (hd s1) (tl s1) -> ExtendFrom a s1.
End Extend_Some_Dependent_Relationship_Pointwise.

Set Strict Implicit.
Unset Implicit Arguments.

(* $Id$ *)

