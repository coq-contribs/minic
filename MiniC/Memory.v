Require Import List.
Require Import Dictionary.
Require Import Exceptions.
Require Import PrettyPrint.

Require Import BasicTypes.
Require Import CAbstractSyntax.

Set Implicit Arguments.
Unset Strict Implicit.

(***************************************************************************)
(* An ideal computer memory: an (unbounded) array of c_values indexed 
   by addresses.                                                           *)
(***************************************************************************)

Parameter memory : Set.

(* Functions to create, access and modify memories *)

Parameter memo_new : memory.
Parameter memo_access : memory -> address -> c_basicValue.
Parameter memo_store : memory -> address -> c_basicValue -> memory.

(* Axioms describing the expected behavior of the functions above *)

Axiom
  memoNeeDef :
    forall (v : c_value) (i : address), memo_access memo_new i = C_NoVal.

Axiom
  memoStoreDef1 :
    forall (t : memory) (v : c_basicValue) (i : address),
    memo_access (memo_store t i v) i = v.

Axiom
  memoStoreDef2 :
    forall (t : memory) (v : c_basicValue) (i j : address),
    i <> j -> memo_access (memo_store t i v) j = memo_access t j.

(******************************************************************)
(* Operations on memories                                         *)
(******************************************************************)

Section Copy_Block.
Variable memo : memory.
(* copies from adrs2 the block of length n starting at adrs1*)
Fixpoint memo_copy (n : nat) : address -> address -> memory :=
  fun adrs1 adrs2 =>
  match n with
  | O => memo
  | S m =>
      memo_store (memo_copy m (newAddress adrs1) (newAddress adrs2)) adrs1
        (memo_access memo adrs2)
  end.
End Copy_Block.
(******************************************************************)
Section Compare_Block.
Variable memo : memory.
(* compares the n cells starting from adrs1 against the n cells starting 
   from adrs2 *)
Fixpoint memo_comp (n : nat) : address -> address -> bool :=
  fun adrs1 adrs2 =>
  match n with
  | O => true
  | S m =>
      If (c_basicValueEq (memo_access memo adrs1) (memo_access memo adrs2))
      then (memo_comp m (newAddress adrs1) (newAddress adrs2)) else false
  end.
End Compare_Block.


(************************************************************************)
(*      The type of all the exceptions raisen by the C interpreter      *)
(************************************************************************)

Inductive c_dynError : Set :=
 (* Errors *)
  | MemoryFault : address -> c_dynError
  | IdentNotFound : c_ident -> c_dynError
  | TypeIdentNotFound : c_typeIdent -> c_dynError
  | ImpossibleCoercion : c_value -> c_predefType -> c_dynError
  | WrongType : c_value -> list c_predefType -> c_dynError
  | ShouldBeBasicType : c_value -> c_dynError
  | AccessPointer : c_value -> c_dynError
  | AccessArray : c_value -> c_dynError
  | AccessStruct : c_value -> c_dynError
  | BadProjection :
      c_value ->
      c_dynError
      (* The only exception to be caught up : raised by the return instruction *)
  | C_SkipOver : memory -> c_value -> c_dynError.

(************************************************************************)

(* An execution yields either something of type A or a dynamic error *)
Definition c_execution (A : Set) : Set := exc A c_dynError.
Definition eval (A : Set) (a : A) : c_execution A := excValue c_dynError a.

Definition memo_result : Set := c_execution c_value.
Definition dynError (e : c_dynError) : memo_result := excRaise c_value e.

(************************************************************************)
(************************************************************************)