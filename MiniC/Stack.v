Require Import List.
Require Import PrettyPrint.
Require Import Exceptions.
Require Import SimplDecl.

Set Implicit Arguments.
Unset Strict Implicit.

(**************************************************************************)
(* This file describes a polymorphic stack, used in the semantics of MiniC 
   to describe the temporary variables created during the execution of the 
   program                                                                *) 
(**************************************************************************)

Section Stack.

Variable Key : Set.
Variable Data : Set.
Variable eqKeyDec : forall x y : Key, {x = y} + {x <> y}.

(* A stack is a refinement of a simple declaration described in 
   the module SimlDecl.v *)

Definition stack : Set := sdecl Key Data.
Definition stack_empty : stack := sdecl_empty Key Data.
Definition stack_push (stk : stack) (k : Key) (d : Data) : stack :=
  sdecl_addShdw stk k d.
Definition stack_map (stk : stack) (k : Key) : exc Data Key :=
  sdecl_map eqKeyDec stk k.

(**************************************************************************)

(* Extra operation available for stacks: the last element with key k
   pushed can be pop up. *)

Fixpoint stack_pop (stk : stack) : Key -> stack :=
  fun k =>
  match stk with
  | nil => stack_empty
  | kv :: stk1 =>
      If (eqKeyDec (fst kv) k) then stk1 else (kv :: stack_pop stk1 k)
  end.

(**************************************************************************)

Definition stack_AssocValIs (m : stack) (k : Key) (d : Data) : Prop :=
  sdecl_AssocValIs eqKeyDec m k d.

Definition stack_IsDefined (m : stack) (k : Key) : Prop :=
  exists d : _, sdecl_AssocValIs eqKeyDec m k d.

End Stack.
(**************************************************************************)
(**************************************************************************)