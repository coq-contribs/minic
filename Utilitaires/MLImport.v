(* This file contains basic types imported from ML *)

Set Implicit Arguments.
Unset Strict Implicit.

Section Option.

Variable A : Set.

Inductive option : Set :=
  | None : option
  | Some : A -> option.

Coercion Local Some : A >-> option. 

End Option.
