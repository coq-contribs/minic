Require Import ZArith.
Require Import List.
Require Import Bool.

Require Import PrettyPrint.
Require Import MLImport.
Require Import ListDefs.
Require Import StreamDefs.
Require Import Exceptions.
Require Import BasicTypes.
Require Import SimplDecl.
Require Import CAbstractSyntax.

Require Import Memory.
Require Import Stack.
Require Import State.

Set Implicit Arguments.
Unset Strict Implicit.

(*********************************************************************)
(* This file containst the denotational semantics of MiniC.          *)
(*********************************************************************)


(*********************************************************************)
(* Auxiliary functions                                               *)
(*********************************************************************)
Section I_Iteration_Recursor.
Variable A : Set.
Variable f : nat -> A -> A.
Variable a : A.
Fixpoint iterate (n : nat) : A :=
  match n with
  | O => a
  | S m => f m (iterate m)
  end.
End I_Iteration_Recursor.


(*********************************************************************)
(*                     Denotation of Types                           *)
(*********************************************************************)

(* The denotation of a type is a type in normal form, where all type
   variables are expanded by their definitions. Types definitions are
   supposed to be ordered with respect to the occurrence relationship.
   Otherwise the interpreter will fail (ie, no denotation for the
   program).  *)

(**************************************************************************)

Section Denotation_Of_Binds.
Variable denc_type : c_type -> domc_type.
(* Normalizaes the types in the bindings of a structured type *)
Definition denc_binds (binds : sdecl c_ident c_type) :
  c_execution (sdecl c_ident n_type) :=
  sdecl_fold_right
    (fun id t r =>
     try env : _ = r
     in try nt : _ = (denc_type t) in (eval (sdecl_addShdw env id nt))) binds
    (eval (sdecl_empty c_ident n_type)).
End Denotation_Of_Binds.

Section Denotation_Of_Types.
Variable envTyp : sdecl c_typeIdent n_type.

(* Normalizes the type t *)
Fixpoint denc_type (t : c_type) : domc_type :=
  match t with
  | C_Void => eval N_Void
  | C_DefType id =>
      try nt = (sdecl_map c_typeIdentEq envTyp id) in 
      (eval nt) with err => (excRaise n_type (TypeIdentNotFound id))
  | C_PrimType pt => eval (N_PrimType pt)
  | C_Pointer t => try nt : _ = (denc_type t) in (eval (N_Pointer nt))
  | C_Array n t => try nt : _ = (denc_type t) in (eval (N_Array n nt))
  | C_Struct binds =>
      try nbinds : _ = (denc_binds denc_type binds)
      in (eval (N_Struct nbinds))
  end.
End Denotation_Of_Types.

(* Normalizes all the types in type definitions *)
Definition denc_typeDefs (decl : c_typeDefs) : domc_typeDefs :=
  sdecl_fold_right
    (fun id ty r =>
     try env : _ = r
     in try nt : _ = (denc_type env ty) in (eval (sdecl_addShdw env id nt)))
    decl (eval (sdecl_empty c_typeIdent n_type)).



(****************************************************************************)
(*             Denotation of MiniC Static Variable Envrionment              *)
(****************************************************************************)

Section Memory_Allocation.

(* Declaration denotes allocation in the memory. Memory allocation
   depends on the size of the object to be allocated, that is
   determined by its type. This is why an environment of sizes for the
   defined types is necessary.  *)

Variable typEnv : sdecl c_typeIdent n_type.

(***************************************************************************)
(* Allocates a static variables of the program *)
(* Allocates sizeof(t) cells and associates the initial address of
   this block to the variable id.  *)
Definition allocateStatic (st : state) (id : c_ident) 
  (ty : n_type) (v : c_basicValue) : state :=
  let nbcells := sizeOfType ty in
  match st with
  | MkState memo maxi sv dv =>
      let startsAt := newAddress maxi in
      MkState memo (shiftToAddress maxi nbcells)
        (sdecl_addShdw sv id (C_VarObj startsAt ty)) dv
  end.


(* The denotation of the variable declarations is a function
   producing the initial state of the machie, where all the static
   variables of the program are allocated in the memory. All the 
   allocated memory cells contain garbage. *)

Definition denc_varDecls (gbd : c_varDecls) : c_execution state :=
  sdecl_fold_left
    (fun id (obj : c_varDecl) r =>
     try st : _ = r
     in match obj with
        | C_MkVarDecl t =>
            try nt : _ = (denc_type typEnv t)
            in (eval (allocateStatic st id nt C_NoVal))
        end) gbd (eval emptyState).


(****************************************************************************)
(*             Denotation of MiniC Temporary Variable Envrionment           *)
(****************************************************************************)

(*****************************************************************************)
(* Allocates a temporary variable of the program in the stack of the machine *)

Definition allocateDynamic (id : c_ident) (ty : n_type) 
  (v : c_value) (st : state) : state :=
  let nbcells := sizeOfType ty in
  match st with
  | MkState memo maxi sv dv =>
      let startsAt := newAddress maxi in
      MkState (storeMemoBlock memo startsAt v) (shiftToAddress maxi nbcells)
        sv (stack_push dv id (C_VarObj startsAt ty))
  end.

(* Allocates the input variables of a function *)
Definition allocateParams (l : list (c_ident * n_type * c_value))
  (st : state) : state :=
  fold_right
    (fun (p : c_ident * n_type * c_value) r =>
     match p with
     | ((id, ty), v) => allocateDynamic id ty v r
     end) st l.

(* Allocates the local variables of a function *)
Definition allocateLocalVars (gbd : sdecl c_ident n_type) 
  (st : state) : state :=
  sdecl_fold_left (fun id t st => allocateDynamic id t C_NoVal st) gbd st.


(****************************************************************************)
Section Denotation_Of_Expressions_And_Statements.
(****************************************************************************)

(* Environment with the executable code for the already compiled functions *)
Variable denc_f : sdecl c_ident domc_funDecl.

(****************************************************************************)
(*                   Denotation of Unary Expressions                        *)
(****************************************************************************)

(* Auxiliary unary morphisms on bool and type values *)

(****************************************************************************)
Definition univBoolUnMorph (f : c_boolVal -> c_boolVal) 
  (v : memo_result) : memo_result :=
  try x : _ = v
  in match x with
     | C_ValBasic (C_InjBool b) => eval (C_ValBasic (C_InjBool (f b)))
     | x => dynError (WrongType x (one C_bool))
     end.
(****************************************************************************)
Definition univIntUnMorph (f : c_intVal -> c_intVal) 
  (v1 : memo_result) : memo_result :=
  try x1 : _ = v1
  in match x1 with
     | C_ValBasic (C_InjInt n1) => eval (C_ValBasic (C_InjInt (f n1)))
     | x => dynError (WrongType x (one C_int))
     end.
(****************************************************************************)
Definition coerceType (t : c_predefType) (v1 : memo_result) : memo_result :=
  try x1 : _ = v1
  in match t, x1 with
     | C_int, C_ValBasic (C_InjReal r1) =>
         eval (C_ValBasic (C_InjInt (c_intOfReal r1)))
     | C_real, C_ValBasic (C_InjInt n1) =>
         eval (C_ValBasic (C_InjReal (c_realOfInt n1)))
     | t, x1 => dynError (ImpossibleCoercion x1 t)
     end.
(****************************************************************************)

Section Unary_Applications.
Variable denc_exp : c_exp -> state -> domc_exp.

Definition unApp (m : state) (op : c_unOp) (e1 : c_exp) : domc_exp :=
  try mv1 : _ = (denc_exp e1 m)
  in (let m1 := stateOfExpValue mv1 in
      let v1 := valueOfExpValue mv1 in
      match op with
      | C_Not =>
          try v : _ = (univBoolUnMorph c_boolNot (eval v1))
          in (eval (MkExpValue m1 v))
      | C_Mns =>
          try v : _ = (univIntUnMorph c_intMns (eval v1))
          in (eval (MkExpValue m1 v))
      | C_Cast t =>
          try v : _ = (coerceType t (eval v1)) in (eval (MkExpValue m1 v))
      end).  
End Unary_Applications.

(****************************************************************************)
(*                   Denotation of Binary Expressions                       *)
(****************************************************************************)

(* Auxiliary binary morphisms for each type *)

(*****************************************************************************)
Definition univBinMorph (f : domc_univ -> domc_univ -> domc_univ)
  (v1 v2 : memo_result) : memo_result :=
  try x1 : _ = v1 in try x2 : _ = v2 in (eval (f x1 x2)).
(*****************************************************************************)
Definition univBoolBinMorph (f : c_boolVal -> c_boolVal -> c_boolVal)
  (v1 v2 : memo_result) : memo_result :=
  try x1 : _ = v1
  in try x2 : _ = v2
     in match x1, x2 with
        | C_ValBasic (C_InjBool b1), C_ValBasic (C_InjBool b2) =>
            eval (C_ValBasic (C_InjBool (f b1 b2)))
        | C_ValBasic C_NoVal, _ => eval (C_ValBasic C_NoVal)
        | _, C_ValBasic C_NoVal => eval (C_ValBasic C_NoVal)
        | x, y => dynError (WrongType x (one C_bool))
        end.
(*****************************************************************************)
Definition univIntBinMorph (f : c_intVal -> c_intVal -> c_intVal)
  (v1 v2 : memo_result) : memo_result :=
  try x1 : _ = v1
  in try x2 : _ = v2
     in match x1, x2 with
        | C_ValBasic (C_InjInt n1), C_ValBasic (C_InjInt n2) =>
            eval (C_ValBasic (C_InjInt (f n1 n2)))
        | C_ValBasic C_NoVal, _ => eval (C_ValBasic C_NoVal)
        | _, C_ValBasic C_NoVal => eval (C_ValBasic C_NoVal)
        | x, y => dynError (WrongType x (one C_int))
        end.
(*****************************************************************************)
Definition univNatBinMorph (f : c_natVal -> c_natVal -> c_natVal)
  (v1 v2 : memo_result) : memo_result :=
  try x1 : _ = v1
  in try x2 : _ = v2
     in match x1, x2 with
        | C_ValBasic (C_InjNat n1), C_ValBasic (C_InjNat n2) =>
            eval (C_ValBasic (C_InjNat (f n1 n2)))
        | C_ValBasic C_NoVal, _ => eval (C_ValBasic C_NoVal)
        | _, C_ValBasic C_NoVal => eval (C_ValBasic C_NoVal)
        | x, y => dynError (WrongType x (one C_nat))
        end.
(*****************************************************************************)
Definition univArithBinMorph (f1 : c_natVal -> c_natVal -> c_natVal)
  (f2 : c_intVal -> c_intVal -> c_intVal)
  (f3 : c_realVal -> c_realVal -> c_realVal) (v1 v2 : memo_result) :
  memo_result :=
  try x1 : _ = v1
  in try x2 : _ = v2
     in match x1, x2 with
        | C_ValBasic (C_InjNat n1), C_ValBasic (C_InjNat n2) =>
            eval (C_ValBasic (C_InjNat (f1 n1 n2)))
        | C_ValBasic (C_InjInt z1), C_ValBasic (C_InjInt z2) =>
            eval (C_ValBasic (C_InjInt (f2 z1 z2)))
        | C_ValBasic (C_InjReal r1), C_ValBasic (C_InjReal r2) =>
            eval (C_ValBasic (C_InjReal (f3 r1 r2)))
        | C_ValBasic C_NoVal, _ => eval (C_ValBasic C_NoVal)
        | _, C_ValBasic C_NoVal => eval (C_ValBasic C_NoVal)
        | x, y => dynError (WrongType x (C_int :: C_nat :: one C_real))
        end.
(*****************************************************************************)
Definition univArithCompareMorph (f1 : c_natVal -> c_natVal -> c_boolVal)
  (f2 : c_intVal -> c_intVal -> c_boolVal)
  (f3 : c_realVal -> c_realVal -> c_boolVal) (v1 v2 : memo_result) :
  memo_result :=
  try x1 : _ = v1
  in try x2 : _ = v2
     in match x1, x2 with
        | C_ValBasic (C_InjNat n1), C_ValBasic (C_InjNat n2) =>
            eval (C_ValBasic (C_InjBool (f1 n1 n2)))
        | C_ValBasic (C_InjInt z1), C_ValBasic (C_InjInt z2) =>
            eval (C_ValBasic (C_InjBool (f2 z1 z2)))
        | C_ValBasic (C_InjReal r1), C_ValBasic (C_InjReal r2) =>
            eval (C_ValBasic (C_InjBool (f3 r1 r2)))
        | C_ValBasic C_NoVal, _ => eval (C_ValBasic C_NoVal)
        | _, C_ValBasic C_NoVal => eval (C_ValBasic C_NoVal)
        | x, y => dynError (WrongType x (C_int :: C_nat :: one C_real))
        end.
(*****************************************************************************)
Definition irArithBinMorph (f2 : c_intVal -> c_intVal -> c_intVal)
  (f3 : c_realVal -> c_realVal -> c_realVal) (v1 v2 : memo_result) :
  memo_result :=
  try x1 : _ = v1
  in try x2 : _ = v2
     in match x1, x2 with
        | C_ValBasic (C_InjInt z1), C_ValBasic (C_InjInt z2) =>
            eval (C_ValBasic (C_InjInt (f2 z1 z2)))
        | C_ValBasic (C_InjReal r1), C_ValBasic (C_InjReal r2) =>
            eval (C_ValBasic (C_InjReal (f3 r1 r2)))
        | C_ValBasic C_NoVal, _ => eval (C_ValBasic C_NoVal)
        | _, C_ValBasic C_NoVal => eval (C_ValBasic C_NoVal)
        | x, y => dynError (WrongType x (C_int :: C_nat :: one C_real))
        end.
(******************************************************************)
Definition powerMorph (v1 v2 : memo_result) : memo_result :=
  try x1 : _ = v1
  in try x2 : _ = v2
     in match x1, x2 with
        | C_ValBasic (C_InjInt z1), C_ValBasic (C_InjInt z2) =>
            eval (C_ValBasic (C_InjInt (c_intPow z1 z2)))
        | C_ValBasic (C_InjReal r1), C_ValBasic (C_InjInt z2) =>
            eval (C_ValBasic (C_InjReal (c_realPow r1 z2)))
        | C_ValBasic C_NoVal, _ => eval (C_ValBasic C_NoVal)
        | _, C_ValBasic C_NoVal => eval (C_ValBasic C_NoVal)
        | x, y => dynError (WrongType x (C_int :: one C_real))
        end.
(******************************************************************)
(* A special case: the lazy operator \&\& of C                      *)
Definition lazyAnd (v1 v2 : memo_result) : memo_result :=
  try x1 : _ = v1
  in try x2 : _ = v2
     in match x1 with
        | C_ValBasic (C_InjBool b1) =>
            if b1
            then
             match x2 with
             | C_ValBasic (C_InjBool b2) => eval (C_ValBasic (C_InjBool b2))
             | C_ValBasic C_NoVal => eval (C_ValBasic C_NoVal)
             | _ => dynError (WrongType x2 (one C_bool))
             end
            else eval (C_ValBasic (C_InjBool false))
        | C_ValBasic C_NoVal => eval (C_ValBasic C_NoVal)
        | _ => dynError (WrongType x1 (one C_bool))
        end.
(******************************************************************)
(* Comparison of structured values is not allowed: use CompMem    *)

Definition eqMorph (v1 v2 : memo_result) : memo_result :=
  try x1 : _ = v1
  in try x2 : _ = v2
     in match x1, x2 with
        | C_ValBasic bv1, C_ValBasic bv2 =>
            If (c_basicValueEq bv1 bv2)
            then (eval (C_ValBasic (C_InjBool true)))
            else (eval (C_ValBasic (C_InjBool false)))
        | _, _ =>
            dynError (WrongType x1 (C_int :: C_real :: C_char :: one C_bool))
        end.
(******************************************************************)
Definition compareMemo (memo : memory) (n : nat) (v1 v2 : memo_result) :
  memo_result :=
  try x1 : _ = v1
  in try x2 : _ = v2
     in match x1, x2 with
        | C_ValBasic (C_InjAddress adrs1), C_ValBasic (C_InjAddress adrs2) =>
            if memo_comp memo n adrs1 adrs2
            then eval (C_ValBasic (C_InjBool true))
            else eval (C_ValBasic (C_InjBool false))
        | x, y => dynError (WrongType x (one C_bool))
        end.
(******************************************************************)

Section Binary_Application.
Variable denc_exp : c_exp -> state -> domc_exp.
(* Computs the denotation of a binary expression *)
Definition binApp (st : state) (op : c_binOp) (e1 e2 : c_exp) : domc_exp :=
  try mv1 : _ = (denc_exp e1 st)
  in (let st1 := stateOfExpValue mv1 in
      let v1 := valueOfExpValue mv1 in
      try mv2 : _ = (denc_exp e2 st1)
      in (let st2 := stateOfExpValue mv2 in
          let v2 := valueOfExpValue mv2 in
          match op with
          | C_Equal =>
              try v : _ = (eqMorph (eval v1) (eval v2))
              in (eval (MkExpValue st2 v))
          | C_Lt =>
              try v : _ =
              (univArithCompareMorph c_natLt c_intLt c_realLt 
                 (eval v1) (eval v2)) in (eval (MkExpValue st2 v))
          | C_Gt =>
              try v : _ =
              (univArithCompareMorph c_natGt c_intGt c_realGt 
                 (eval v1) (eval v2)) in (eval (MkExpValue st2 v))
          | C_Le =>
              try v : _ =
              (univArithCompareMorph c_natLe c_intLe c_realLe 
                 (eval v1) (eval v2)) in (eval (MkExpValue st2 v))
          | C_Ge =>
              try v : _ =
              (univArithCompareMorph c_natGe c_intGe c_realGe 
                 (eval v1) (eval v2)) in (eval (MkExpValue st2 v))
          | C_And =>
              try v : _ = (univBoolBinMorph c_boolAnd (eval v1) (eval v2))
              in (eval (MkExpValue st2 v))
          | C_AndAnd =>
              try v : _ = (lazyAnd (eval v1) (eval v2))
              in (eval (MkExpValue st2 v))
          | C_Or =>
              try v : _ = (univBoolBinMorph c_boolOr (eval v1) (eval v2))
              in (eval (MkExpValue st2 v))
          | C_Xor =>
              try v : _ = (univBoolBinMorph c_boolXor (eval v1) (eval v2))
              in (eval (MkExpValue st2 v))
          | C_Plus =>
              try v : _ =
              (univArithBinMorph c_natPlus c_intPlus c_realPlus 
                 (eval v1) (eval v2)) in (eval (MkExpValue st2 v))
          | C_Mult =>
              try v : _ =
              (univArithBinMorph c_natMult c_intMult c_realMult 
                 (eval v1) (eval v2)) in (eval (MkExpValue st2 v))
          | C_Minus =>
              try v : _ =
              (univArithBinMorph c_natMinus c_intMinus c_realMinus 
                 (eval v1) (eval v2)) in (eval (MkExpValue st2 v))
          | C_Power =>
              try v : _ = (powerMorph (eval v1) (eval v2))
              in (eval (MkExpValue st2 v))
          | C_Div =>
              try v : _ =
              (irArithBinMorph c_intDiv c_realDiv (eval v1) (eval v2))
              in (eval (MkExpValue st2 v))
          | C_Mod =>
              try v : _ = (univIntBinMorph c_intMod (eval v1) (eval v2))
              in (eval (MkExpValue st2 v))
          | C_CompMem t =>
              try nt : _ = (denc_type typEnv t)
              in (let n := sizeOfType nt in
                  let memo := memoOfState st2 in
                  try v : _ = (compareMemo memo n (eval v1) (eval v2))
                  in (eval (MkExpValue st2 v)))
          end)).
End Binary_Application.

(******************************************************************)

Definition denc_expList (denc_exp : c_exp -> state -> domc_exp) 
  (st : state) (le : list c_exp) : c_execution (state * list c_value) :=
  fold_right
    (fun e (pe : c_execution (state * list c_value)) =>
     try p : (state * list c_value) = pe
     in try ev2 : _ = (denc_exp e (fst p))
        in (let st2 := stateOfExpValue ev2 in
            let v2 := valueOfExpValue ev2 in eval (st2, v2 :: snd p)))
    (eval (st, nil)) le.

(***********************************************************************)
(*              Denotation of MiniC Assignable Expressions             *)
(***********************************************************************)

(* Denotation of assignable expressions *)

Section Denotation_Of_Assignable_Expressions.
Variable denc_exp : c_exp -> state -> domc_exp.

(**************************************************************************)
(* Computes the length of the jump to be done in order to access to
   the position x of a structure. *)
Section Sum_Size.
Variable x : c_ident.
Fixpoint sumSizeRec (binds : list (c_ident * n_type)) : 
 nat -> nat :=
  fun n =>
  match binds with
  | nil => n
  | (id, t) :: l =>
      If (c_identEq id x) then n else (sumSizeRec l (n + sizeOfType t))
  end.
Definition sumSizeUpTo (binds : list (c_ident * n_type)) : nat :=
  sumSizeRec binds 0.
End Sum_Size.
(**************************************************************************)

(* Computes the address, the typ and the stored value of an assignable 
   expression, plus the new current state produced by its evaluation. 

   TODO: for efficiency reasons, this function should not compute the
   value of the expression, just the address and the type; and then
   directly read the object from the memory.  Also, shiftToAddress should
   be directly implemented in Ocaml to avoid being linear on the size of 
   the jump. *)

Fixpoint denc_assgnExp (ae : c_assgnExp) : state -> domc_assgnExp :=
  fun s0 =>
  match ae with
  | C_Var id =>
      try nty : _ = (typeOfVarInState s0 id)
      in try addrs : _ = (addressOfVar s0 id)
         in try val = (segmentOfVar s0 id)
            in (eval (MkAssgnExpValue s0 addrs nty val)) with err =>
            (excRaise c_assgnExpValue (IdentNotFound id))
  | C_Refer ae1 =>
      try r : c_assgnExpValue = (denc_assgnExp ae1 s0)
      in (let (s1, ae1addrs, ae1ty, ae1val) := r in
          match ae1val, ae1ty with
          
              (* The value of ae1 must denote an address pointing to an object of type nty1*)
              | C_ValBasic (C_InjAddress addrs), N_Pointer nty1 =>
              let memo := memoOfState s1 in
              let val := readMemoBlock memo nty1 addrs in
              eval (MkAssgnExpValue s1 addrs nty1 val)
          | _, _ => excRaise c_assgnExpValue (BadProjection ae1val)
          end)
  | C_ArrayPos ae1 e =>
      try sv1
      : _ 
      (* The expression e must denote a positive integer *)
       
      (* jump n objects of size nty1 *)
       = (denc_exp e s0)
      in (let s1 := stateOfExpValue sv1 in
          let v1 := valueOfExpValue sv1 in
          match v1 with
          | C_ValBasic (C_InjNat n) =>
              try r : c_assgnExpValue = (denc_assgnExp ae1 s1)
              in (let (s2, ae1addrs, ae1ty, ae1val) := r in
                  match ae1val, ae1ty with
                  | C_ValTuple lv, N_Array m nty1 =>
                      let jumpsize := sizeOfType nty1 * n in
                      let memo := memoOfState s2 in
                      let addrs := shiftToAddress ae1addrs jumpsize in
                      let subv := readMemoBlock memo nty1 addrs in
                      eval (MkAssgnExpValue s2 addrs nty1 subv)
                  | _, _ => excRaise c_assgnExpValue (BadProjection ae1val)
                  end)
          | _ => excRaise c_assgnExpValue (AccessArray v1)
          end)
  | C_StructPos ae1 x =>
      try r : c_assgnExpValue = (denc_assgnExp ae1 s0)
      in (let (s1, ae1addrs, ae1ty, ae1val) := r in
          match ae1val, ae1ty with
          | C_ValStruct vbinds, N_Struct tybinds => 
              (* jump all the objects preceeding x *)
              let jumpsize := sumSizeUpTo x tybinds in
              let addrs := shiftToAddress ae1addrs jumpsize in
              let memo := memoOfState s1 in
              try nty1 = (sdecl_map c_identEq tybinds x)
              in (let subv := readMemoBlock memo nty1 addrs in
                  eval (MkAssgnExpValue s1 addrs nty1 subv)) with err =>
              (excRaise c_assgnExpValue (IdentNotFound x))
          | _, _ => excRaise c_assgnExpValue (BadProjection ae1val)
          end)
  end. 

End Denotation_Of_Assignable_Expressions.

(**************************************************************************)
(*               Denotation of MiniC Expressions                          *)
(**************************************************************************)

Fixpoint denc_exp (e : c_exp) : state -> domc_exp :=
  fun st =>
  match e with
  | C_AssgnInj ae =>
      try aev : _ = (denc_assgnExp denc_exp ae st)
      in (let (s1, adrs, nty, v) := aev in eval (MkExpValue s1 v))
  | C_Derefer ae =>
      try aev : _ = (denc_assgnExp denc_exp ae st)
      in (let (s1, adrs, _, _) := aev in
          eval (MkExpValue s1 (C_InjAddress adrs)))
  | C_Val v => eval (MkExpValue st (C_ValBasic v))
  | C_UnApp op e1 => unApp denc_exp st op e1
  | C_BinApp op e1 e2 => binApp denc_exp st op e1 e2
  | C_FunCall f realargs =>
      (* The components of the state before evaluating the function call *) 
      let maxi := maxPosition st in
      let stck := lVarsOfState st in
      let gbv := gVarsOfState st in 
      (* Look for the function code *)
      try funblock = (sdecl_map c_identEq denc_f f)
      in (let funParams := domc_paramOfFunDecl funblock in
          let funBody := domc_bodyOfFunDecl funblock in
          let funlocv := domc_localVarsOfFunDecl funblock in
          (* Evaluate the arguments of the function call *)
          try p : (state * list c_value) =
          (denc_expList denc_exp st realargs)
          in (let (st1, rlva) := p in
              (* Allocate the cells on the stack for the input and local variables *)
              let pshl := zip funParams rlva in
              let st2 := allocateParams pshl st1 in
              let st3 :=
                allocateLocalVars funlocv st2
                (* Evaluate the function body *)
                 in
              try news = (funBody st3)
              in (let fnlst := MkState (memoOfState news) maxi gbv stck in
                  eval (MkExpValue fnlst (C_ValBasic C_NoVal))) with ex =>
              match ex with
               
                  (* The function raised a return value: catch it *)
                  | C_SkipOver m v =>
                  let fnlst := MkState m maxi gbv stck in
                  eval (MkExpValue fnlst v)
              | x => excRaise c_expValue x
              end)) with x_ => (excRaise c_expValue (IdentNotFound f))
  end.

(********************************************************************)
(*               Denotation of MiniC instructions                   *)
(********************************************************************)

(* Auxiliary functions *)

(********************************************************************)

Definition denc_seq (denc_statement : c_statement -> domc_statement)
  (s1 s2 : c_statement) : domc_statement :=
  fun m : state =>
  try m1 : _ = (denc_statement s1 m) in (denc_statement s2 m1).

(********************************************************************)

Section Switch_Semantics.
Variable denc_statement : c_statement -> domc_statement.
Variable cond : c_value.
Variable default : c_statement.
Fixpoint denc_switch (branches : list (c_intVal * c_statement)) :
 domc_statement :=
  fun st =>
  match branches with
  | nil => denc_statement default st
  | (l, s) :: br1 =>
      If (c_valueEq cond (C_InjInt l)) then (denc_statement s st)
      else (denc_switch br1 st)
  end.
End Switch_Semantics.

(* Denotation of an assignment *)

(********************************************************************)

Definition copyMemo (n : nat) (v1 v2 : c_value) : domc_statement :=
  fun st =>
  match v1, v2 with
  | C_ValBasic (C_InjAddress adrs1), C_ValBasic (C_InjAddress adrs2) =>
      match st with
      | MkState memo maxi sv dv =>
          eval
            (MkState (memo_copy (memoOfState st) n adrs1 adrs2) maxi sv dv)
      end 
      (* Bad error message: there is no primitive type for addresses ... *)
  | x, y => excRaise state (WrongType x nil)
  end.

(********************************************************************)

Definition forBody (denc_statement : c_statement -> domc_statement)
  (i : c_assgnExp) (body : c_statement) (n : c_natVal)
  (m : c_execution state) : c_execution state :=
  try m1 : _ = m
  in try m2 : _ = (denc_statement body m1)
     in try aev : _ = (denc_assgnExp denc_exp i m2)
        in (let (st1, adrs, _, _) := aev in
            eval (storeValueAtAddress st1 adrs (C_InjNat n))). 

(********************************************************************)
(********************************************************************)

(* Denotation of a statement *)

Fixpoint denc_statement (s : c_statement) : domc_statement :=
  fun st : state =>
  match s with
  | C_Copy t e1 e2 =>
      try nt : _ = (denc_type typEnv t)
      in (let n := sizeOfType nt in
          try mv1 : _ = (denc_exp e1 st)
          in (let st1 := stateOfExpValue mv1 in
              let v1 := valueOfExpValue mv1 in
              try mv2 : _ = (denc_exp e2 st1)
              in (let st2 := stateOfExpValue mv2 in
                  let v2 := valueOfExpValue mv2 in copyMemo n v1 v2 st2)))
  | C_Assign ae e =>
      try de : _ = (denc_exp e st)
      in (let v1 := valueOfExpValue de in
          let st1 := stateOfExpValue de in
          try dae : _ = (denc_assgnExp denc_exp ae st1)
          in match dae with
             | MkAssgnExpValue st2 adrs _ _ =>
                 eval (storeBlockAtAddress st2 adrs v1)
             end)
  | C_Return e =>
      try sv : _ = (denc_exp e st)
      in (let m := memoOfState (stateOfExpValue sv) in
          let v := valueOfExpValue sv in excRaise state (C_SkipOver m v))
  | C_Block ls =>
      let em := eval st in
      fold_left
        (fun (r : c_execution state) (s : c_statement) =>
         try nr : _ = r in (denc_statement s nr)) ls em
  | C_ProcCall f realargs =>
      (* The components of the state before evaluating the function call *) 
      let maxi := maxPosition st in
      let stck := lVarsOfState st in
      let gbv := gVarsOfState st in 
      (* Look for the function code *)
      try funblock = (sdecl_map c_identEq denc_f f)
      in (let funParams := domc_paramOfFunDecl funblock in
          let funBody := domc_bodyOfFunDecl funblock in
          let funlocv := domc_localVarsOfFunDecl funblock in
          (* Evaluate the arguments of the function call *)
          try p : (state * list c_value) =
          (denc_expList denc_exp st realargs)
          in 
          (* Allocate the cells on the stack for the input and local variables *)
          (let (st1, rlva) := p in
           let pshl := zip funParams rlva in
           let st2 := allocateParams pshl st1 in
           let st3 :=
             allocateLocalVars funlocv st2
             (* Evaluate the the function body *)
              in
           try news = (funBody st3)
           in (eval (MkState (memoOfState news) maxi gbv stck)) with ex =>
           match ex with
            
               (* The function ended on a return instruction *)
               | C_SkipOver m _ =>
               eval (MkState m maxi gbv stck)
               (* A dynamic error occured *)
           | e => excRaise state e
           end)) with id => (excRaise state (IdentNotFound id))
  | C_If e thn els =>
      try mv1 : _ = (denc_exp e st)
      in (let m1 := stateOfExpValue mv1 in
          let v1 := valueOfExpValue mv1 in
          match v1 with
          | C_ValBasic (C_InjBool true) => denc_statement thn m1
          | C_ValBasic (C_InjBool false) => denc_statement els m1
          | x => excRaise state (WrongType x (one C_bool))
          end)
  | C_Switch e brchs dflt =>
      try mv1 : _ = (denc_exp e st)
      in (let m1 := stateOfExpValue mv1 in
          let v1 := valueOfExpValue mv1 in
          denc_switch denc_statement v1 dflt brchs m1)
  | C_ForDwn i fst body =>
      try aev : _ = (denc_assgnExp denc_exp i st)
      in (let (st1, adrs, _, _) := aev in
          let mv := storeValueAtAddress st1 adrs (C_InjNat fst) in
          iterate (forBody denc_statement i body) (eval mv) fst)
  end.

(*******************************************************************)
(*               Denotation of Function Declarations               *)
(*******************************************************************)

(* Normalizes the type of the headers to know how many cells have to been
   allocated for each of the parameters *)
Definition denc_header (env : c_funHeader) :
  c_execution (sdecl c_ident n_type) :=
  sdecl_fold_right
    (fun id obj r =>
     try env : _ = r
     in try nty : _ = (denc_type typEnv (typeOfVarDecl obj))
        in (eval (sdecl_addShdw env id nty))) env
    (eval (sdecl_empty c_ident n_type)).

(* Idem for the types of the local variables of the function *)
Definition denc_locals (env : c_varDecls) :
  c_execution (sdecl c_ident n_type) :=
  sdecl_fold_right
    (fun id obj r =>
     try env : _ = r
     in try nty : _ = (denc_type typEnv (typeOfVarDecl obj))
        in (eval (sdecl_addShdw env id nty))) env
    (eval (sdecl_empty c_ident n_type)).

End Denotation_Of_Expressions_And_Statements.

(*******************************************************************)

Definition denc_funDecl (called : sdecl c_ident domc_funDecl)
  (fd : c_funDecl) : c_execution domc_funDecl :=
  match fd with
  | MkFunDecl _ t args locs body => 
      (* Store the variables to be allocated before the execution of the function *)
      try hdr
      : _
      (* Store the denotation of the function for later execution *)
       = (denc_header args)
      in try lcs : _ = (denc_locals locs)
         in (let stm := denc_statement called body in
             eval (MkFunValue hdr lcs stm))
  end.

(* Propagate along the environment of functions *)
Definition denc_funDecls (fds : c_funDecls) : domc_funDecls :=
  sdecl_fold_right
    (fun id (fn : c_funDecl) r =>
     try fv : _ = r
     in try fd : _ = (denc_funDecl fv fn) in (eval (sdecl_addShdw fv id fd)))
    fds (eval (sdecl_empty c_ident domc_funDecl)).
End Memory_Allocation.


(****************************************************************************)
(*                     Denotation of a REACTIVE programs                    *)
(****************************************************************************)

(* Given an inifinite stream of input values for some of its variables
   and a list of variables to be observed, the denotation of the
   program [MkProgram tys gvs fns init loopbody] is the infinite
   sequence of outputs generated by the following program:

   begin 
     <init>;
     while true do
       <read inputs>;
       <loopbody>;
       <print outputs>
     done
   end

  An input value is just a C value, an output is either a value or 
  an exception raised by the program.  

  The semantics are parametrized by the type of traces generated by
  the program. For the proof, we use infinite traces, as in the
  semantics of Lustre. For the extraction into Ocaml --a language with
  strict semantics-- we use finite lists. Cf. the file OcamlSimulator.v *)


Section Parametric_Simulation.  

(* This section is necessary for being able to extract streams into
   finite lists, so that the function whileTrue and the simulator can
   be realized in Ocaml. *)

(* Parametric:to be instantiated differently in Coq and in Ocaml *)
Variable Stream : Set -> Set.

Notation StreamPIn := (Stream c_value) (only parsing).
Notation StreamPOut := (Stream (c_execution c_value)) (only parsing).
Notation c_readPEnv := (sdecl c_assgnExp (Stream c_value)) (only parsing).
Notation c_runPEnv := (sdecl c_assgnExp (Stream (c_execution c_value)))
  (only parsing).

(* Function generating the trace of one of the observed variables *)
Variable
  traceOfAssgnExp :
    sdecl c_typeIdent n_type ->
    sdecl c_ident domc_funDecl ->
    c_statement ->
    c_assgnExp ->
    sdecl c_assgnExp (Stream c_value) ->
    state -> Stream (c_execution c_value).

(*******************************************************************)

Section Simulate_Program.

(* Type definitions in normal form *)
Variable typEnv : sdecl c_typeIdent n_type.
(* Code of the previous functions *)
Variable fnsEnv : sdecl c_ident domc_funDecl.
(* The instruction to be placed inside the while-true loop *)
Variable loopbody : c_statement.
(* An infinite stream of values for each input *)
Variable inps : sdecl c_assgnExp (Stream c_value).
(* The MiniC variables to be observed *)
Variable outs : list c_assgnExp.

(*******************************************************************)
(* The following functions produce the trace corresponding to a 
   single variable of the MiniC program. *)

Section Simulate_One_Variable.
Variable out : c_assgnExp.

(* Stores a possible structured value in the memory positions associated to 
   an assignable expression *)
Definition storeSegmentFromAssgnExp (st0 : state) (ae : c_assgnExp)
  (lv : c_value) : c_execution state :=
  try aev : _ = (denc_assgnExp (denc_exp typEnv fnsEnv) ae st0)
  in (let (st1, addrss, _, _) := aev in
      eval (storeBlockAtAddress st1 addrss lv)).

(* Reads a possible structured value associated contained in 
   an assignable expression *)
Definition readSegmentFromAssgnExp (st0 : state) (ae : c_assgnExp) :
  c_execution c_value :=
  try aev : _ = (denc_assgnExp (denc_exp typEnv fnsEnv) ae st0)
  in (let (_, _, _, lv) := aev in eval lv).

(* Performs the <read inputs> step of the loop body *)
Definition storeReadInputs (inpenv : sdecl c_assgnExp c_value) :
  domc_statement :=
  fun st0 =>
  sdecl_fold_right
    (fun ae lv r => try st : _ = r in (storeSegmentFromAssgnExp st ae lv))
    inpenv (eval st0).


(* Simulate each of the outputs required *)
Definition c_simulateOuts (env : sdecl c_assgnExp (Stream c_value))
  (st0 : state) : sdecl c_assgnExp (Stream (c_execution c_value)) :=
  map (fun id => (id, traceOfAssgnExp typEnv fnsEnv loopbody id env st0))
    outs.

End Simulate_One_Variable.
End Simulate_Program.

(* The generic simulation function *)
Definition simulateProgram (prg : c_program)
  (env : sdecl c_assgnExp (Stream c_value)) (outs : list c_assgnExp) :
  c_execution (sdecl c_assgnExp (Stream (c_execution c_value))) :=
  match prg with
  | MkProgram tys gvs fns init loopbody =>
      try typEnv : _ = (denc_typeDefs tys)
      in try fnsEnv : _ = (denc_funDecls typEnv fns)
         in try allocSt : _ = (denc_varDecls typEnv gvs)
            in try initSt : _ = (denc_statement typEnv fnsEnv init allocSt)
               in (eval
                     (c_simulateOuts typEnv fnsEnv loopbody outs env initSt))
  end.

End Parametric_Simulation.

(************************************************************************)
(*        Denotation of a MiniC program using infinite traces           *)
(************************************************************************)

(* Realizing the variables of the section Parametric\_Simulation above 
   using co-inductive types *)

(* Inifite traces *)
Definition Trace := Stream (c_execution state).
Definition readInput (s : StreamIn) : c_value := hd s.
Definition readInputs (env : c_readEnv) : sdecl c_assgnExp c_value :=
  sdecl_image (fun s => hd s) env.
Definition outState (st : state) (s : Trace) : Trace := Cons (eval st) s.
Definition printError (err : c_dynError) (s : Trace) : Trace :=
  Cons (excRaise state err) s.

(* The while-true loop as a co-recursive definition *)
Section While_True_Statement.
Variable typEnv : sdecl c_typeIdent n_type.
Variable fnsEnv : sdecl c_ident domc_funDecl.
Variable loopbody : c_statement.
CoFixpoint whileTrue  : c_readEnv -> state -> Trace :=
  fun env st0 =>
  let inpshd := readInputs env in
  let inpstl := sdecl_image (fun s => tl s) env in
  try redSt = (storeReadInputs typEnv fnsEnv inpshd st0)
  in try newst = (denc_statement typEnv fnsEnv loopbody redSt)
     in (outState newst (whileTrue inpstl newst)) with err =>
     (printError err (whileTrue inpstl redSt)) with err =>
  (printError err (whileTrue inpstl st0)).

Variable out : c_assgnExp.
Definition projectAssgnExp (sst : Trace) : StreamOut :=
  extend
    (fun r =>
     try st : _ = r in (readSegmentFromAssgnExp typEnv fnsEnv st out)) sst.

Definition traceOfAssgnExp (env : c_readEnv) (st : state) : StreamOut :=
  projectAssgnExp (whileTrue env st).
End While_True_Statement.

(*****************************************************************************)
Definition denc_program (prg : c_program) (env : c_readEnv)
  (outs : list c_assgnExp) : c_execution c_runEnv :=
  simulateProgram (Stream:=Stream) traceOfAssgnExp prg env outs.

(****************************************************************************)
