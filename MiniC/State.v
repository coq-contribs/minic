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


Require Import List.
Require Import StreamDefs.
Require Import MLImport.
Require Import ListDefs.
Require Import SimplDecl.
Require Import Stack.
Require Import Exceptions.

Require Import BasicTypes.
Require Import CAbstractSyntax.
Require Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.

(**************************************************************************)
(* This file describes the state of the MiniC interpretation machine,
   as well as the different interpretation domains of the syntactical
   constructions of MiniC.

   The state of the C interpreter consists of three mappings: 
       1- the current state of the computer memory: a mapping from 
          addresses to values
       2- an environment associating a type and a starting address to each 
          static variable of the program;
       3- a stack associating a type and a starting address to each 
          temporary variable of the program.

   The types in the environments are used to access to the different
   components of the structure. They also enable to retraive the
   number of memory cells used to store the object that the variable
   denotes.

   IMPORTANT: We assume that structures and arrays are allocated as
   sequences of consecutive memory cells. This seems to be true for
   gcc and it is consistent with C memory arithmetic. SCADE uses
   indirectly this assumption through the primitives _comp_mem and
   _copy_mem.

   Every static variable is unique and its information cannot be
   removed.  Adding two variable declarations with the same name means
   redeclaration. The first declaration becomes unaccessible (forever).

   On the contrary,there may be several local variables in the stack,
   and entries can be pop up. When a variable is pop up from the
   stack, hidden ones may become visible again.                             *)

(****************************************************************************)
(*                Domain of Interpretation of MiniC Types                   *)
(****************************************************************************)

(* The denotation of a type is a normalized type, where all the type 
   variables have been replaced by their respective definitions.

   Type normalization is necessary to know the actual size of an
   object stored in the memory from a certain starting address.             *)

Inductive n_type : Set :=
  | N_Void : n_type
  | N_PrimType : c_predefType -> n_type
  | N_Pointer : n_type -> n_type
  | N_Array : c_natVal -> n_type -> n_type
  | N_Struct : sdecl c_ident n_type -> n_type.
Parameter n_typeEq : forall x y : n_type, {x = y} + {x <> y}.

Definition domc_type : Set := c_execution n_type.
Definition domc_typeDef : Set := c_execution n_type.
Definition domc_typeDefs : Set := c_execution (sdecl c_typeIdent n_type).

(*************************************************************************)
(* Type size: the function computing the memory space (in cells)
   necesary to allocate an object of normal type t. Representing the
   length of the object as a type --instead of as a number-- enables the
   access to any sub-structure of the objet.                             *)

Fixpoint sizeOfType (t : n_type) : nat :=
  match t with
  | N_Void => 1
  | N_PrimType _ => 1
  | N_Pointer _ => 1
  | N_Array n t => sizeOfType t * n
  | N_Struct binds =>
      sdecl_fold_right (fun x t n => n + sizeOfType t) binds 0
  end.

(****************************************************************************)
(*         Domain of Interpretation of MiniC Static Variable Envrionment    *)
(****************************************************************************)

(* Memory allocation depends on the size of the object to be allocated,
   that is determined by its type. This is why an environment of sizes
   for the defined types is necessary.
*)

Record domc_varDecl : Set := C_VarObj
  {c_startAddressOfVarObj : address;
    (* starting address          *)
    c_typeOfVarObj : n_type (* size of the stored object *)
   }.

Definition domc_varDecls : Set := sdecl c_ident domc_varDecl.
Definition domc_emptyvarDecls : domc_varDecls :=
  sdecl_empty c_ident domc_varDecl.

(****************************************************************************)
(*                  State of the MiniC Interpretation Machine               *)
(****************************************************************************)

Record state : Set := MkState
  { (* the values contained at each address *)
    memoOfState : memory;
   
    (* the next memory address to be used for variable allocation *)
    maxPosition : address;
    
    (* starting addresses and size for each static identifier *)
    gVarsOfState : domc_varDecls;
   
    (* starting addresses and size for each temporary identifier *)
    lVarsOfState : domc_varDecls}.

Definition emptyState : state :=
  MkState memo_new baseAddress domc_emptyvarDecls domc_emptyvarDecls.

(****************************************)
(* Retrieving information form a state  *)
(****************************************)

Definition typeOfVarInState (s0 : state) (id : c_ident) :
  c_execution n_type :=
  match s0 with
  | MkState m maxi sv dv =>
      try obj = (sdecl_map c_identEq dv id) in (eval (c_typeOfVarObj obj))
      with err =>
      try obj = (sdecl_map c_identEq sv id) in (eval (c_typeOfVarObj obj))
      with err => (excRaise n_type (IdentNotFound id))
  end.

(***************************************************************************)
(* The STARTING CELL of the memory segment containing the object
   associated with the id. *)

Definition addressOfVar (st : state) (id : c_ident) : 
  c_execution address :=
  let lvars := lVarsOfState st in
  let gvars := gVarsOfState st in
  try obj = (stack_map c_identEq lvars id)
  in (eval (c_startAddressOfVarObj obj)) with x_ =>
  try obj = (sdecl_map c_identEq gvars id)
  in (eval (c_startAddressOfVarObj obj)) with id =>
  (excRaise address (IdentNotFound id)).

(***************************************************************************)
(* Retrieving a structured value from the memory                           *)

Section Retreive_Structured_Values_From_Memory.
Variable memo : memory.

Section Raise_A_List_Of_Values.
Variable readVal : n_type -> address -> c_value.
Variable nty : n_type.
Fixpoint readArrayVal (n : nat) : address -> list c_value :=
  fun addrs =>
  match n with
  | O => nil (A:=c_value)
  | S m =>
      readVal nty addrs
      :: readArrayVal m (shiftToAddress addrs (sizeOfType nty))
  end. 
Fixpoint readStructVal (binds : list (c_ident * n_type)) :
 address -> list (c_ident * c_value) :=
  fun addrs =>
  match binds with
  | nil => nil (A:=c_ident * c_value)
  | (x, ty) :: l =>
      (x, readVal ty addrs)
      :: readStructVal l (shiftToAddress addrs (sizeOfType ty))
  end. 
End Raise_A_List_Of_Values.
(******************************************************************)
(* Raises up a possible structured value from the flat suite of 
   cells the memory is. *)
Fixpoint readMemoBlock (nty : n_type) : address -> c_value :=
  fun addrs =>
  match nty with
  | N_Void => C_ValBasic (memo_access memo addrs)
  | N_PrimType _ => C_ValBasic (memo_access memo addrs)
  | N_Pointer _ => C_ValBasic (memo_access memo addrs)
  | N_Array n t =>
      C_ValTuple (readArrayVal readMemoBlock t n addrs)
      (* Necessary for compatibility with compileValue *) 
  | N_Struct nil => C_ValTuple nil
  | N_Struct binds => C_ValStruct (readStructVal readMemoBlock binds addrs)
  end.

End Retreive_Structured_Values_From_Memory.

(******************************************************************)
(* Retrieves a structured value from a given identifier         *) 
 
Definition segmentOfVar (st : state) (id : c_ident) : 
  c_execution c_value :=
  let m := memoOfState st in
  let lvars := lVarsOfState st in
  let gvars := gVarsOfState st in
  try obj = (stack_map c_identEq lvars id)
  in (let (adrs, t) := obj in eval (readMemoBlock m t adrs)) with x_ =>
  try obj = (sdecl_map c_identEq gvars id)
  in (let (adrs, t) := obj in eval (readMemoBlock m t adrs)) with id =>
  (excRaise c_value (IdentNotFound id)).

(****************************************)
(*  Storing information into the state  *)
(****************************************)

(******************************************************************)
(* Storing a structured value into the memory                     *)

Section Store_Structured_Values_In_Memory.
(* The number of cells necessary to store a structured value *)
Fixpoint sizeOfValue (v : c_value) : nat :=
  match v with
  | C_ValBasic _ => 1
  | C_ValTuple lv => fold_right (fun v r => sizeOfValue v + r) 0 lv
  | C_ValStruct binds =>
      sdecl_fold_right (fun id v r => sizeOfValue v + r) binds 0
  end.

(* Auxiliary: storing a list of values *)
Section Store_A_List_Of_Values.
Variable storeValue : memory -> address -> c_value -> memory.
Fixpoint storeArray (m : memory) (addrs : address) 
 (lv : list c_value) {struct lv} : memory :=
  match lv with
  | nil => m
  | v :: l1 =>
      storeArray (storeValue m addrs v)
        (shiftToAddress addrs (sizeOfValue v)) l1
  end.
Fixpoint storeStruct (m : memory) (addrs : address)
 (lv : list (c_ident * c_value)) {struct lv} : memory :=
  match lv with
  | nil => m
  | (x, v) :: l1 =>
      storeStruct (storeValue m addrs v)
        (shiftToAddress addrs (sizeOfValue v)) l1
  end.
End Store_A_List_Of_Values.

(* Stores a structured value in the memory *)
Fixpoint storeMemoBlock (m : memory) (addrs : address) 
 (v : c_value) {struct v} : memory :=
  match v with
  | C_ValBasic v => memo_store m addrs v
  | C_ValTuple lv => storeArray storeMemoBlock m addrs lv
  | C_ValStruct binds => storeStruct storeMemoBlock m addrs binds
  end.
End Store_Structured_Values_In_Memory.

(***************************************************************************)
(* Stores a basic value v at the address adrs *)

Definition storeValueAtAddress (st : state) (adrs : address)
  (v : c_basicValue) : state :=
  match st with
  | MkState m maxi sv dv => MkState (memo_store m adrs v) maxi sv dv
  end.
(***************************************************************************)
(* Stores a possibly structured value v at the address adrs *)

Definition storeBlockAtAddress (st : state) (adrs : address) 
  (v : c_value) : state :=
  match st with
  | MkState m maxi sv dv => MkState (storeMemoBlock m adrs v) maxi sv dv
  end.

(***************************************************************************)
(* Assigns a structured value v to the memory segment associated to the 
   variable id *)

Definition storeSegmentFromVar (st : state) (id : c_ident) 
  (lv : c_value) : c_execution state :=
  let m := memoOfState st in
  try addrss : _ = (addressOfVar st id)
  in match st with
     | MkState memo maxi sv dv =>
         eval (MkState (storeMemoBlock memo addrss lv) maxi sv dv)
     end.

(***************************************************************************)
(* Copies the block of n memory cells starting in adrs2 into the block of
   n memory cells starting from adrs1. *)

Definition c_copyMemo (st : state) (n : nat) (adrs1 adrs2 : address) :
  state :=
  match st with
  | MkState memo maxi sv dv =>
      MkState (memo_copy memo n adrs1 adrs2) maxi sv dv
  end.


(****************************************************************************)
(*        Interpretation Domain of MiniC Assignable Expressions             *)
(****************************************************************************)

(* Universe of expression values *)
Definition domc_univ := c_value.

(* An assignable expression denotes:
      1.- a memory block, representad by a starting address and a normalized 
          type;
      2.- a value;
      3._ a new current state, since evaluating the expression may
          also produce a side effect changing the state of the MiniC
          machine, for example when an array index calls a function
          modifying a global variable. *)

Record c_assgnExpValue : Set := MkAssgnExpValue
  {stateOfAssgnExpValue : state;
   addressOfAssgnExpValue : address;
   typeOfAssgnExpValue : n_type;
   valueOfAssgnExpValue : domc_univ}.

Definition domc_assgnExp := c_execution c_assgnExpValue.


(****************************************************************************)
(*              Interpretation Domain of MiniC Expressions                  *)
(****************************************************************************)

(* An expression denotes a value and a possible new current state. *)

Record c_expValue : Set := MkExpValue
  {stateOfExpValue : state; valueOfExpValue : domc_univ}.
Definition domc_exp := c_execution c_expValue.

(****************************************************************************)
(*              Interpretation Domain of MiniC Instructions                 *)
(****************************************************************************)

(* A statement denotes a function transforming the current state of the 
   interpreter *)

Definition domc_statement := state -> c_execution state.

(****************************************************************************)
(*          Interpretation Domain of MiniC Function Declarations            *)
(****************************************************************************)

(* The denotation of a function declaration is the denotation of its body,
   plus the temporary variables that must be allocated before executing
   the denotation of its body.                                             *)

Record domc_funDecl : Set := MkFunValue
  {domc_paramOfFunDecl : sdecl c_ident n_type;
    (* input variables *)
    domc_localVarsOfFunDecl : sdecl c_ident n_type;
    (* local variables *)
    domc_bodyOfFunDecl : domc_statement (* function code   *)
   }.
Definition domc_funDecls := c_execution (sdecl c_ident domc_funDecl).

(****************************************************************************)
(*          Interpretation Domain of MiniC Programs                         *)
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
  an exception raised by the program.                                      *)

Definition StreamIn : Set := Stream c_value.
Definition StreamOut : Set := Stream (c_execution c_value).
Definition c_readEnv : Set := sdecl c_assgnExp StreamIn.
Definition c_runEnv : Set := sdecl c_assgnExp StreamOut.
Definition domc_program : Set := c_execution c_runEnv.
(***************************************************************************)
(***************************************************************************)
