Require Import List.

Require Import MLImport.
Require Import SimplDecl.

Require Export BasicTypes.

(**************************************************************************)
(* This file contains the abstract syntax of MiniC programs.              *)
(**************************************************************************)


(**************************************************************************)
(*                         MiniC Literals                                 *)
(**************************************************************************)

(* Literals are directly represented as constants from the interpretation 
   domain of expressions defined in BasicTypes.v *)

Definition c_literal := c_basicValue.


(**************************************************************************)
(*                         MiniC Types                                    *)
(**************************************************************************)

(* Predefined types *)
Inductive c_predefType : Set :=
  | C_bool : c_predefType
  | C_nat : c_predefType
  | C_int : c_predefType
  | C_real : c_predefType
  | C_char : c_predefType.

(* MiniC types *)
Inductive c_type : Set :=
  | C_Void : c_type
  | C_DefType : c_typeIdent -> c_type
  | C_PrimType : c_predefType -> c_type
  | C_Pointer : c_type -> c_type
  | C_Array : c_natVal -> c_type -> c_type
  | C_Struct : sdecl c_ident c_type -> c_type.

(* TODO: actually, there are no nested struct definitions in C. 
   The constructor C_Struct should be rather like that:

   | C_Struct   : (sdecl c_ident c_typeIdent) -> c_type.
*)

Parameter c_typeEq : forall x y : c_type, {x = y} + {x <> y}.
Coercion C_PrimType : c_predefType >-> c_type.
Coercion C_DefType : c_typeIdent >-> c_type.

(* Environment of type definitions *)
Definition c_typeDefs : Set := sdecl c_typeIdent c_type.

(**************************************************************************)
(*                       MiniC Primitive Operators                        *)
(**************************************************************************)

(* Unary operators *)
Inductive c_unOp : Set :=
  | C_Not : c_unOp
  | C_Mns : c_unOp
  | C_Cast : c_predefType -> c_unOp.

(* Binary operators *)
Inductive c_binOp : Set :=
  | C_Equal : c_binOp
  | C_Lt : c_binOp
  | C_Gt : c_binOp
  | C_Le : c_binOp
  | C_Ge : c_binOp 
      (* Strict and, stands for the &  operator in C *)
  | C_And : c_binOp
      (* Lazy and,   stands for the && operator in C *)
  | C_AndAnd : c_binOp
  | C_Or : c_binOp
  | C_Xor : c_binOp
  | C_Plus : c_binOp
  | C_Minus : c_binOp
  | C_Mult : c_binOp
  | C_Power : c_binOp
  | C_Div : c_binOp
  | C_Mod :
      c_binOp
      (* this corresponds to the function _comp_mem used by lustre2C *)
  | C_CompMem : c_type -> c_binOp. 


(**************************************************************************)
(*                         MiniC Expressions                              *)
(**************************************************************************)

(* Expressions *)
Inductive c_exp : Set :=
  | C_AssgnInj : c_assgnExp -> c_exp
  | C_Derefer : c_assgnExp -> c_exp
  | C_Val : c_literal -> c_exp
  | C_UnApp : c_unOp -> c_exp -> c_exp
  | C_BinApp : c_binOp -> c_exp -> c_exp -> c_exp
  | C_FunCall : c_ident -> list c_exp -> c_exp
with

(* Assignable expressions: the left hand side of an assignment instruction,
   those expression that also denote a memory address. *)
c_assgnExp : Set :=
  | C_Var : c_ident -> c_assgnExp
  | C_Refer : c_assgnExp -> c_assgnExp
  | C_ArrayPos : c_assgnExp -> c_exp -> c_assgnExp
  | C_StructPos : c_assgnExp -> c_ident -> c_assgnExp.

Parameter c_assgnExpEq : forall x y : c_assgnExp, {x = y} + {x <> y}.
Coercion C_AssgnInj : c_assgnExp >-> c_exp.
Coercion C_Val : c_literal >-> c_exp.

(**************************************************************************)
(*                    MiniC Variable Declarations                         *)
(**************************************************************************)

Record c_varDecl : Set := C_MkVarDecl {typeOfVarDecl : c_type}.

Definition c_varDecls : Set := sdecl c_ident c_varDecl.
Definition c_noVarDecl : c_varDecls := sdecl_empty c_ident c_varDecl.

(**************************************************************************)
(*               Formal parameters of MiniC functions                     *)
(**************************************************************************)

Definition c_funInput : Set := c_varDecl.
Definition c_funHeader := sdecl c_ident c_funInput.
Definition c_noFunHeader : c_funHeader := sdecl_empty c_ident c_funInput.

(**************************************************************************)
(*                       MiniC instructions                               *)
(**************************************************************************)

Inductive c_statement : Set :=
 (* The _copy_memo function used in lustre2C *)
  | C_Copy :
      c_type ->
      c_exp -> c_exp -> c_statement 
               (* assignment instruction "=" *)
  | C_Assign : c_assgnExp -> c_exp -> c_statement 
                             (* return *)
  | C_Return : c_exp -> c_statement
               (* instruction block { ...} *)
  | C_Block : list c_statement -> c_statement
              (* function call *)
  | C_ProcCall : c_ident -> list c_exp -> c_statement
                            (* if-then-else *)
  | C_If :
      c_exp ->
      c_statement ->
      c_statement ->
      c_statement
      (* switch with default case and break instruction at the end of each branch *)
  | C_Switch :
      c_exp ->
      list (c_intVal * c_statement) ->
      c_statement -> c_statement 
      (* for(i=n;i<0;i--){...} *)
  | C_ForDwn : c_assgnExp -> c_natVal -> c_statement -> c_statement.

(**************************************************************************)
(*                     MiniC function declaration                         *)
(**************************************************************************)

Record c_funDecl : Set := MkFunDecl
  {c_nameOfFunDecl : c_ident;
   c_typeOfFunDecl : c_type;
   c_paramOfFunDecl : c_funHeader;
   c_localVarsOfFunDecl : c_varDecls;
   c_bodyOfFunDecl : c_statement}.

Definition c_funDecls := sdecl c_ident c_funDecl.

(**************************************************************************)
(*                            MiniC Program                               *)
(**************************************************************************)

(* This is the  abstract syntax of a REACTIVE C program, that is, 
   a program whose main function is of the form:

   <initializations>;
   while true do 
     <loop body>
   done;                  *)

Record c_program : Set := MkProgram
  {tdOfProgram : c_typeDefs (* type definitions *)
   ;
   gvOfProgram : c_varDecls (* global variables *)
   ;
   fnOfProgram : c_funDecls (* function definitions *)
   ;
   initOfProgram : c_statement (* initialization of the while-true loop *)
   ;
   loopOfProgram : c_statement (* while-true loop body *) 
   }.

(**************************************************************************)
(*                 Some useful macros for MinC programs                   *)
(**************************************************************************)

(* Some useful macros for C programs *)
Definition c_expOfVar (id : c_ident) : c_exp := C_AssgnInj (C_Var id).
Definition c_assgnExpOfVar (id : c_ident) : c_exp := C_Var id.
Definition c_arrow (r l : c_ident) : c_assgnExp :=
  C_StructPos (C_Refer (C_Var r)) l.

Definition nullStmt : list c_statement := nil.
Definition skipStmt : c_statement := C_Block nullStmt.
(**************************************************************************)
(**************************************************************************)