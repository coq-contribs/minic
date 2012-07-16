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


(* Representation of ML exceptions *)

Global Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.

Section Exception_Type.

Inductive exc (V E : Set) : Set :=
  | Value : V -> exc V E
  | Error : E -> exc V E.

Variable V1 V2 E1 E2 : Set.

Definition excDecomp (C : Set) (e : exc V1 E1) (f : V1 -> C) 
  (g : E1 -> C) : C := match e with
                       | Value x => f x
                       | Error y => g y
                       end.

Definition excValue (v : V1) : exc V1 E1 := Value E1 v.
Definition excRaise (b : E1) : exc V2 E1 := Error V2 b.

Definition excReraise (e : exc V1 E1) (f : V1 -> exc V2 E1) : 
  exc V2 E1 := excDecomp e f (fun x => excRaise x).


End Exception_Type.

(**************************************************************************)

Notation "'try' id1 = e 'in' c 'with' id2 => d" :=
  (excDecomp e (fun id1 => c) (fun id2 => d))
  (at level 1, id1 ident, id2 ident, c, d, e at level 1).

Notation "'try' id1 = e 'in' c" := (excReraise e (fun id1 => c))
  (at level 1, id1 ident, c, e at level 1).

Notation "'try' id1 : T = e 'in' c" := (excReraise e (fun id1 : T => c))
  (at level 1, id1 ident, c, e at level 1, T at level 0).

(**************************************************************************)


(* Example :

Require Exceptions.
Inductive dicoError [Key: Set] :Set := 
     DicoError   : Key -> (dicoError Key). 

Parameter dictionary : Set -> Set -> Set.

Parameter dico_map
     : (Key,Data:Set)(dictionary Key Data)->Key->(exc Data (dicoError Key)).

Record state : Set := 
 MkState
  { gVarsOfState : (dictionary nat bool)
  ; lVarsOfState : (dictionary nat bool)
  }.

Definition natDicoError := (dicoError nat).

Inductive stateError : Set := 
  StateError   : stateError |
  InjDicoError : natDicoError -> stateError. 

Coercion InjDicoError : natDicoError  >-> stateError.


Definition addressOfVar : state -> nat -> (exc bool stateError) :=
  [st:state][id:nat]
    let lvars  = (lVarsOfState st) in
    let gvars  = (gVarsOfState st) 
    in  (try addrss = (dico_map ? ? lvars id)
         in  (excValue stateError  addrss)
         with _ =>  try addrss = (dico_map ? ? gvars id)
                    in  (excValue stateError addrss)
                    with _ => (excRaise bool StateError))
.

Require Extraction.
Extract Constant dictionary => dico.
Extract Constant dico_map   => dico_map.
Extract Constant  excValue     => excValue.
Extract Constant  excRaise     => excRaise.
Extract Constant  excDecomp    => excDecomp.
Write Caml File "prueba" [addressOfVar].

*)