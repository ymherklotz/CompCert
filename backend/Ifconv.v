(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Maps Errors.
Require Import AST Events Cminor.
Require Import Cminortyping.

Definition tyenv := ident -> typ.
Definition known_idents := PTree.t unit.

Definition is_known (ki: known_idents) (id: ident) :=
  match ki!id with Some _ => true | None => false end.

Definition safe_unop (op: unary_operation) : bool :=
  match op with
  | Ointoffloat | Ointuoffloat | Ofloatofint | Ofloatofintu => false
  | Ointofsingle | Ointuofsingle | Osingleofint | Osingleofintu => false
  | Olongoffloat | Olonguoffloat | Ofloatoflong | Ofloatoflongu => false
  | Olongofsingle | Olonguofsingle | Osingleoflong | Osingleoflongu => false
  | _ => true
  end.

Definition safe_binop (op: binary_operation) : bool :=
  match op with
  | Odiv | Odivu | Omod | Omodu => false
  | Odivl | Odivlu | Omodl | Omodlu => false
  | Ocmpl _ | Ocmplu _ => false
  | _ => true
  end.

Fixpoint safe_expr (ki: known_idents) (a: expr) : bool :=
  match a with
  | Evar v => is_known ki v
  | Econst c => true
  | Eunop op e1 => safe_unop op && safe_expr ki e1
  | Ebinop op e1 e2 => safe_binop op && safe_expr ki e1 && safe_expr ki e2
  | Eload chunk e => false
  end.

Definition Sselection (id: ident) (ty: typ) (cond ifso ifnot: expr) : stmt :=
  Sbuiltin (Some id) (EF_select ty) (cond :: ifso :: ifnot :: nil).

Inductive stmt_class : Type :=
  | SCskip
  | SCassign (id: ident) (a: expr)
  | SCother.

Function classify_stmt (s: stmt) : stmt_class :=
  match s with
  | Sskip => SCskip
  | Sassign id a => SCassign id a
  | Sseq Sskip s => classify_stmt s
  | Sseq s Sskip => classify_stmt s
  | _ => SCother
  end.

Definition if_conversion_base
      (ki: known_idents) (env: tyenv)
      (cond: expr) (id: ident) (ifso ifnot: expr) : option stmt :=
  if is_known ki id && safe_expr ki ifso && safe_expr ki ifnot
  then Some (Sselection id (env id) cond ifso ifnot)
  else None.

Definition if_conversion
      (ki: known_idents) (env: tyenv)
      (cond: expr) (ifso ifnot: stmt) : option stmt :=
  match classify_stmt ifso, classify_stmt ifnot with
  | SCskip, SCassign id a =>
      if_conversion_base ki env cond id (Evar id) a
  | SCassign id a, SCskip =>
      if_conversion_base ki env cond id a (Evar id)
  | SCassign id1 a1, SCassign id2 a2 =>
      if ident_eq id1 id2 then if_conversion_base ki env cond id1 a1 a2 else None
  | _, _ => None
  end.

Fixpoint transf_stmt (ki: known_idents) (env: tyenv) (s: stmt) : stmt :=
  match s with
  | Sskip => s
  | Sassign _ _ => s
  | Sstore _ _ _ => s
  | Scall _ _ _ _ => s
  | Stailcall _ _ _ => s
  | Sbuiltin _ _ _ => s
  | Sseq s1 s2 => Sseq (transf_stmt ki env s1) (transf_stmt ki env s2)
  | Sifthenelse e s1 s2 =>
      match if_conversion ki env e s1 s2 with
      | Some s => s
      | None => Sifthenelse e (transf_stmt ki env s1) (transf_stmt ki env s2)
      end
  | Sloop s1 => Sloop (transf_stmt ki env s1)
  | Sblock s1 => Sblock (transf_stmt ki env s1)
  | Sexit _ => s
  | Sswitch _ _ _ _ => s
  | Sreturn _ => s
  | Slabel lbl s1 => Slabel lbl (transf_stmt ki env s1)
  | Sgoto _ => s
  end.

Definition known_id (f: function) : known_idents :=
  let add (ki: known_idents) (id: ident) := PTree.set id tt ki in
  List.fold_left add f.(fn_vars)
      (List.fold_left add f.(fn_params) (PTree.empty unit)).

Local Open Scope error_monad_scope.

Definition transf_function (f: function) : res function :=
  let ki := known_id f in
  do env <- type_function f;
  OK (mkfunction f.(fn_sig) f.(fn_params) f.(fn_vars) f.(fn_stackspace)
                 (transf_stmt ki env f.(fn_body))).

Definition transf_fundef (fd: fundef) : res fundef :=
  transf_partial_fundef transf_function fd.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.
