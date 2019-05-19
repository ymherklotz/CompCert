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

Require Import Recdef Coqlib Maps Errors.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Cminor Cminortyping Ifconv.

Definition match_prog (prog tprog: program) :=
  match_program (fun cu f tf => transf_fundef f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. apply match_transform_partial_program; auto.
Qed.

Lemma known_id_sound_1:
  forall f id x, (known_id f)!id = Some x -> In id f.(fn_params) \/ In id f.(fn_vars).
Proof.
  unfold known_id.
  set (add := fun (ki: known_idents) (id: ident) => PTree.set id tt ki).
  intros.
  assert (REC: forall l ki, (fold_left add l ki)!id = Some x -> In id l \/ ki!id = Some x).
  { induction l as [ | i l ]; simpl; intros.
    - auto.
    - apply IHl in H0. destruct H0; auto. unfold add in H0; rewrite PTree.gsspec in H0.
      destruct (peq id i); auto. }
  apply REC in H. destruct H; auto. apply REC in H. destruct H; auto.
  rewrite PTree.gempty in H; discriminate.
Qed.

Lemma known_id_sound_2:
  forall f id, is_known (known_id f) id = true -> In id f.(fn_params) \/ In id f.(fn_vars).
Proof.
  unfold is_known; intros. destruct (known_id f)!id eqn:E; try discriminate.
  eapply known_id_sound_1; eauto.
Qed.

Lemma eval_safe_expr:
  forall ge f sp e m a,
  def_env f e ->
  safe_expr (known_id f) a = true ->
  exists v, eval_expr ge sp e m a v.
Proof.
  induction a; simpl; intros.
  - apply known_id_sound_2 in H0.
    destruct (H i H0) as [v E].
    exists v; constructor; auto.
  - destruct (eval_constant ge sp c) as [v|] eqn:E.
    exists v; constructor; auto.
    destruct c; discriminate.
  - InvBooleans. destruct IHa as [v1 E1]; auto.
    destruct (eval_unop u v1) as [v|] eqn:E.
    exists v; econstructor; eauto.
    destruct u; discriminate.
  - InvBooleans.
    destruct IHa1 as [v1 E1]; auto.
    destruct IHa2 as [v2 E2]; auto.
    destruct (eval_binop b v1 v2 m) as [v|] eqn:E.
    exists v; econstructor; eauto.
    destruct b; discriminate.
  - discriminate.
Qed.

Lemma step_selection:
  forall ge f id ty cond a1 a2 k sp e m v0 b v1 v2,
  eval_expr ge sp e m cond v0 -> Val.bool_of_val v0 b ->
  eval_expr ge sp e m a1 v1 ->
  eval_expr ge sp e m a2 v2 ->
  Val.has_type v1 ty -> Val.has_type v2 ty ->
  step ge (State f (Sselection id ty cond a1 a2) k sp e m)
       E0 (State f Sskip k sp (PTree.set id (if b then v1 else v2) e) m).
Proof.
  unfold Sselection; intros.
  eapply step_builtin with (optid := Some id).
  eauto 6 using eval_Enil, eval_Econs.
  replace (if b then v1 else v2) with (Val.select (Some b) v1 v2 ty).
  constructor; auto.
  destruct b; apply Val.normalize_idem; auto.
Qed.

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma wt_prog : wt_program prog.
Proof.
  red; intros.
  destruct TRANSL as [A _].
  exploit list_forall2_in_left; eauto.
  intros ((i' & gd') & B & (C & D)). simpl in *. inv D.
  destruct f; monadInv H2.
- monadInv EQ. econstructor; apply type_function_sound; eauto.
- constructor.
Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSL).

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial TRANSL).

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial TRANSL).

Lemma sig_transf_function:
  forall f tf,
  transf_fundef f = OK tf ->
  funsig tf = funsig f.
Proof.
  unfold transf_fundef, transf_partial_fundef; intros. destruct f.
- monadInv H. monadInv EQ. auto.
- inv H. auto.
Qed.

Lemma stackspace_transf_function:
  forall f tf,
  transf_function f = OK tf ->
  tf.(fn_stackspace) = f.(fn_stackspace).
Proof.
  intros. monadInv H. auto.
Qed.

Lemma eval_expr_preserved:
  forall sp e m a v, eval_expr ge sp e m a v -> eval_expr tge sp e m a v.
Proof.
  induction 1; econstructor; eauto.
  destruct cst; auto.
  simpl in *. unfold Genv.symbol_address in *. rewrite symbols_preserved. auto.
Qed.

Lemma eval_exprlist_preserved:
  forall sp e m al vl, eval_exprlist ge sp e m al vl -> eval_exprlist tge sp e m al vl.
Proof.
  induction 1; econstructor; eauto using eval_expr_preserved.
Qed.

(*
Lemma classify_stmt_sound:
  forall f sp e m s,
    match classify_stmt s with
    | SCskip =>
        forall k, star step ge (State f s k sp e m) E0 (State f Sskip k sp e m)
    | SCassign id a =>
        forall k v,
        eval_expr ge sp e m a v ->
        star step ge (State f s k sp e m) E0 (State f Sskip k sp (PTree.set id v e) m)
    | SCother => True
    end.
Proof.
  intros until s; functional induction (classify_stmt s).
  - intros; apply star_refl.
  - intros; apply star_one; constructor; auto.
  - assert (A: forall k, star step ge (State f (Sseq Sskip s0) k sp e m)
                              E0 (State f s0 k sp e m)).
    { intros. eapply star_two; constructor. }
    destruct (classify_stmt s0); auto;
    intros; (eapply star_trans; [apply A| auto | reflexivity]).
  - destruct (classify_stmt s0); auto.
    + intros. eapply star_left. constructor. eapply star_right.
      apply IHs0. constructor. eauto. eauto.
    + intros. eapply star_left. constructor. eapply star_right.
      apply IHs0. eauto. constructor. eauto. eauto.
  - auto.
Qed.
*)

Lemma classify_stmt_sound_1:
  forall f sp e m s k,
  classify_stmt s = SCskip ->
  star step ge (State f s k sp e m) E0 (State f Sskip k sp e m).
Proof.
  intros until s; functional induction (classify_stmt s); intros; try discriminate.
  - apply star_refl.
  - eapply star_trans; eauto. eapply star_two. constructor. constructor.
    traceEq. traceEq.
  - eapply star_left. constructor.
    eapply star_right. eauto. constructor.
    traceEq. traceEq.
Qed.

Lemma classify_stmt_sound_2:
  forall f sp e m a id v,
  eval_expr ge sp e m a v ->
  forall s k,
  classify_stmt s = SCassign id a ->
  star step ge (State f s k sp e m) E0 (State f Sskip k sp (PTree.set id v e) m).
Proof.
  intros until s; functional induction (classify_stmt s); intros; try discriminate.
  - inv H0. apply star_one. constructor; auto.
  - eapply star_trans; eauto. eapply star_two. constructor. constructor.
    traceEq. traceEq.
  - eapply star_left. constructor.
    eapply star_right. eauto. constructor.
    traceEq. traceEq.
Qed.

Lemma classify_stmt_wt_2:
  forall env tyret id a s,
  classify_stmt s = SCassign id a ->
  wt_stmt env tyret s ->
  wt_expr env a (env id).
Proof.
  intros until s; functional induction (classify_stmt s); intros CL WT;
  try discriminate.
- inv CL; inv WT; auto.
- inv WT; eauto.
- inv WT; eauto.
Qed.

Lemma if_conversion_sound:
  forall f env cond ifso ifnot s vb b k f' k' sp e m,
  if_conversion (known_id f) env cond ifso ifnot = Some s ->
  def_env f e -> wt_env env e ->
  wt_stmt env f.(fn_sig).(sig_res) ifso ->
  wt_stmt env f.(fn_sig).(sig_res) ifnot ->
  eval_expr ge sp e m cond vb -> Val.bool_of_val vb b ->
  let s0 := if b then ifso else ifnot in
  exists e1,
     step tge (State f' s k' sp e m) E0 (State f' Sskip k' sp e1 m)
  /\ star step ge (State f s0 k sp e m) E0 (State f Sskip k sp e1 m).
Proof.
  unfold if_conversion; intros until m; intros IFC DE WTE WT1 WT2 EVC BOV.
  set (s0 := if b then ifso else ifnot). set (ki := known_id f) in *.
  destruct (classify_stmt ifso) eqn:IFSO; try discriminate;
  destruct (classify_stmt ifnot) eqn:IFNOT; try discriminate;
  unfold if_conversion_base in IFC.
  - destruct (is_known ki id && safe_expr ki (Evar id) && safe_expr ki a) eqn:B; inv IFC.
    InvBooleans.
    destruct (eval_safe_expr ge f sp e m (Evar id)) as (v1 & EV1); auto.
    destruct (eval_safe_expr ge f sp e m a) as (v2 & EV2); auto.
    assert (Val.has_type v1 (env id)).
    { eapply wt_eval_expr; eauto using wt_prog. constructor. }
    assert (Val.has_type v2 (env id)).
    { eapply wt_eval_expr; eauto using wt_prog. eapply classify_stmt_wt_2; eauto. }
    econstructor; split.
    eapply step_selection; eauto using eval_expr_preserved.
    unfold s0; destruct b.
    rewrite PTree.gsident by (inv EV1; auto). apply classify_stmt_sound_1; auto.
    eapply classify_stmt_sound_2; eauto.
  - destruct (is_known ki id && safe_expr ki a && safe_expr ki (Evar id)) eqn:B; inv IFC.
    InvBooleans.
    destruct (eval_safe_expr ge f sp e m a) as (v1 & EV1); auto.
    destruct (eval_safe_expr ge f sp e m (Evar id)) as (v2 & EV2); auto.
    assert (Val.has_type v1 (env id)).
    { eapply wt_eval_expr; eauto using wt_prog. eapply classify_stmt_wt_2; eauto. }
    assert (Val.has_type v2 (env id)).
    { eapply wt_eval_expr; eauto using wt_prog. constructor. }
    econstructor; split.
    eapply step_selection; eauto using eval_expr_preserved.
    unfold s0; destruct b.
    eapply classify_stmt_sound_2; eauto.
    rewrite PTree.gsident by (inv EV2; auto). apply classify_stmt_sound_1; auto.
  - destruct (ident_eq id id0); try discriminate. subst id0.
    destruct (is_known ki id && safe_expr ki a && safe_expr ki a0) eqn:B; inv IFC.
    InvBooleans.
    destruct (eval_safe_expr ge f sp e m a) as (v1 & EV1); auto.
    destruct (eval_safe_expr ge f sp e m a0) as (v2 & EV2); auto.
    assert (Val.has_type v1 (env id)).
    { eapply wt_eval_expr; eauto using wt_prog. eapply classify_stmt_wt_2; eauto. }
    assert (Val.has_type v2 (env id)).
    { eapply wt_eval_expr; eauto using wt_prog. eapply classify_stmt_wt_2; eauto. }
    econstructor; split.
    eapply step_selection; eauto using eval_expr_preserved.
    unfold s0; destruct b; eapply classify_stmt_sound_2; eauto.
Qed.

Inductive match_cont: known_idents -> typenv -> cont -> cont -> Prop :=
  | match_cont_seq: forall ki env s k k',
      match_cont ki env k k' ->
      match_cont ki env (Kseq s k) (Kseq (transf_stmt ki env s) k')
  | match_cont_block: forall ki env k k',
      match_cont ki env k k' ->
      match_cont ki env (Kblock k) (Kblock k')
  | match_cont_call: forall ki env k k',
      match_call_cont k k' ->
      match_cont ki env k k'

with match_call_cont: cont -> cont -> Prop :=
  | match_call_cont_stop:
      match_call_cont Kstop Kstop
  | match_call_cont_base: forall optid f sp e k f' k' env
        (WT_FN: type_function f = OK env)
        (TR_FN: transf_function f = OK f')
        (CONT: match_cont (known_id f) env k k'),
      match_call_cont (Kcall optid f sp e k)
                      (Kcall optid f' sp e k').

Inductive match_states: state -> state -> Prop :=
  | match_states_gen: forall f s k sp e m f' s' env k'
        (WT_FN: type_function f = OK env)
        (TR_FN: transf_function f = OK f')
        (TR_STMT: transf_stmt (known_id f) env s = s')
        (CONT: match_cont (known_id f) env k k'),
      match_states (State f s k sp e m)
                   (State f' s' k' sp e m)
  | match_states_call: forall f args k m f' k'
        (TR_FN: transf_fundef f = OK f')
        (CONT: match_call_cont k k'),
      match_states (Callstate f args k m)
                   (Callstate f' args k' m)
  | match_states_return: forall v k m k'
        (CONT: match_call_cont k k'),
      match_states (Returnstate v k m)
                   (Returnstate v k' m).

Lemma match_cont_is_call_cont:
  forall ki env k k',
  match_cont ki env k k' -> is_call_cont k -> is_call_cont k' /\ match_call_cont k k'.
Proof.
  destruct 1; intros; try contradiction.  split; auto. inv H; exact I.
Qed.

Lemma match_cont_call_cont:
  forall ki env k k',
  match_cont ki env k k' -> match_call_cont (call_cont k) (call_cont k').
Proof.
  induction 1; auto. inversion H; subst; auto.
Qed.

Definition nolabel (s: stmt) : Prop :=
  forall lbl k, find_label lbl s k = None.

Lemma classify_stmt_nolabel:
  forall s, classify_stmt s <> SCother -> nolabel s.
Proof.
  intros s. functional induction (classify_stmt s); intros.
- red; auto.
- red; auto.
- apply IHs0 in H. red; intros; simpl. apply H.
- apply IHs0 in H. red; intros; simpl. rewrite H; auto.
- congruence.
Qed.

Lemma if_conversion_base_nolabel: forall ki env a id a1 a2 s,
  if_conversion_base ki env a id a1 a2 = Some s ->
  nolabel s.
Proof.
  unfold if_conversion_base; intros.
  destruct (is_known ki id && safe_expr ki a1 && safe_expr ki a2); inv H.
  red; auto.
Qed.

Lemma if_conversion_nolabel: forall ki env a s1 s2 s,
    if_conversion ki env a s1 s2 = Some s ->
    nolabel s1 /\ nolabel s2 /\ nolabel s.
Proof.
  unfold if_conversion; intros.
  Ltac conclude :=
    split; [apply classify_stmt_nolabel;congruence
           |split; [apply classify_stmt_nolabel;congruence
                   |eapply if_conversion_base_nolabel; eauto]].
  destruct (classify_stmt s1) eqn:C1; try discriminate;
  destruct (classify_stmt s2) eqn:C2; try discriminate.
  conclude.
  conclude.
  destruct (ident_eq id id0). conclude. discriminate.
Qed.

Lemma transf_find_label: forall lbl ki env s k k',
  match_cont ki env k k' ->
  match find_label lbl s k with
  | Some (s1, k1) =>
    exists k1', find_label lbl (transf_stmt ki env s) k' = Some (transf_stmt ki env s1, k1')
             /\ match_cont ki env k1 k1'
  | None => find_label lbl (transf_stmt ki env s) k' = None
  end.
Proof.
  induction s; intros k k' MC; simpl; auto.
- exploit (IHs1 (Kseq s2 k)). econstructor; eauto.
  destruct (find_label lbl s1 (Kseq s2 k)) as [[sx kx]|].
  + intros (kx' & A & B); rewrite A. exists kx'; auto.
  + intros A; rewrite A. apply IHs2; auto.
- destruct (if_conversion ki env e s1 s2) as [s|] eqn:IFC.
  + apply if_conversion_nolabel in IFC. destruct IFC as (L1 & L2 & L3).
    rewrite L1, L2. apply L3.
  + simpl. exploit (IHs1 k); eauto. destruct (find_label lbl s1 k) as [[sx kx]|].
    * intros (kx' & A & B). rewrite A. exists kx'; auto.
    * intros A; rewrite A. apply IHs2; auto.
- apply IHs. constructor; auto.
- apply IHs. constructor; auto.
- destruct (ident_eq lbl l).
  + exists k'; auto.
  + apply IHs; auto.
Qed.

Lemma simulation:
  forall S1 t S2, step ge S1 t S2 -> wt_state S1 ->
  forall R1, match_states S1 R1 ->
  exists S3 R2, star step ge S2 E0 S3 /\ step tge R1 t R2 /\ match_states S3 R2.
Proof.
  assert (DFL: forall R1 t R2 S2,
             step tge R1 t R2 -> match_states S2 R2 ->
             exists S3 R2, star step ge S2 E0 S3 /\ step tge R1 t R2 /\ match_states S3 R2).
  { intros. exists S2, R2; split. apply star_refl. auto. }
  destruct 1; intros WT R1 MS; inv MS.
- (* skip Kseq *)
  inv CONT; simpl. eapply DFL.
  constructor.
  econstructor; eauto.
  inv H.
- (* skip Kblock *)
  inv CONT; simpl. eapply DFL.
  constructor.
  econstructor; eauto.
  inv H.
- (* skip return *)
  exploit match_cont_is_call_cont; eauto. intros [A B].
  eapply DFL.
  eapply step_skip_call; eauto. erewrite stackspace_transf_function; eauto.
  econstructor; eauto.
- (* assign *)
  eapply DFL.
  econstructor. eapply eval_expr_preserved; eauto.
  econstructor; eauto.
- (* store *)
  eapply DFL.
  econstructor; eauto using eval_expr_preserved.
  econstructor; eauto.
- (* call *)
  exploit functions_translated; eauto using eval_expr_preserved.
  intros (tf & A & B).
  eapply DFL.
  econstructor; eauto using eval_expr_preserved, eval_exprlist_preserved.
  apply sig_transf_function; auto.
  econstructor; eauto. econstructor; eauto.
- (* tailcall *)
  exploit functions_translated; eauto using eval_expr_preserved.
  intros (tf & A & B).
  eapply DFL.
  econstructor; eauto using eval_expr_preserved, eval_exprlist_preserved.
  apply sig_transf_function; auto.
  erewrite stackspace_transf_function; eauto.
  econstructor; eauto using match_cont_call_cont.
- (* builtin *)
  eapply DFL.
  econstructor. eapply eval_exprlist_preserved; eauto.
  eapply external_call_symbols_preserved. eexact senv_preserved. eauto.
  econstructor; eauto.
- (* seq *)
  simpl. eapply DFL.
  econstructor.
  econstructor; eauto. econstructor; eauto.
- (* ifthenelse *)
  simpl. destruct (if_conversion (known_id f) env a s1 s2) as [s|] eqn:IFC.
  + inv WT. assert (env0 = env) by (inv WT_FN; inv WT_FN0; congruence); subst env0.
    inv WT_STMT.
    exploit if_conversion_sound; eauto.
    set (s0 := if b then s1 else s2).
    intros (e1 & A & B).
    econstructor; econstructor. split. eexact B. split. eexact A.
    econstructor; eauto.
  + eapply DFL.
    econstructor; eauto using eval_expr_preserved.
    econstructor; eauto. destruct b; auto.
- (* loop *)
  eapply DFL.
  simpl; econstructor.
  econstructor; eauto. econstructor; eauto.
- (* block *)
  eapply DFL.
  simpl; econstructor.
  econstructor; eauto. econstructor; eauto.
- (* exit seq *)
  inv CONT. eapply DFL.
  econstructor; eauto.
  econstructor; eauto.
  inv H.
- (* exit block *)
  inv CONT. eapply DFL.
  econstructor; eauto.
  econstructor; eauto.
  inv H.
- (* exit block *)
  inv CONT. eapply DFL.
  econstructor; eauto.
  econstructor; eauto.
  inv H.
- (* switch *)
  eapply DFL.
  econstructor; eauto using eval_expr_preserved.
  econstructor; eauto.
- (* return none *)
  eapply DFL.
  econstructor.  erewrite stackspace_transf_function; eauto.
  econstructor; eauto using match_cont_call_cont.
- (* return some *)
  eapply DFL.
  econstructor. eapply eval_expr_preserved; eauto. erewrite stackspace_transf_function; eauto.
  econstructor; eauto using match_cont_call_cont.
- (* label *)
  eapply DFL.
  simpl; econstructor.
  econstructor; eauto.
- (* goto *)
  exploit (transf_find_label lbl (known_id f) env (fn_body f)).
  apply match_cont_call. eapply match_cont_call_cont. eauto.
  rewrite H. intros (k'' & A & B).
  replace (transf_stmt (known_id f) env (fn_body f)) with (fn_body f') in A
  by (monadInv TR_FN; simpl; congruence).
  eapply DFL.
  econstructor; eauto.
  econstructor; eauto.
- (* internal function *)
  monadInv TR_FN. generalize EQ; intros EQ'; monadInv EQ'.
  eapply DFL.
  econstructor; simpl; eauto.
  econstructor; simpl; eauto. constructor; auto.
- (* external function *)
  monadInv TR_FN. eapply DFL.
  econstructor. eapply external_call_symbols_preserved. eexact senv_preserved. eauto.
  econstructor; eauto.
- (* return *)
  inv CONT. eapply DFL.
  econstructor.
  econstructor; eauto.
Qed.

Lemma initial_states_simulation:
  forall S, initial_state prog S -> exists R, initial_state tprog R /\ match_states S R.
Proof.
  intros; inv H.
  exploit function_ptr_translated; eauto. intros (tf & FIND & TR).
  exploit sig_transf_function; eauto. intros SG.
  econstructor; split.
  econstructor.  eapply (Genv.init_mem_transf_partial TRANSL); eauto.
  rewrite symbols_preserved, (match_program_main TRANSL); eauto.
  eauto.
  congruence.
  constructor; auto. constructor.
Qed.

Lemma final_states_simulation:
  forall S R r,
  match_states S R -> final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv CONT. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  set (ms := fun S R => wt_state S /\ match_states S R).
  eapply forward_simulation_determ_one with (match_states := ms).
- apply Cminor.semantics_determinate.
- apply senv_preserved.
- intros. exploit initial_states_simulation; eauto. intros [R [A B]].
  exists R; split; auto. split; auto.
  apply wt_initial_state with (p := prog); auto. exact wt_prog.
- intros. destruct H. eapply final_states_simulation; eauto.
- intros. destruct H0.
  exploit simulation; eauto. intros (s1'' & s2' & A & B & C).
  exists s1'', s2'. intuition auto. split; auto.
  eapply subject_reduction_star with (st1 := s1). eexact wt_prog.
  econstructor; eauto. auto.
Qed.

End PRESERVATION.
