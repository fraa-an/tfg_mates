From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Program.Tactics.

Import ListNotations.

Require Import LenguajeYul.dialect.
Require Import main.ast.
Require Import main.semantica.


Module YulEquivalences (D : DIALECT) (A : AST_INTERFACE D).
    Module Sem := YulSemantica D A.
    Import A.
    Import Sem.

    Lemma existsb_env_in : forall (env : A.yul_env) (n : string) (v : D.value_t), In (n, v) env -> existsb (fun '(m, _) => String.eqb n m) env = true.
    Proof.
      induction env as [| [n' v'] resto IH]; intros n v Hin.
      - contradiction.
      - simpl. destruct Hin as [Heq | Hin].
        + inversion Heq; subst. rewrite String.eqb_refl. reflexivity.
        + apply IH in Hin.
          destruct (String.eqb n n').
          * reflexivity.
          * exact Hin.
    Qed.

    Lemma filter_env_id : forall (env1 env2 : A.yul_env), (forall n v, In (n, v) env1 -> existsb (fun '(m, _) => String.eqb n m) env2 = true) ->
        filter (fun '(n, _) => existsb (fun '(m, _) => String.eqb n m) env2) env1 = env1.
    Proof.
      induction env1 as [| [k v'] resto IH]; intros env2 H.
      - reflexivity.
      - simpl.
          assert (H_h : existsb (fun '(m, _) => String.eqb k m) env2 = true).
          { apply (H k v'). left. reflexivity. }
          rewrite H_h. 
          f_equal.
          apply IH.
          intros n' v'' Hin.             
          apply (H n' v''). right. exact Hin.
    Qed.

    Lemma restringe_env_mismo : forall (env : A.yul_env), restringe_env env env = env.
    Proof.
      intros env.
      unfold restringe_env.
      apply filter_env_id.
      intros n v Hin.
      apply (existsb_env_in env n v).
      exact Hin.
    Qed.

    Definition expr_equiv (e1 e2 : yul_expr) : Prop :=
        forall f env fenv state,
            eval_yul f e1 env fenv state = eval_yul f e2 env fenv state.

    Definition list_equiv (l1 l2 : list yul_expr) : Prop :=
        forall f env fenv state,
            eval_list f l1 env fenv state = eval_list f l2 env fenv state.
    
    Definition expr_list_equiv (e : yul_expr) (l : list yul_expr) : Prop :=
    forall env fenv state res env' fenv' state',
      (exists f, eval_yul f e env fenv state = (res, env', fenv', state', Yul_Running)) <->
      (exists f, eval_list f l env fenv state = (res, env', fenv', state', Yul_Running)).

    Theorem yul_skip_izq : forall l,
        list_equiv ([] ++ l) l.
    Proof.
      intros l f env fenv state.
      simpl. reflexivity.
    Qed.

    Theorem yul_skip_der : forall l,
        list_equiv (l ++ []) l.
    Proof.
      intros l f env fenv state.
      unfold list_equiv.
      rewrite app_nil_r.
      reflexivity.
    Qed.

    (*(c1;c2);c3 == c1;(c2;c3)*)
    Theorem yul_seq_assoc : forall l1 l2 l3,
        list_equiv ((l1 ++ l2) ++ l3) (l1 ++ (l2 ++ l3)).
    Proof.
      intros l1 l2 l3.
      unfold list_equiv.
      intros.
      rewrite app_assoc.
      reflexivity.
    Qed.

    Theorem yul_if_false : forall (v : D.value_t) (inst : list yul_expr),
      D.is_true_value v = false -> expr_list_equiv (YulIf (YulConst v) inst) ([]).
    Proof.
      intros v inst Hv.
      unfold expr_list_equiv.
      intros env fenv state res env' fenv' state'.
      split; intros H.
      -
        destruct H as [f Hif].
        destruct f as [|f']. inversion Hif.
        destruct f' as [|f'']. inversion Hif.
        simpl in Hif.
        rewrite Hv in Hif.
        inversion Hif. subst.
        exists 1. simpl. reflexivity.
      -
        destruct H as [f H'].
        destruct f as [|f']. inversion H'.
        simpl in H'. inversion H'. subst.
        exists 2. simpl. rewrite Hv. reflexivity.
    Qed.

    Theorem yul_for_false : forall (v : D.value_t) (post cuerpo : list yul_expr),
      D.is_true_value v = false -> expr_list_equiv (YulFor [] (YulConst v) post cuerpo) ([]).
    Proof.
      intros v post cuerpo Hv.
      unfold expr_list_equiv.
      intros env fenv state res env' fenv' state'.
      split; intros H.
      - 
        destruct H as [f Hfor].
        destruct f as [|f']. inversion Hfor.
        destruct f' as [|f'']. inversion Hfor.
        destruct f'' as [|f''']. inversion Hfor.
        simpl in Hfor.
        rewrite Hv in Hfor.
        inversion Hfor. subst.
        exists 1. simpl. reflexivity.
      - 
        destruct H as [f H'].
        destruct f as [|f']. inversion H'.
        simpl in H'. inversion H'. subst.
        exists 3. simpl. 
        rewrite Hv. reflexivity.
    Qed.

    Definition cond_equiv_true (cond : yul_expr) : Prop :=
    forall f env fenv state res env' fenv' state',
      eval_yul f cond env fenv state = (res, env', fenv', state', Sem.Yul_Running) ->
      match res with
      | v :: _ => D.is_true_value v = true
      | []     => False
      end.

    Fixpoint sin_breakcontleave (e : yul_expr) : bool :=
      match e with
      | YulBreak => false
      | YulContinue => false
      | YulLeave => false
      | YulFor ini cond post inst =>
        forallb sin_breakcontleave ini &&
        sin_breakcontleave cond &&
        forallb sin_breakcontleave post &&
        forallb sin_breakcontleave inst
      | YulIf cond inst =>
        sin_breakcontleave cond && forallb sin_breakcontleave inst
      | YulSwitch cond cases def =>
        sin_breakcontleave cond &&
        forallb (fun '(_, c) => forallb sin_breakcontleave c) cases &&
        forallb sin_breakcontleave def
      | YulOp _ args => forallb sin_breakcontleave args
      | YulLet _ v => sin_breakcontleave v
      | YulFunc _ _ _ inst => forallb sin_breakcontleave inst        
      | YulCall _ args => forallb sin_breakcontleave args
      | _ => true
      end.


    Definition sin_breakcontleave_fenv (fenv : A.yul_fun_env) : Prop :=
      forall nom func, buscar_funcion nom fenv = Some func ->
        forallb sin_breakcontleave (f_inst func) = true.

    Lemma sin_breakcontleave_fenv_cons :
      forall nom func fenv,
        forallb sin_breakcontleave (f_inst func) = true ->
        sin_breakcontleave_fenv fenv ->
        sin_breakcontleave_fenv ((nom, func) :: fenv).
    Proof.
      intros nom func fenv Hfunc Hfenv n f' Hbuscar.
      simpl in Hbuscar.
      destruct (string_dec n nom) as [Heq | Hneq].
      - inversion Hbuscar; subst. exact Hfunc.
      - exact (Hfenv n f' Hbuscar).
    Qed.

    Lemma no_breakcontleave_aux : forall f,
      (forall expr env fenv state res env' fenv' state' ctrl,
         sin_breakcontleave expr = true ->
         sin_breakcontleave_fenv fenv ->
         eval_yul f expr env fenv state = (res, env', fenv', state', ctrl) ->
         (ctrl <> Yul_Break /\ ctrl <> Yul_Continue /\ ctrl <> Yul_Leave)/\ sin_breakcontleave_fenv fenv')
      /\
      (forall l env fenv state res env' fenv' state' ctrl,
         forallb sin_breakcontleave l = true ->
         sin_breakcontleave_fenv fenv ->
         eval_list f l env fenv state = (res, env', fenv', state', ctrl) ->
         (ctrl <> Yul_Break /\ ctrl <> Yul_Continue /\ ctrl <> Yul_Leave)/\ sin_breakcontleave_fenv fenv')
      /\
      (forall args env fenv state res env' fenv' state' ctrl,
         forallb sin_breakcontleave args = true ->
         sin_breakcontleave_fenv fenv ->
         eval_argumentos f args env fenv state = (res, env', fenv', state', ctrl) ->
         (ctrl <> Yul_Break /\ ctrl <> Yul_Continue /\ ctrl <> Yul_Leave)/\ sin_breakcontleave_fenv fenv')
      /\
      (forall ini cond post cuerpo,
        forallb sin_breakcontleave ini = true ->
         sin_breakcontleave cond = true ->
         forallb sin_breakcontleave post = true ->
         forallb sin_breakcontleave cuerpo = true ->
         forall ei fei si res env' fenv' state' ctrl,
         sin_breakcontleave_fenv fei ->
         eval_yul f (YulFor [] cond post cuerpo) ei fei si =
           (res, env', fenv', state', ctrl) ->
         (ctrl <> Yul_Break /\ ctrl <> Yul_Continue /\ ctrl <> Yul_Leave)/\ sin_breakcontleave_fenv fenv')
      /\
      (forall cond cuerpo post env_orig ei fei si res env' fenv' state' ctrl,
        sin_breakcontleave cond = true ->
        forallb sin_breakcontleave cuerpo = true ->
        forallb sin_breakcontleave post = true ->
        sin_breakcontleave_fenv fei ->
        eval_bucle cond cuerpo post env_orig f ei fei si = (res, env', fenv', state', ctrl) ->
        (ctrl <> Yul_Break /\ ctrl <> Yul_Continue /\ ctrl <> Yul_Leave)/\ sin_breakcontleave_fenv fenv').
    Proof.
      intro f.
      induction f as [f IH] using (well_founded_induction Wf_nat.lt_wf).
      set (Pe := fun g => forall expr env fenv state res env' fenv' state' ctrl,
        sin_breakcontleave expr = true ->
        sin_breakcontleave_fenv fenv ->
        eval_yul g expr env fenv state = (res, env', fenv', state', ctrl) ->
        (ctrl <> Yul_Break /\ ctrl <> Yul_Continue /\ ctrl <> Yul_Leave)/\ sin_breakcontleave_fenv fenv').
      set (Pl := fun g => forall l env fenv state res env' fenv' state' ctrl,
        forallb sin_breakcontleave l = true ->
        sin_breakcontleave_fenv fenv ->
        eval_list g l env fenv state = (res, env', fenv', state', ctrl) ->
        (ctrl <> Yul_Break /\ ctrl <> Yul_Continue /\ ctrl <> Yul_Leave) /\ sin_breakcontleave_fenv fenv').
      set (Pa := fun g => forall args env fenv state res env' fenv' state' ctrl,
        forallb sin_breakcontleave args = true ->
        sin_breakcontleave_fenv fenv ->
        eval_argumentos g args env fenv state = (res, env', fenv', state', ctrl) ->
        (ctrl <> Yul_Break /\ ctrl <> Yul_Continue /\ ctrl <> Yul_Leave)/\ sin_breakcontleave_fenv fenv').
      set (Pb := fun g => forall cond cuerpo post env_orig ei fei si res env' fenv' state' ctrl,
        sin_breakcontleave cond = true ->
        forallb sin_breakcontleave cuerpo = true ->
        forallb sin_breakcontleave post = true ->
        sin_breakcontleave_fenv fei ->
        eval_bucle cond cuerpo post env_orig g ei fei si = (res, env', fenv', state', ctrl) ->
        (ctrl <> Yul_Break /\ ctrl <> Yul_Continue /\ ctrl <> Yul_Leave)/\ sin_breakcontleave_fenv fenv').
      assert (IHe : forall g, g < f -> Pe g) by (intros g Hg; exact (proj1 (IH g Hg))).
      assert (IHl : forall g, g < f -> Pl g) by (intros g Hg; exact (proj1 (proj2 (IH g Hg)))).
      assert (IHa : forall g, g < f -> Pa g) by (intros g Hg; exact (proj1 (proj2 (proj2(IH g Hg))))).
      assert (IHb: forall g, g<f ->
        forall ini cond post cuerpo,
        forallb sin_breakcontleave ini = true-> 
        sin_breakcontleave cond=true->
        forallb sin_breakcontleave post=true ->
        forallb sin_breakcontleave cuerpo= true->
        forall ei fei si res env' fenv' state' ctrl,
        sin_breakcontleave_fenv fei ->
        eval_yul g (YulFor [] cond post cuerpo) ei fei si= (res, env', fenv', state', ctrl)->
        (ctrl <> Yul_Break /\ ctrl <> Yul_Continue /\ ctrl <> Yul_Leave)/\ sin_breakcontleave_fenv fenv') by (intros g Hg; exact (proj1(proj2(proj2(proj2(IH g Hg)))))).
      assert (IHbb : forall g, g < f -> Pb g) by (intros g Hg; exact (proj2 (proj2 (proj2 (proj2((IH g Hg))))))).
      destruct f as [| f'].
      - repeat split.
        + intros. simpl in H1. inversion H1; subst. repeat split; discriminate.
        + intros. simpl in H1. inversion H1; subst. repeat split; discriminate.
        + intros. simpl in H1. inversion H1; subst. repeat split; discriminate.
        + inversion H1. subst. exact H0.
        + intros. simpl in H1. inversion H1; subst. repeat split; discriminate.
        + intros. simpl in H1. inversion H1; subst. repeat split; discriminate.
        + intros. simpl in H1. inversion H1; subst. repeat split; discriminate.
        + inversion H1. subst. exact H0.
        + intros. simpl in H1. inversion H1; subst. repeat split; discriminate.
        + intros. simpl in H1. inversion H1; subst. repeat split; discriminate.
        + intros. simpl in H1. inversion H1; subst. repeat split; discriminate.
        + inversion H1. subst. exact H0.
        + simpl in H3. inversion H4; subst. repeat split; congruence.
        + simpl in H3. inversion H4; subst. repeat split; congruence.
        + simpl in H3. inversion H4; subst. repeat split; congruence.
        + inversion H4. subst. exact H3.
        + simpl in H3. inversion H3; subst. repeat split; discriminate.
        + simpl in H3. inversion H3; subst. repeat split; discriminate.
        + simpl in H3. inversion H3; subst. repeat split; discriminate.
        + inversion H3. subst. exact H2.
      - assert (Hf' : f' < S f') by lia.
        set (IHe' := IHe f' Hf').
        set (IHl' := IHl f' Hf').
        set (IHa' := IHa f' Hf').
        set (IHb' := IHb f' Hf').
        set (IHbb' := IHbb f' Hf').
        split; [| split; [| split; [| split]]].
        + intros expr env fenv state res env' fenv' state' ctrl H H0 H1.
          destruct expr as [ v | op args | ns y | nombre_var | cond inst | cond casos def | ini cond post cuerpo | nom params rets inst | nom args | | | ];
          simpl in H, H1.
          * inversion H1; subst. split.
            ++ repeat split; discriminate.
            ++ exact H0.
          * revert H1.
            destruct (eval_argumentos f' args env fenv state) as [[[[ra ea] fea] sa] ctrla] eqn:Ha.
            intro H1.
            destruct (IHa' args env fenv state ra ea fea sa ctrla H H0 Ha) as [[Ha1 [Ha2 Ha3]] Hfea].
            destruct ctrla.
            destruct (D.execute_opcode sa op ra) as [[ro so] stso].
            destruct stso.
              ++ inversion H1. subst. split; [repeat split; assumption | exact Hfea].
              ++ inversion H1. subst. split; [repeat split; discriminate | exact Hfea].
              ++ inversion H1. subst. split; [repeat split; discriminate | exact Hfea].
              ++ inversion H1. subst. split; [repeat split; discriminate | exact Hfea].
              ++ inversion H1. subst. exfalso. apply Ha1. reflexivity.
              ++ inversion H1. subst. exfalso. apply Ha2. reflexivity.
              ++ inversion H1. subst. exfalso. apply Ha3. reflexivity.
              ++ inversion H1. subst. split; [repeat split; discriminate | exact Hfea].
          * (*YulLet*)
            revert H1.
            destruct (eval_yul f' y env fenv state) as [[[[rv ev] fev] sv] ctrlv] eqn:Hv.
            intro H1.
            destruct (IHe' y env fenv state rv ev fev sv ctrlv H H0 Hv) as [[Hv1 [Hv2 Hv3]] Hfev].
            destruct ctrlv; try congruence.
            set (opt := (fix asignar (ns0 : list string) (vs : list D.value_t) (e0 : yul_env) {struct ns0} : option yul_env :=
                  match ns0 with
                  | [] => match vs with
                          | [] => Some e0
                          | _ :: _ => None
                          end
                  | n :: ns' => match vs with
                    | [] => None
                    | v :: vs' => asignar ns' vs' ((n, v) :: e0)
                    end
                  end) ns rv ev) in H1.
            destruct opt; inversion H1; subst.
            ++ split; [repeat split; assumption | exact Hfev].
            ++ split; [repeat split; discriminate | exact Hfev].
            ++ split; inversion H1; subst;[repeat split; assumption | exact Hfev].
          * destruct (buscar_variable nombre_var env);
            inversion H1; subst; (split; [repeat split; discriminate | exact H0]).
          * destruct (andb_prop _ _ H) as [Hcond Hinst].
            revert H1.
            destruct (eval_yul f' cond env fenv state) as [[[[rc ec] fec] sc] ctrlc] eqn:Hc.
            intro H1.
            destruct (IHe' cond env fenv state rc ec fec sc ctrlc Hcond H0 Hc) as [[Hc1 [Hc2 Hc3]] Hfec].
            destruct ctrlc; try congruence.
            destruct (is_true rc).
            -- destruct (eval_list f' inst ec fec sc) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
              destruct (IHl' inst ec fec sc rb eb feb sb ctrlb Hinst Hfec Hb) as [[Hb1 [Hb2 Hb3]] Hfeb].
              destruct ctrlb; inversion H1; subst; (split; [repeat split; assumption | exact Hfeb]).
            -- inversion H1; subst; (split; [repeat split; discriminate | exact Hfec]).
            -- inversion H1; subst; (split; [repeat split; discriminate | exact Hfec]).
          * apply Bool.andb_true_iff in H. destruct H as [H_cond_casos Hdef].
            apply Bool.andb_true_iff in H_cond_casos. destruct H_cond_casos as [Hcond Hcasos].
            revert H0.
            destruct (eval_yul f' cond env fenv state) as [[[[rc ec] fec] sc] ctrlc] eqn:Hc.              intro H0.
            destruct (IHe' cond env fenv state rc ec fec sc ctrlc Hcond H0 Hc) as [[Hc1 [Hc2 Hc3]] Hfec].
            destruct ctrlc; try congruence.
            revert Hcasos H0 H1.
            induction casos as [| [vc cc] casos' IHcasos]; intros Hcasos H0.
            -- simpl in H0.
              destruct (eval_list f' def ec fec sc) as [[[[rd ed] fed] sd] ctrld] eqn:Hd.
              destruct (IHl' def ec fec sc rd ed fed sd ctrld Hdef Hfec Hd) as [[Hd1 [Hd2 Hd3]] Hfed].
              destruct ctrld; try congruence.
              ++ intro H1. inversion H1; subst. split. repeat split; assumption. exact Hfed.
              ++ intro H1. inversion H1; subst. split. repeat split; discriminate. exact Hfed.
            -- simpl in H0, Hcasos.
              apply Bool.andb_true_iff in Hcasos. destruct Hcasos as [Hcc Hcasos'].
              destruct (D.eqb (match rc with v :: _ => v | [] => D.default_value end) vc).
              ++ destruct (eval_list f' cc ec fec sc) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
                destruct (IHl' cc ec fec sc rb eb feb sb ctrlb Hcc Hfec Hb) as [[Hb1 [Hb2 Hb3]] Hfeb].
                destruct ctrlb; try congruence.
                ** intro H1. inversion H1; subst. split. repeat split; assumption. exact Hfeb.
                ** intro H1. inversion H1; subst. split. repeat split; discriminate. exact Hfeb.
              ++ exact (IHcasos Hcasos' H0).
            -- inversion H1. subst. split. repeat split; assumption. exact Hfec.
          * (*YulFor*) 
            apply Bool.andb_true_iff in H. destruct H as [H_rest Hcuerpo].
            apply Bool.andb_true_iff in H_rest. destruct H_rest as [H_rest2 Hpost].
            apply Bool.andb_true_iff in H_rest2. destruct H_rest2 as [Hini Hcond].
            revert H0.
            destruct (eval_list f' ini env fenv state) as [[[[ri ei] fei] si] ctrli] eqn:Hi.
            intro H0.
            destruct (IHl' ini env fenv state ri ei fei si ctrli Hini H0 Hi) as [[Hi1 [Hi2 Hi3]] Hfei].
            destruct ctrli; try congruence.
            -- exact (IHbb' cond cuerpo post env ei fei si res env' fenv' state' ctrl Hcond Hcuerpo Hpost Hfei H1).
            -- inversion H1; subst. split. repeat split; assumption. exact Hfei.
          * (*YulFunc*)
            inversion H1; subst. split. 
            ++ repeat split; discriminate.
            ++ apply sin_breakcontleave_fenv_cons.
              ** exact H.
              ** exact H0.
          * (* YulCall*)
            revert H1.
            destruct (eval_argumentos f' args env fenv state) as [[[[ra ea] fea] sa] ctrla] eqn:Ha.
            intro H1.
            destruct (IHa' args env fenv state ra ea fea sa ctrla H H0 Ha) as [[Ha1 [Ha2 Ha3]] Hfea].
            destruct ctrla; try congruence.
            destruct (buscar_funcion nom fea) as [func|] eqn:Hfunc.
            -- revert H1.
              destruct (eval_list f' (f_inst func) (combinar_params (f_params func) ra) fea sa) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
              intro H1.
              assert (Hfunc_sin : forallb sin_breakcontleave (f_inst func) = true) by (exact (Hfea nom func Hfunc)).
              destruct (IHl' (f_inst func) (combinar_params (f_params func) ra) fea sa rb eb feb sb ctrlb Hfunc_sin Hfea Hb) as [[Hbb1 [Hbb2 Hbb3]] Hfeb].
              destruct ctrlb.
              ++ inversion H1; subst. split. repeat split; assumption. exact Hfea.
              ++ exfalso. apply Hbb1. reflexivity.
              ++ exfalso. apply Hbb2. reflexivity.
              ++ exfalso. apply Hbb3. reflexivity.
              ++ inversion H1; subst. split. repeat split; discriminate. exact Hfea.
            -- inversion H1; subst. split. repeat split; discriminate. exact Hfea.
            -- inversion H1; subst. split. repeat split; discriminate. exact Hfea.
          * discriminate H.
          * discriminate H.
          * discriminate H.
        + intros l env fenv state res env' fenv' state' ctrl H Hfenv H0.
          destruct l as [| h t].
          * simpl in H0. inversion H0; subst. split. repeat split; discriminate. exact Hfenv.
          * simpl in H0, H.
            destruct (andb_prop _ _ H) as [Hh Ht].
            revert H0.
            destruct (eval_yul f' h env fenv state) as [[[[rh eh] feh] sh] ctrlh] eqn:Hh_eval.
            intro H0.
            destruct (IHe' h env fenv state rh eh feh sh ctrlh Hh Hfenv Hh_eval) as [[Hh1 [Hh2 Hh3]] Hfeh].
            destruct ctrlh; try congruence.
            exact (IHl' t eh feh sh res env' fenv' state' ctrl Ht Hfeh H0).
            inversion H0; subst. split. repeat split; discriminate. exact Hfeh.
        + intros args env fenv state res env' fenv' state' ctrl H Hfenv H0.
          destruct args as [| h t].
          * simpl in H0. inversion H0; subst. split. repeat split; discriminate. exact Hfenv.
          * simpl in H0, H.
            destruct (andb_prop _ _ H) as [Hh Ht].
            revert H0.
            destruct (eval_argumentos f' t env fenv state) as [[[[rt et] fet] st] ctrlt] eqn:Ht_eval.
            intro H0.
            destruct (IHa' t env fenv state rt et fet st ctrlt Ht Hfenv Ht_eval) as [[Ht1 [Ht2 Ht3]] Hfet].
            destruct ctrlt; try congruence.
            revert H0.
            destruct (eval_yul f' h et fet st) as [[[[rh eh] feh] sh] ctrlh] eqn:Hh_eval.
            intro H0.
            destruct (IHe' h et fet st rh eh feh sh ctrlh Hh Hfet Hh_eval) as [[Hh1 [Hh2 Hh3]] Hfeh].
            destruct ctrlh; try congruence;
            inversion H0; subst; (split; [repeat split; congruence | exact Hfeh]).
            inversion H0; subst. split. repeat split; assumption. exact Hfet.
        + intros ini cond post cuerpo Hini Hcond Hpost Hcuerpo ei fei si res env' fenv' state' ctrl Hfenv H0.
          simpl in H0.
          destruct f' as [| f''].
          -- simpl in H0. inversion H0; subst. split. repeat split; discriminate. exact Hfenv.
          -- simpl in H0.
             exact (IHbb' cond cuerpo post ei ei fei si res env' fenv' state' ctrl Hcond Hcuerpo Hpost Hfenv H0).
        + intros cond cuerpo post env_orig ei fei si res env' fenv' state' ctrl Hcond Hcuerpo Hpost Hfenv Heval_bucle.
          revert Heval_bucle.
          destruct (eval_yul f' cond ei fei si) as [[[[rc ec] fec] sc] ctrlc] eqn:Hc.
          intro Heval_bucle.
          destruct (IHe' cond ei fei si rc ec fec sc ctrlc Hcond Hfenv Hc) as [[Hc1 [Hc2 Hc3]] Hfec].
          destruct ctrlc; try congruence.
          destruct (is_true rc) eqn:Htrue.
          * revert Heval_bucle.
            destruct (eval_list f' cuerpo ec fec sc) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
            intro Heval_bucle.
            destruct (IHl' cuerpo ec fec sc rb eb feb sb ctrlb Hcuerpo Hfec Hb) as [[Hb1 [Hb2 Hb3]] Hfeb].
            destruct ctrlb; try congruence.
            -- (*Yul_Running*)
              revert Heval_bucle.
              destruct (eval_list f' post (restringe_env eb ec) feb sb) as [[[[rp ep] fep] sp] ctrlp] eqn:Hp.
              intro Heval_bucle.
              destruct (IHl' post (restringe_env eb ec) feb sb rp ep fep sp ctrlp Hpost Hfeb Hp) as [[Hp1 [Hp2 Hp3]] Hfep].
              destruct ctrlp; try congruence.
              ++ unfold eval_yul in Heval_bucle.
                 simpl in Heval_bucle.
                 rewrite Hc in Heval_bucle.
                 rewrite Htrue in Heval_bucle.
                 rewrite Hb in Heval_bucle.
                 rewrite Hp in Heval_bucle.
                 simpl in Heval_bucle.
                 apply IHbb' in Heval_bucle.
                 exact Heval_bucle. exact Hcond. exact Hcuerpo. exact Hpost. exact Hfep.
              ++ unfold eval_yul in Heval_bucle.
                 simpl in Heval_bucle.
                 rewrite Hc in Heval_bucle.
                 rewrite Htrue in Heval_bucle.
                 rewrite Hb in Heval_bucle.
                 rewrite Hp in Heval_bucle.
                 simpl in Heval_bucle.
                 inversion Heval_bucle; subst.
                 split. repeat split; assumption. exact Hfeb.
            --  unfold eval_yul in Heval_bucle.
                simpl in Heval_bucle.
                rewrite Hc in Heval_bucle.
                rewrite Htrue in Heval_bucle.
                rewrite Hb in Heval_bucle.
                simpl in Heval_bucle.
                inversion Heval_bucle; subst.
                split. repeat split; assumption. exact Hfeb.
          * unfold eval_yul in Heval_bucle.
            simpl in Heval_bucle.
            rewrite Hc in Heval_bucle.
            rewrite Htrue in Heval_bucle.
            inversion Heval_bucle; subst. 
            split. repeat split; discriminate. exact Hfec.
          * unfold eval_yul in Heval_bucle.
            simpl in Heval_bucle.
            rewrite Hc in Heval_bucle.
            inversion Heval_bucle; subst. split. repeat split; assumption. exact Hfec.
    Qed.
 
    Lemma no_breakcontleave_list :
      forall f l env fenv state res env' fenv' state' ctrl,
        forallb sin_breakcontleave l = true ->
        sin_breakcontleave_fenv fenv ->
        eval_list f l env fenv state = (res, env', fenv', state', ctrl) ->
        ctrl <> Yul_Break /\ ctrl <> Yul_Continue /\ ctrl <> Yul_Leave.
    Proof.
      intros f l env fenv state res env' fenv' state' ctrl Hsinb Hfenv Heval.
      exact (proj1 (proj1(proj2 (no_breakcontleave_aux f)) l env fenv state res env' fenv' state' ctrl Hsinb Hfenv Heval)).
    Qed.
    
    Lemma sin_breakcontleave_fenv_vacio : sin_breakcontleave_fenv [].
    Proof.
      unfold sin_breakcontleave_fenv.
      intros nom func Hbuscar.
      simpl in Hbuscar. 
      inversion Hbuscar.  
    Qed.

    Lemma eval_list_vacia :
    forall f env fenv state,
      f>0 ->
      eval_list f [] env fenv state = ([], env, fenv, state, Yul_Running).
    Proof.
      intros f env fenv state.
      destruct f; unfold eval_list. lia. reflexivity.
    Qed.

    Lemma bucle_no_running :
    forall cond post cuerpo, 
      cond_equiv_true cond ->
      sin_breakcontleave cond = true -> 
      forallb sin_breakcontleave cuerpo = true ->
      forallb sin_breakcontleave post = true ->
      forall n env e fe s res env' fenv' state',
      sin_breakcontleave_fenv fe ->
        eval_bucle cond cuerpo post env n e fe s = (res, env', fenv', state', Yul_Running) -> False.
    Proof.
      intros cond post cuerpo Hcond_equiv Hcond_sin Hcuerpo Hpost.
      induction n as [|n IH]; intros env e fe s res env' fenv' state' He Heval.
      - simpl in Heval. inversion Heval.
      - cbn [eval_bucle] in Heval.
        destruct (no_breakcontleave_aux n) as [Pe [Pl _]].
        revert Heval.
        destruct (eval_yul n cond e fe s) as [[[[rc ec] fec] sc] ctrlc] eqn: Hc.
        intro Heval.
        cbn in Heval.
        destruct ctrlc; try inversion Heval.
        destruct (Pe cond e fe s rc ec fec sc Yul_Running Hcond_sin He Hc) as [_ Hfec].
        pose proof (Pe cond e fe s rc ec fec sc Yul_Running Hcond_sin He Hc) as HPe.
        pose proof (Hcond_equiv n e fe s rc ec fec sc Hc) as Htrue.
        assert (Htrue': is_true rc=true).
        {destruct rc as [|v t]; simpl in *.
          - contradiction.
          - exact Htrue. }
        rewrite Htrue' in Heval.
        revert Heval.
        destruct (eval_list n cuerpo ec fec sc) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
        intro Heval. simpl in Heval.
        destruct (Pl cuerpo ec fec sc rb eb feb sb ctrlb Hcuerpo Hfec Hb) as [[Hb1 [Hb2 Hb3]] Hfeb].
        destruct ctrlb.
        + revert Heval.
          destruct (eval_list n post (restringe_env eb ec) feb sb) as [[[[rp ep] fep] sp] ctrlp] eqn:Hp.
          intro Heval. simpl in Heval.
          destruct (Pl post (restringe_env eb ec) feb sb rp ep fep sp ctrlp Hpost Hfeb Hp) as [[Hp1 [Hp2 Hp3]] Hfep].
          destruct ctrlp.
          * exact (IH env (restringe_env ep (restringe_env eb ec)) fep sp res env' fenv' state' Hfep Heval).
          * exfalso. apply Hp1. reflexivity.
          * exfalso. apply Hp2. reflexivity.
          * exfalso. apply Hp3. reflexivity.
          * inversion Heval.
        + exfalso. apply Hb1. reflexivity.
        + exfalso. apply Hb2. reflexivity.
        + exfalso. apply Hb3. reflexivity.
        + inversion Heval.
    Qed.

    Theorem yul_while_true_no_running :
      forall f cond post cuerpo, 
        cond_equiv_true cond ->
        sin_breakcontleave cond = true ->
        forallb sin_breakcontleave cuerpo = true ->
        forallb sin_breakcontleave post = true ->
        forall env state res env' fenv' state',
          eval_yul f (YulFor [] cond post cuerpo) env [] state = (res, env', fenv', state', Yul_Running) -> False.
    Proof.
      intros [|f1] cond post cuerpo Hcond Hcond' Hcuerpo Hpost env state res env' fenv' state' Heval.
      - simpl in Heval. inversion Heval.
      - simpl in Heval.
        destruct f1 as [|f2].
        + simpl in Heval. inversion Heval.
        + rewrite (eval_list_vacia (S f2) env [] state) in Heval; [| lia].
          eapply (bucle_no_running cond post cuerpo Hcond Hcond' Hcuerpo Hpost (S f2) env env [] state res env' fenv' state').
          * exact sin_breakcontleave_fenv_vacio.
          * exact Heval.
    Qed.


End YulEquivalences.