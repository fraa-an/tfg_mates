From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import LenguajeYul.dialect.
Require Import main.ast.
Require Import main.semantica.

Module YulHoare (D : DIALECT) (A : AST_INTERFACE D).
    Module Sem := YulSemantica D A.
    Import A.
    Import Sem.

    Definition Assertion := A.yul_env -> A.yul_fun_env -> D.dialect_state_t -> Prop.
    Definition assert_implies (P Q : Assertion) : Prop :=
      forall env fenv state, P env fenv state -> Q env fenv state.
    Notation "P ->> Q" := (assert_implies P Q) (at level 80).
    Notation "P <<->> Q" := (P->>Q  /\ Q->>P) (at level 80).

    Definition hoare_triple (P : Assertion) (e : A.yul_expr) (Q : Assertion) : Prop :=
    forall f env fenv state res env' fenv' state', eval_yul f e env fenv state = (res, env', fenv', state', Yul_Running) ->
      P env fenv state -> Q env' fenv' state'.

    Definition hoare_triple_list (P : Assertion) (l : list A.yul_expr) (Q : Assertion) : Prop :=
    forall f env fenv state res env' fenv' state',
      eval_list f l env fenv state = (res, env', fenv', state', Yul_Running) ->
      P env fenv state -> Q env' fenv' state'.

    Notation "{{ P }} e {{ Q }}" := (hoare_triple P e Q) (at level 90, e at next level).
    Notation "{{{ P }}} l {{{ Q }}}" := (hoare_triple_list P l Q) (at level 90, l at next level).
    
    Theorem hoare_empty_list : forall (P : Assertion),
      {{{ P }}} [] {{{ P }}}.
    Proof.
      intros P. unfold hoare_triple_list.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      destruct f as [|f'].
      - simpl in Heval. inversion Heval.
      - simpl in Heval. inversion Heval. subst.
        exact Hpre.
    Qed.

    Theorem hoare_seq : forall (P Q R : Assertion) e l,
      {{ P }} e {{ Q }} ->
      {{{ Q }}} l {{{ R }}} ->
    	{{{ P }}} e :: l {{{ R }}}.
    Proof.
      intros P Q R e l H_e H_l.
      unfold hoare_triple, hoare_triple_list in *.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      destruct f as [|f'].
      - simpl in Heval. inversion Heval.
      - simpl in Heval.
          destruct (eval_yul f' e env fenv state) as [[[[res_e env_e] fenv_e] state_e] ctrl_e] eqn:Heval_e.  
          destruct ctrl_e; try (inversion Heval).
          assert (HQ : Q env_e fenv_e state_e). { apply (H_e f' env fenv state res_e env_e fenv_e state_e); eauto. }
          apply (H_l f' env_e fenv_e state_e res env' fenv' state'); eauto.
    Qed.

    Definition ValAssertion := list D.value_t -> A.yul_env -> A.yul_fun_env -> D.dialect_state_t -> Prop.

    Definition hoare_triple_val (P : Assertion) (e : A.yul_expr) (Q : ValAssertion) : Prop :=
    forall f env fenv state res env' fenv' state',
      eval_yul f e env fenv state = (res, env', fenv', state', Yul_Running) ->
      P env fenv state ->
      Q res env' fenv' state'.

    Notation "<< P >> e << Q >>" := (hoare_triple_val P e Q) (at level 90, e at next level).

    Fixpoint asignar_vars (ns : list string) (vs : list D.value_t) (e : A.yul_env) : option A.yul_env :=
      match ns, vs with
      | [], [] => Some e
      | n::ns', v::vs' => asignar_vars ns' vs' ((n, v) :: e)
      | _, _ => None
      end.

    Lemma asignar_equiv : forall (ns : list string) (vs : list D.value_t) (e : yul_env),
    (fix asignar (ns0 : list string) (vs0 : list D.value_t) (e0 : yul_env) {struct ns0} : option yul_env :=
      match ns0 with
      | [] => match vs0 with
              | [] => Some e0
              | _ :: _ => None
              end
      | n :: ns' =>
          match vs0 with
          | [] => None
          | v :: vs' => asignar ns' vs' ((n, v) :: e0)
			    end
      end) ns vs e = asignar_vars ns vs e.
    Proof.
    induction ns as [|n ns' IH]; intros [|v vs'] e; simpl; auto.
    Qed.

    Theorem hoare_let : forall (P : Assertion) (Q : Assertion) nombres valor (R : ValAssertion),
      << P >> valor << R >> ->
      (forall res env fenv state, R res env fenv state -> 
          match asignar_vars nombres res env with
	       	| Some nuevo_env => Q nuevo_env fenv state
          | None => False
          end) ->
      {{ P }} YulLet nombres valor {{ Q }}.
    Proof.
      intros P Q nombres valor R Hvalor Hassign.
      unfold hoare_triple, hoare_triple_val in *.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      destruct f as [|f'].
			- simpl in Heval. inversion Heval.
      - simpl in Heval.
        destruct (eval_yul f' valor env fenv state) as [[[[valores env_i] fenv_i] state_i] st] eqn:Heval'.
        destruct st; try discriminate.
        assert (HR : R valores env_i fenv_i state_i).
				eapply Hvalor; eauto.
        pose proof (Hassign valores env_i fenv_i state_i HR) as Hmatch.
        destruct (asignar_vars nombres valores env_i) as [nuevo_env |] eqn:Hv.
      	+ rewrite asignar_equiv in Heval.
          rewrite Hv in Heval.
          inversion Heval; subst.
          exact Hmatch.
        + contradiction.
    Qed.

    Definition assertion_sub (X : string) (v : D.value_t) (Q : Assertion) : Assertion :=
      fun env fenv state => Q ((X, v) :: env) fenv state.

    Notation "Q '[' X '|->' v ']'" := (assertion_sub X v Q) (at level 10, X at next level).

    Definition assertion_sub_op (X : string) (f : D.value_t -> D.value_t) (Q : Assertion) : Assertion :=
      fun env fenv state => 
        match buscar_variable X env with
        | Some v => Q ((X, f v) :: env) fenv state
        | None => False
        end.

    Theorem hoare_consequence : forall (P P' Q Q' : Assertion) e,
      {{ P' }} e {{ Q' }} ->
      P ->> P' ->
      Q' ->> Q ->
      {{ P }} e {{ Q }}.
    Proof.
      intros P P' Q Q' e H HP HQ.
      unfold hoare_triple.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      apply HQ.
      apply (H f env fenv state res env' fenv' state').
      - exact Heval.
      - apply HP. exact Hpre.
    Qed.

    Theorem hoare_consequence_pre : forall (P P' Q : Assertion) e,
      {{ P' }} e {{ Q }} ->
      P ->> P' ->
      {{ P }} e {{ Q }}.
    Proof.
      intros P P' Q e H' H''.
      apply hoare_consequence with (P' := P') (Q' := Q); auto.
      intros env fenv state H. exact H.
    Qed.

    Theorem hoare_consequence_post : forall (P Q Q' : Assertion) e,
      {{ P }} e {{ Q' }} ->
      Q' ->> Q ->
      {{ P }} e {{ Q }}.
    Proof.
      intros P Q Q' e H' H''.
      apply hoare_consequence with (P' := P) (Q' := Q'); auto.
      intros env fenv state H. exact H.
    Qed.

    Theorem hoare_if : forall P Q (R : ValAssertion) cond inst,
      << P >> cond << R >> ->
      (forall res env fenv state, R res env fenv state -> is_true res = true ->
      {{{ fun e fe s => R res e fe s }}} inst {{{ fun e' fe' s' => Q (restringe_env e' env) fe' s' }}}) ->
      (forall res env fenv state, R res env fenv state -> is_true res = false -> Q env fenv state) ->
     	{{ P }} YulIf cond inst {{ Q }}.
    Proof.
      intros P Q R cond inst Hcond Htrue Hfalse.
      unfold hoare_triple, hoare_triple_list, hoare_triple_val in *.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      destruct f as [|f'].
      - simpl in Heval. inversion Heval.
      - simpl in Heval.
        destruct (eval_yul f' cond env fenv state) as [[[[res_c env_c] fenv_c] state_c] st_c] eqn:Heval_c.
        destruct st_c; try discriminate.
        assert (HR : R res_c env_c fenv_c state_c).
        eapply Hcond; eauto.
        destruct (is_true res_c) eqn:Hbool.
        destruct (eval_list f' inst env_c fenv_c state_c) as [[[[res_i env_i] fenv_i] state_i] st_i] eqn:Heval_i.
        destruct st_i; inversion Heval; subst.
        eapply Htrue; eauto.
        inversion Heval; subst.
        apply (Hfalse res_c env' fenv' state'); auto.
    Qed.

		Theorem hoare_const : forall (P : Assertion) (v : D.value_t),
      << P >> YulConst v << fun res env fenv state => res = [v] /\ P env fenv state >>.
    Proof.
			intros P v.
			unfold hoare_triple_val.
			intros f env fenv state res env' fenv' state' Heval Hpre.
			destruct f.
			- simpl in Heval. inversion Heval.
      - simpl in Heval. inversion Heval. subst. split. reflexivity. exact Hpre.
    Qed.


		Theorem hoare_var : forall (P : Assertion) nom,
      (forall env fenv state, P env fenv state ->
         exists v, buscar_variable nom env = Some v) ->
      << P >> YulVar nom << fun res env fenv state =>
          P env fenv state /\
          buscar_variable nom env = Some (hd D.default_value res) >>.
    Proof.
			intros P nom H.
			unfold hoare_triple_val.
			intros f env fenv state res env' fenv' state' Heval Hpre.
			destruct f.
			- simpl in Heval. inversion Heval.
			- simpl in Heval. destruct (buscar_variable nom env) eqn: Hbuscar.
				+ inversion Heval; subst. split. exact Hpre. exact Hbuscar.
				+ inversion Heval.
		Qed.

		Theorem hoare_func : forall (P : Assertion) nom params rets inst,
      {{ P }} YulFunc nom params rets inst  {{ fun env fenv state =>
           P env (tl fenv) state /\
           fenv = (nom, {| f_params := params; f_ret := rets; f_inst := inst |}) :: tl fenv }}.
    Proof.
      intros P nom params rets inst.
      unfold hoare_triple.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      destruct f; simpl in Heval; inversion Heval; subst.
      split. exact Hpre. simpl. reflexivity.
    Qed.
		
		Theorem hoare_call : forall (P : Assertion) (nom : string) (args : list yul_expr) (Q : Assertion),
			(forall f env fenv state vals env_a fenv_a state_a,
				eval_argumentos f args env fenv state = (vals, env_a, fenv_a, state_a, Yul_Running) ->
				P env fenv state ->
				match buscar_funcion nom fenv_a with
				| Some func =>
						forall env_post fenv_post state_post st_post res_func,
						eval_list f (f_inst func) (combinar_params (f_params func) vals) fenv_a state_a = (res_func, env_post, fenv_post, state_post, st_post) ->
						(st_post = Yul_Running \/ st_post = Yul_Leave) ->
						Q env_a fenv_a state_post
				| None => False
				end) ->
			{{ P }} YulCall nom args {{ Q }}.
		Proof.
			intros P nom args Q H.
			unfold hoare_triple.
			intros f env fenv state res env' fenv' state' Heval Hpre.
			destruct f as [|f']; simpl in Heval; [discriminate|].
			destruct (eval_argumentos f' args env fenv state) as [[[[vals env_a] fenv_a] state_a] st_args] eqn:Hargs.
			destruct st_args; try discriminate.
			assert (H_call := H f' env fenv state vals env_a fenv_a state_a Hargs Hpre).
			destruct (buscar_funcion nom fenv_a) as [func|] eqn:Hfunc; [|contradiction].
			destruct (eval_list f' (f_inst func) (combinar_params (f_params func) vals) fenv_a state_a) as [[[[res_func env_post] fenv_post] state_post] st_post] eqn:Hlist.
			destruct st_post; inversion Heval; subst.
			- eapply H_call; eauto.
			- eapply H_call; eauto.
		Qed.
		
    Theorem hoare_switch : forall (P Q : Assertion) (R : ValAssertion)
      cond casos def,
      << P >> cond << R >> ->
      (forall val_caso cuerpo_caso,
        In (val_caso, cuerpo_caso) casos ->
        forall res env_c fenv_c state_c,
          R res env_c fenv_c state_c ->
          D.eqb (hd D.default_value res) val_caso = true ->
          {{{ fun e fe s => R res e fe s }}} cuerpo_caso {{{ fun e' fe' s' => Q (restringe_env e' env_c) fe' s' }}}) ->
       
      (forall res env_c fenv_c state_c,
        R res env_c fenv_c state_c ->
        forallb (fun '(vc, _) => negb (D.eqb (hd D.default_value res) vc)) casos = true ->
        {{{ fun e fe s => R res e fe s }}} def {{{ fun e' fe' s' => Q (restringe_env e' env_c) fe' s' }}}) ->

      {{ P }} YulSwitch cond casos def {{ Q }}.
    Proof.
      intros P Q R cond casos def Hcond Hcasos Hdef.
      unfold hoare_triple, hoare_triple_list, hoare_triple_val in *.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      destruct f.
      + simpl in Heval. inversion Heval.
      + simpl in Heval.   
        destruct (eval_yul f cond env fenv state) as [[[[res_c env_c] fenv_c] state_c] st_c] eqn:Heval_c.
        destruct st_c; try discriminate.
        assert (H : R res_c env_c fenv_c state_c).
        {eapply Hcond. eauto. exact Hpre. }
        set (v_eval := match res_c with v :: _ => v | [] => D.default_value end).
        assert (Hdef_c : forallb (fun '(vc, _) => negb (D.eqb v_eval vc)) casos = true ->
          {{{ fun e fe s => R res_c e fe s }}} def {{{ fun e' fe' s' => Q (restringe_env e' env_c) fe' s' }}}).
        { intros H' f0 env0 fenv0 state0 res0 env0' fenv0' state0' Heval0 H0. eapply Hdef; eauto. }
        clear Hdef.
        revert Hcasos Hdef_c Heval.
        induction casos as [| [vc cc] casos' IHcasos]; intros Hcasos Hdef_c Heval.
        - destruct (eval_list f def env_c fenv_c state_c) as [[[[rd ed] fed] sd] ctrld] eqn:Hd.
          destruct ctrld; inversion Heval; subst.
          eapply Hdef_c; eauto.
        - destruct (D.eqb v_eval vc) eqn:Hmatch.
          ** destruct (eval_list f cc env_c fenv_c state_c) as [[[[rc ec] fec] sc] ctrc] eqn:Hcc.
            destruct ctrc; inversion Heval; subst.
            change (match res_c with | [] => D.default_value | v :: _ => v end) with v_eval in Heval.
            rewrite Hmatch in Heval.
            inversion Heval; subst.
            eapply Hcasos; eauto.
            ++ left. reflexivity.
            ++ change (match res_c with | [] => D.default_value | v :: _ => v end) with v_eval in Heval.
               rewrite Hmatch in Heval.
               discriminate Heval.
            ++ change (match res_c with | [] => D.default_value | v :: _ => v end) with v_eval in Heval.
               rewrite Hmatch in Heval.
               discriminate Heval.
            ++ change (match res_c with | [] => D.default_value | v :: _ => v end) with v_eval in Heval.
               rewrite Hmatch in Heval.
               discriminate Heval.
            ++ change (match res_c with | [] => D.default_value | v :: _ => v end) with v_eval in Heval.
               rewrite Hmatch in Heval.
               discriminate Heval.
          ** apply IHcasos.
            ++ intros val_caso cuerpo_caso H_caso; intros.
               eapply Hcasos; eauto. right. exact H_caso. 
            ++ intros Hf.
               apply Hdef_c.
               simpl.
               rewrite Hmatch. simpl.
               exact Hf.
            ++ change (match res_c with | [] => D.default_value | v :: _ => v end) with v_eval in Heval.
               rewrite Hmatch in Heval.
               exact Heval.
    Qed.

    Lemma hoare_bucle : forall (I Q : Assertion) cond cuerpo post,
      (forall f e fe s rc ec fec sc,
          I e fe s ->
          eval_yul f cond e fe s = (rc, ec, fec, sc, Yul_Running) ->
          I ec fec sc) ->
      (* cond = false *)
      (forall f e fe s rc ec fec sc,
          I e fe s ->
          eval_yul f cond e fe s = (rc, ec, fec, sc, Yul_Running) ->
          is_true rc = false ->
          Q ec fec sc) ->
      (* break en cuerpo *)
      (forall f env_orig rc ec fec sc rb eb feb sb,
          I ec fec sc ->
          is_true rc = true ->
          eval_list f cuerpo ec fec sc = (rb, eb, feb, sb, Yul_Break) ->
          Q (restringe_env (restringe_env eb ec) env_orig) feb sb) ->
      (* break en post *)
      (forall f env_orig rc ec fec sc rb eb feb sb rp ep fep sp ctrlb,
          I ec fec sc ->
          is_true rc = true ->
          (ctrlb = Yul_Running \/ ctrlb = Yul_Continue) ->
          eval_list f cuerpo ec fec sc = (rb, eb, feb, sb, ctrlb) ->
          eval_list f post (restringe_env eb ec) feb sb = (rp, ep, fep, sp, Yul_Break) ->
          Q (restringe_env (restringe_env eb ec) env_orig) feb sb) ->
      (forall f e_i fe_i s_i rc ec fec sc rb eb feb sb rp ep fep sp ctrlb ctrlp,
          I e_i fe_i s_i ->
          eval_yul f cond e_i fe_i s_i = (rc, ec, fec, sc, Yul_Running) ->
          is_true rc = true ->
          (ctrlb = Yul_Running \/ ctrlb = Yul_Continue) ->
          eval_list f cuerpo ec fec sc = (rb, eb, feb, sb, ctrlb) ->
          eval_list f post (restringe_env eb ec) feb sb = (rp, ep, fep, sp, ctrlp) ->
          (ctrlp = Yul_Running \/ ctrlp = Yul_Continue) ->
          I (restringe_env ep (restringe_env eb ec)) fep sp) ->
      forall n env_orig e fe s res env' fenv' state',
        I e fe s ->
        eval_bucle cond cuerpo post env_orig n e fe s =
          (res, env', fenv', state', Yul_Running) ->
        Q env' fenv' state'.
    Proof.
      intros I Q cond cuerpo post Hcond_inv Hfalse Hbreak_b Hbreak_p Hpaso.
      induction n as [|n IHn];
        intros env_orig e fe s res env' fenv' state' HI Heval.
      - simpl in Heval. inversion Heval.
      - cbn [eval_bucle] in Heval.
        destruct (eval_yul n cond e fe s) as [[[[rc ec] fec] sc] ctrlc] eqn:Hc.
        destruct ctrlc; try inversion Heval.
        assert (HIec : I ec fec sc) by (eapply Hcond_inv; eauto).
        revert Heval.
        destruct (is_true rc) eqn:Hrc; intro Heval.
        + destruct (eval_list n cuerpo ec fec sc) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
          destruct ctrlb.
          * destruct (eval_list n post (restringe_env eb ec) feb sb) as [[[[rp ep] fep] sp] ctrlp] eqn:Hp.
            destruct ctrlp.
            -- assert (HI' : I (restringe_env ep (restringe_env eb ec)) fep sp).
               { eapply (Hpaso n e fe s rc ec fec sc rb eb feb sb rp ep fep sp Yul_Running Yul_Running);
                 eauto. }
               eapply IHn; eauto.
            -- inversion Heval; subst.
               exact (Hbreak_p n env_orig rc ec fec sc rb eb fenv' state' rp ep fep sp Yul_Running HIec Hrc (or_introl eq_refl) Hb Hp).
            -- apply (IHn env_orig (restringe_env ep (restringe_env eb ec)) fep sp res env' fenv' state').
              ** exact (Hpaso n e fe s rc ec fec sc rb eb feb sb rp ep fep sp Yul_Running Yul_Continue HI   Hc Hrc (or_introl eq_refl) Hb Hp (or_intror eq_refl)).
              ** exact Heval.
            -- inversion Heval.
            -- inversion Heval.
          * inversion Heval; subst.
            exact (Hbreak_b n env_orig rc ec fec sc rb eb fenv' state' HIec Hrc Hb).
          * destruct (eval_list n post (restringe_env eb ec) feb sb) as [[[[rp ep] fep] sp] ctrlp] eqn:Hp.
            destruct ctrlp.
            -- apply (IHn env_orig (restringe_env ep (restringe_env eb ec)) fep sp res env' fenv' state').
               exact (Hpaso n e fe s rc ec fec sc rb eb feb sb rp ep fep sp Yul_Continue Yul_Running HI Hc Hrc (or_intror eq_refl) Hb Hp (or_introl eq_refl)).
               exact Heval.
            -- inversion Heval; subst.
               exact (Hbreak_p n env_orig rc ec fec sc rb eb fenv' state' rp ep fep sp Yul_Continue HIec Hrc (or_intror eq_refl) Hb Hp).
            -- apply (IHn env_orig (restringe_env ep (restringe_env eb ec)) fep sp res env' fenv' state').
               exact (Hpaso n e fe s rc ec fec sc rb eb feb sb rp ep fep sp Yul_Continue Yul_Continue HI Hc Hrc (or_intror eq_refl) Hb Hp (or_intror eq_refl)).
               exact Heval.
            -- inversion Heval.
            -- inversion Heval.
          * inversion Heval.
          * inversion Heval.
        + inversion Heval; subst.
          exact (Hfalse n e fe s rc env' fenv' state' HI Hc Hrc). 
    Qed.
      
 
    Theorem hoare_for : forall (P I Q : Assertion)
      init cond post cuerpo,
      {{{ P }}} init {{{ I }}} ->
      (*Hcond*)
      (forall f e fe s rc ec fec sc,
          I e fe s ->
          eval_yul f cond e fe s = (rc, ec, fec, sc, Yul_Running) ->
          I ec fec sc) ->
      (*Hfalse*)
      (forall f e fe s rc ec fec sc,
          I e fe s ->
          eval_yul f cond e fe s = (rc, ec, fec, sc, Yul_Running) ->
          is_true rc = false ->
          Q ec fec sc) ->
      (*Hbreak*)
      (forall f env_orig rc ec fec sc rb eb feb sb,
          I ec fec sc ->
          is_true rc = true ->
          eval_list f cuerpo ec fec sc = (rb, eb, feb, sb, Yul_Break) ->
          Q (restringe_env (restringe_env eb ec) env_orig) feb sb) ->
      (*Hbreak'*)
      (forall f env_orig rc ec fec sc rb eb feb sb rp ep fep sp ctrlb,
          I ec fec sc ->
          is_true rc = true ->
          (ctrlb = Yul_Running \/ ctrlb = Yul_Continue) ->
          eval_list f cuerpo ec fec sc = (rb, eb, feb, sb, ctrlb) ->
          eval_list f post (restringe_env eb ec) feb sb = (rp, ep, fep, sp, Yul_Break) ->
          Q (restringe_env (restringe_env eb ec) env_orig) feb sb) ->
      (*H'*)
      (forall f e_i fe_i s_i rc ec fec sc rb eb feb sb rp ep fep sp ctrlb ctrlp,
          I e_i fe_i s_i ->
          eval_yul f cond e_i fe_i s_i = (rc, ec, fec, sc, Yul_Running) ->
          is_true rc = true ->
          (ctrlb = Yul_Running \/ ctrlb = Yul_Continue) ->
          eval_list f cuerpo ec fec sc = (rb, eb, feb, sb, ctrlb) ->
          eval_list f post (restringe_env eb ec) feb sb = (rp, ep, fep, sp, ctrlp) ->
          (ctrlp = Yul_Running \/ ctrlp = Yul_Continue) ->
          I (restringe_env ep (restringe_env eb ec)) fep sp) ->
      {{ P }} YulFor init cond post cuerpo {{ Q }}.
    Proof.
      intros P I Q init cond post cuerpo H Hcond Hfalse Hbreak Hbreak' H'.
      unfold hoare_triple, hoare_triple_list in *.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      destruct f.
      + simpl in Heval; inversion Heval.
      + simpl in Heval; inversion Heval.
        destruct (eval_list f init env fenv state) as [[[[ri ei] fei] si] ctrli] eqn:Hi.
        destruct ctrli; try inversion Heval.
        assert (HI : I ei fei si) by (eapply H; eauto).
        eapply hoare_bucle; eauto.
    Qed.
      
	End YulHoare.