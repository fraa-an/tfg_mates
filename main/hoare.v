From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import LenguajeYul.dialect.
Require Import main.ast.
Require Import main.semantica.

Module YulHoare (D : DIALECT) (A : AST_INTERFACE D).
    Import A.
    Module Sem := YulSemantica D A.
    Import Sem.

    (* Precondición o postcondición en la Lógica de Hoare.*)
    Definition Assertion := A.yul_env -> A.yul_fun_env -> D.dialect_state_t -> Prop.
    
    (* Implicación lógica entre aserciones (P implica Q). *)
    Definition assert_implies (P Q : Assertion) : Prop :=
      forall env fenv state, P env fenv state -> Q env fenv state.
    Notation "P ->> Q" := (assert_implies P Q) (at level 80).
    Notation "P <<->> Q" := (P->>Q  /\ Q->>P) (at level 80).

    (* Terna de Hoare tradicional: {{ P }} e {{ Q }} *)
    Definition hoare_triple (P : Assertion) (e : A.yul_expr) (Q : Assertion) : Prop :=
    forall f env fenv state res env' fenv' state', eval_yul f e env fenv state false = (res, env', fenv', state', Yul_Running) ->
      P env fenv state -> Q env' fenv' state'.

    (* Equivalente a hoare_triple pero para una lista de instrucciones *)
    Definition hoare_triple_list (P : Assertion) (l : list A.yul_expr) (Q : Assertion) : Prop :=
    forall f env fenv state res env' fenv' state',
      eval_list f l env fenv state false = (res, env', fenv', state', Yul_Running) ->
      P env fenv state -> Q env' fenv' state'.

    Notation "{{ P }} e {{ Q }}" := (hoare_triple P e Q) (at level 90, e at next level).
    Notation "{{{ P }}} l {{{ Q }}}" := (hoare_triple_list P l Q) (at level 90, l at next level).
    
    (* Un bloque vacío no altera el estado, por lo que P se mantiene. *)
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

    (* Regla de composición secuencial *)
    Theorem hoare_seq : forall (P Q R : Assertion) e l,
      {{ P }} e {{ Q }} ->
      {{{ Q }}} l {{{ R }}} ->
    	{{{ P }}} e :: l {{{ R }}}.
    Proof.
      intros P Q R e l H_e H_l.
      unfold hoare_triple, hoare_triple_list in *.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      destruct f as [|f'].
      - (* sin combustible *)
        simpl in Heval. inversion Heval.
      - simpl in Heval.
        destruct (eval_yul f' e env fenv state false) as [[[[res_e env_e] fenv_e] state_e] ctrl_e] eqn:Heval_e.  
        (* 'e' terminó correctamente (con Running), si no, descartamos *)
        destruct ctrl_e; try (inversion Heval).
        (* Usando hipótesis de 'e', probamos que el estado intermedio cumple Q *)
        assert (HQ : Q env_e fenv_e state_e). { apply (H_e f' env fenv state res_e env_e fenv_e state_e); eauto. }
        (* Con el estado Q asegurado, aplicamos la hipótesis de 'l' para llegar a R *)
        apply (H_l f' env_e fenv_e state_e res env' fenv' state'); eauto.
    Qed.

    Definition ValAssertion := list D.value_t -> A.yul_env -> A.yul_fun_env -> D.dialect_state_t -> Prop.

    (* Terna de Hoare para expresiones que devuelven valores: << P >> e << Q >>*)
    Definition hoare_triple_val (P : Assertion) (e : A.yul_expr) (Q : ValAssertion) : Prop :=
    forall f env fenv state res env' fenv' state',
      eval_yul f e env fenv state false = (res, env', fenv', state', Yul_Running) ->
      P env fenv state ->
      Q res env' fenv' state'.
    Notation "<< P >> e << Q >>" := (hoare_triple_val P e Q) (at level 90, e at next level).


    (*Regla de Hoare para declaraciones*)
    Theorem hoare_let : forall (P : Assertion) (Q : Assertion) nombres valor (R : ValAssertion),
      << P >> valor << R >> ->
      (forall res env fenv state, R res env fenv state -> 
          match agregar_vars nombres res env with
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
        revert Heval.
        (* Evaluamos el 'valor' que queremos asignar *)
        destruct (eval_yul f' valor env fenv state false) as [[[[valores env_i] fenv_i] state_i] st] eqn:Heval'.
        intro Heval.
        destruct st; try discriminate.
        (* precondición R sobre los valores evaluados *)
        assert (HR : R valores env_i fenv_i state_i).
				eapply Hvalor; eauto.
        (* garantía (Hmatch) de que si añadimos las variables al entorno, se cumplirá Q *)
        pose proof (Hassign valores env_i fenv_i state_i HR) as Hmatch.
        revert Heval.
        (* inyección de las variables en la memoria de Coq *)
        destruct (agregar_vars nombres valores env_i) as [nuevo_env |] eqn:Hv.
        intro Heval.
      	+ (* inyección fue exitosa: el número de variables coincide con el de valores *)
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

    (* Regla de la consecuencia *)
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

    (*Regla de Hoare para condicionales*)
    Theorem hoare_if : forall P Q (R : ValAssertion) cond inst,
      << P >> cond << R >> ->
      (forall res env fenv state, R res env fenv state -> is_true res = true ->
      {{{ fun e fe s => e = abrir_entorno_vars env /\ fe = hoist_funcs inst (abrir_entorno_funcs fenv) /\ s = state }}} inst {{{ fun e' fe' s' => Q (cerrar_entorno_vars e') (cerrar_entorno_funcs fe') s' }}}) ->
      (forall res env fenv state, R res env fenv state -> is_true res = false -> Q env fenv state) ->
     	{{ P }} YulIf cond inst {{ Q }}.
    Proof.
      intros P Q R cond inst Hcond Htrue Hfalse.
      unfold hoare_triple, hoare_triple_list, hoare_triple_val in *.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      destruct f as [|f'].
      - simpl in Heval. inversion Heval.
      - simpl in Heval.
        destruct (eval_yul f' cond env fenv state false) as [[[[res_c env_c] fenv_c] state_c] st_c] eqn:Heval_c.
        destruct st_c; try discriminate.
        assert (HR : R res_c env_c fenv_c state_c).
        eapply Hcond; eauto.
        destruct (is_true res_c) eqn:Hbool.
        destruct (eval_list f' inst (abrir_entorno_vars env_c) (hoist_funcs inst (abrir_entorno_funcs fenv_c)) state_c false) as [[[[res_i env_i] fenv_i] state_i] st_i] eqn:Heval_i.
        destruct st_i; inversion Heval; subst.
        eapply Htrue; eauto.
        inversion Heval; subst.
        eapply Hfalse; eauto.
    Qed.

    (*Regla de Hoare para YulConst *)
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

    (*Regla de Hoare para YulVar*)
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

    (*Regla de Hoare para YulFunc*)
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
		
    (*Regla de Hoare para YulCall*)
		Theorem hoare_call : forall (P : Assertion) (nom : string) (args : list yul_expr) (Q : Assertion),
			(forall f env fenv state vals env_a fenv_a state_a,
				eval_argumentos f args env fenv state false = (vals, env_a, fenv_a, state_a, Yul_Running) ->
				P env fenv state ->
				match buscar_funcion nom fenv_a with
				| Some func =>
						forall env_post fenv_post state_post st_post res_func,
						eval_list f (f_inst func) (combinar_params (f_params func) vals ++ List.map (fun r => (r, D.default_value)) (f_ret func)) (hoist_funcs (f_inst func) fenv_a) state_a false = (res_func, env_post, fenv_post, state_post, st_post) ->
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
			destruct (eval_argumentos f' args env fenv state false) as [[[[vals env_a] fenv_a] state_a] st_args] eqn:Hargs.
			destruct st_args; try discriminate.
			assert (H_call := H f' env fenv state vals env_a fenv_a state_a Hargs Hpre).
			destruct (buscar_funcion nom fenv_a) as [func|] eqn:Hfunc; [|contradiction].
			destruct (eval_list f' (f_inst func) (combinar_params (f_params func) vals ++ List.map (fun r => (r, D.default_value)) (f_ret func)) (hoist_funcs (f_inst func) fenv_a) state_a false) as [[[[res_func env_post] fenv_post] state_post] st_post] eqn:Hlist.
			destruct st_post; inversion Heval; subst.
			- eapply H_call; eauto.
			- eapply H_call; eauto.
		Qed.
		
    (*Regla de Hoare para YulBlock*)
		Theorem hoare_block : forall (P Q : Assertion) inst,
			(forall env_pre fenv_pre state_pre,
				P env_pre fenv_pre state_pre ->
				{{{ fun e fe s => e = abrir_entorno_vars env_pre /\ fe = hoist_funcs inst (abrir_entorno_funcs fenv_pre) /\ s = state_pre }}} 
				inst 
				{{{ fun e' fe' s' => Q (cerrar_entorno_vars e') (cerrar_entorno_funcs fe') s' }}}) ->
			{{ P }} YulBlock inst {{ Q }}.
		Proof.
			intros P Q inst H.
			unfold hoare_triple, hoare_triple_list.
			intros f env fenv state res env' fenv' state' Heval Hpre.
			destruct f; simpl in Heval; [discriminate|].
			destruct (eval_list f inst (abrir_entorno_vars env) (hoist_funcs inst (abrir_entorno_funcs fenv)) state false) as [[[[res_b env_b] fenv_b] state_b] st_b] eqn:Hb.
			destruct st_b; inversion Heval; subst.
			- eapply H; eauto.
		Qed.
		
    (*Regla de Hoare para YulSwitch*)
    Theorem hoare_switch : forall (P Q : Assertion) (R : ValAssertion)
      cond casos def,
      << P >> cond << R >> ->
      (forall val_caso cuerpo_caso,
        In (val_caso, cuerpo_caso) casos ->
        forall res env_c fenv_c state_c,
          R res env_c fenv_c state_c ->
          D.eqb (hd D.default_value res) val_caso = true ->
          {{{ fun e fe s => e = abrir_entorno_vars env_c /\ fe = hoist_funcs cuerpo_caso (abrir_entorno_funcs fenv_c) /\ s = state_c }}} cuerpo_caso {{{ fun e' fe' s' => Q (cerrar_entorno_vars e') (cerrar_entorno_funcs fe') s' }}}) ->
      (forall res env_c fenv_c state_c,
        R res env_c fenv_c state_c ->
        forallb (fun '(vc, _) => negb (D.eqb (hd D.default_value res) vc)) casos = true ->
        {{{ fun e fe s => e = abrir_entorno_vars env_c /\ fe = hoist_funcs def (abrir_entorno_funcs fenv_c) /\ s = state_c }}} def {{{ fun e' fe' s' => Q (cerrar_entorno_vars e') (cerrar_entorno_funcs fe') s' }}}) ->
      {{ P }} YulSwitch cond casos def {{ Q }}.
    Proof.
      intros P Q R cond casos def Hcond Hcasos Hdef.
      unfold hoare_triple, hoare_triple_list, hoare_triple_val in *.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      destruct f.
      + simpl in Heval. inversion Heval.
      + simpl in Heval.   
        destruct (eval_yul f cond env fenv state false) as [[[[res_c env_c] fenv_c] state_c] st_c] eqn:Heval_c.
        destruct st_c; try discriminate.
        assert (H : R res_c env_c fenv_c state_c).
        {eapply Hcond. eauto. exact Hpre. }
        set (v_eval := match res_c with v :: _ => v | [] => D.default_value end).
        assert (Hdef_c : forallb (fun '(vc, _) => negb (D.eqb v_eval vc)) casos = true ->
          {{{ fun e fe s => e = abrir_entorno_vars env_c /\ fe = hoist_funcs def (abrir_entorno_funcs fenv_c) /\ s = state_c }}} def {{{ fun e' fe' s' => Q (cerrar_entorno_vars e') (cerrar_entorno_funcs fe') s' }}}).
        { intros H' f0 env0 fenv0 state0 res0 env0' fenv0' state0' Heval0 H0. eapply Hdef; eauto. }
        clear Hdef.
        revert Hcasos Hdef_c Heval.
        induction casos as [| [vc cc] casos' IHcasos]; intros Hcasos Hdef_c Heval.
        - destruct (eval_list f def (abrir_entorno_vars env_c) (hoist_funcs def (abrir_entorno_funcs fenv_c)) state_c false) as [[[[rd ed] fed] sd] ctrld] eqn:Hd.
          destruct ctrld; inversion Heval; subst.
          eapply Hdef_c; eauto.
        - destruct (D.eqb v_eval vc) eqn:Hmatch.
          ** destruct (eval_list f cc (abrir_entorno_vars env_c) (hoist_funcs cc (abrir_entorno_funcs fenv_c)) state_c false) as [[[[rc ec] fec] sc] ctrc] eqn:Hcc.
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

    (*Regla de Hoare para YulFor*)
    Lemma hoare_bucle : forall (I Q : Assertion) cond cuerpo post,
      (forall f e fe s rc ec fec sc,
          I e fe s ->
          eval_yul f cond e fe s false = (rc, ec, fec, sc, Yul_Running) ->
          I ec fec sc) ->
      (* cond = false *)
      (forall f e fe s rc ec fec sc,
          I e fe s ->
          eval_yul f cond e fe s false = (rc, ec, fec, sc, Yul_Running) ->
          is_true rc = false ->
          Q (cerrar_entorno_vars ec) (cerrar_entorno_funcs fec) sc) ->
      (* break en cuerpo *)
      (forall f rc ec fec sc rb eb feb sb,
          I ec fec sc ->
          is_true rc = true ->
          eval_list f cuerpo (abrir_entorno_vars ec) (hoist_funcs cuerpo (abrir_entorno_funcs fec)) sc true = (rb, eb, feb, sb, Yul_Break) ->
          Q (cerrar_entorno_vars (cerrar_entorno_vars eb)) (cerrar_entorno_funcs (cerrar_entorno_funcs feb)) sb) ->

      (forall f e_i fe_i s_i rc ec fec sc rb eb feb sb rp ep fep sp ctrlb ctrlp,
          I e_i fe_i s_i ->
          eval_yul f cond e_i fe_i s_i false = (rc, ec, fec, sc, Yul_Running) ->
          is_true rc = true ->
          (ctrlb = Yul_Running \/ ctrlb = Yul_Continue) ->
          eval_list f cuerpo (abrir_entorno_vars ec) (hoist_funcs cuerpo (abrir_entorno_funcs fec)) sc true = (rb, eb, feb, sb, ctrlb) ->
          eval_list f post (abrir_entorno_vars (cerrar_entorno_vars eb)) (hoist_funcs post (abrir_entorno_funcs (cerrar_entorno_funcs feb))) sb false = (rp, ep, fep, sp, ctrlp) ->
          (ctrlp = Yul_Running \/ ctrlp = Yul_Continue) ->
          I (cerrar_entorno_vars ep) (cerrar_entorno_funcs fep) sp) ->
      forall n e fe s res env' fenv' state',
        I e fe s ->
        eval_bucle cond cuerpo post n e fe s false =
          (res, env', fenv', state', Yul_Running) ->
        Q (cerrar_entorno_vars env') (cerrar_entorno_funcs fenv') state'.
    Proof.
      intros I Q cond cuerpo post Hcond_inv Hfalse Hbreak_b Hpaso.
      induction n as [|n IHn];
        intros e fe s res env' fenv' state' HI Heval.
      - simpl in Heval. inversion Heval.
      - cbn [eval_bucle] in Heval.
        destruct (eval_yul n cond e fe s false) as [[[[rc ec] fec] sc] ctrlc] eqn:Hc.
        destruct ctrlc; try inversion Heval.
        assert (HIec : I ec fec sc) by (eapply Hcond_inv; eauto).
        revert Heval.
        destruct (is_true rc) eqn:Hrc; intro Heval.
        + destruct (eval_list n cuerpo (abrir_entorno_vars ec) (hoist_funcs cuerpo (abrir_entorno_funcs fec)) sc true) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
          destruct ctrlb.
          * destruct (eval_list n post (abrir_entorno_vars (cerrar_entorno_vars eb)) (hoist_funcs post (abrir_entorno_funcs (cerrar_entorno_funcs feb))) sb false) as [[[[rp ep] fep] sp] ctrlp] eqn:Hp.
            destruct ctrlp.
            -- assert (HI' : I (cerrar_entorno_vars ep) (cerrar_entorno_funcs fep) sp).
               { eapply (Hpaso n e fe s rc ec fec sc rb eb feb sb rp ep fep sp Yul_Running Yul_Running);
                 eauto. }
               eapply IHn; eauto.
            -- inversion Heval.
            -- inversion Heval.
            -- inversion Heval.
            -- inversion Heval.
          * inversion Heval; subst.
            eapply Hbreak_b; [exact HIec | exact Hrc | exact Hb].
          * destruct (eval_list n post (abrir_entorno_vars (cerrar_entorno_vars eb)) (hoist_funcs post (abrir_entorno_funcs (cerrar_entorno_funcs feb))) sb false) as [[[[rp ep] fep] sp] ctrlp] eqn:Hp.
            destruct ctrlp.
            -- apply (IHn (cerrar_entorno_vars ep) (cerrar_entorno_funcs fep) sp res env' fenv' state').
               exact (Hpaso n e fe s rc ec fec sc rb eb feb sb rp ep fep sp Yul_Continue Yul_Running HI Hc Hrc (or_intror eq_refl) Hb Hp (or_introl eq_refl)).
               exact Heval.
            -- inversion Heval.
            -- inversion Heval.
            -- inversion Heval.
            -- inversion Heval.
          * inversion Heval.
          * inversion Heval.
        + inversion Heval; subst.
          eapply Hfalse; [exact HI | exact Hc | exact Hrc].
    Qed.


    Theorem hoare_for : forall (P I Q : Assertion)
      init cond post cuerpo,
      (forall env_pre fenv_pre state_pre, P env_pre fenv_pre state_pre ->
      {{{ fun e fe s => e = abrir_entorno_vars env_pre /\ fe = hoist_funcs init (abrir_entorno_funcs fenv_pre) /\ s = state_pre }}} init {{{ I }}}) ->
      (*Hcond*)
      (forall f e fe s rc ec fec sc,
          I e fe s ->
          eval_yul f cond e fe s false = (rc, ec, fec, sc, Yul_Running) ->
          I ec fec sc) ->
      (*Hfalse*)
      (forall f e fe s rc ec fec sc,
          I e fe s ->
          eval_yul f cond e fe s false = (rc, ec, fec, sc, Yul_Running) ->
          is_true rc = false ->
          Q (cerrar_entorno_vars ec) (cerrar_entorno_funcs fec) sc) ->
      (*Hbreak*)
      (forall f rc ec fec sc rb eb feb sb,
          I ec fec sc ->
          is_true rc = true ->
          eval_list f cuerpo (abrir_entorno_vars ec) (hoist_funcs cuerpo (abrir_entorno_funcs fec)) sc true = (rb, eb, feb, sb, Yul_Break) ->
          Q (cerrar_entorno_vars (cerrar_entorno_vars eb)) (cerrar_entorno_funcs (cerrar_entorno_funcs feb)) sb) ->

      (*H'*)
      (forall f e_i fe_i s_i rc ec fec sc rb eb feb sb rp ep fep sp ctrlb ctrlp,
          I e_i fe_i s_i ->
          eval_yul f cond e_i fe_i s_i false = (rc, ec, fec, sc, Yul_Running) ->
          is_true rc = true ->
          (ctrlb = Yul_Running \/ ctrlb = Yul_Continue) ->
          eval_list f cuerpo (abrir_entorno_vars ec) (hoist_funcs cuerpo (abrir_entorno_funcs fec)) sc true = (rb, eb, feb, sb, ctrlb) ->
          eval_list f post (abrir_entorno_vars (cerrar_entorno_vars eb)) (hoist_funcs post (abrir_entorno_funcs (cerrar_entorno_funcs feb))) sb false = (rp, ep, fep, sp, ctrlp) ->
          (ctrlp = Yul_Running \/ ctrlp = Yul_Continue) ->
          I (cerrar_entorno_vars ep) (cerrar_entorno_funcs fep) sp) ->
      {{ P }} YulFor init cond post cuerpo {{ Q }}.
    Proof.
      intros P I Q init cond post cuerpo H Hcond Hfalse Hbreak H'.
      unfold hoare_triple, hoare_triple_list in *.
      intros f env fenv state res env' fenv' state' Heval Hpre.
      destruct f.
      + simpl in Heval; inversion Heval.
      + simpl in Heval; inversion Heval.
        destruct (eval_list f init (abrir_entorno_vars env) (hoist_funcs init (abrir_entorno_funcs fenv)) state false) as [[[[ri ei] fei] si] ctrli] eqn:Hi.
        destruct ctrli; try (inversion Heval; subst; discriminate).
        assert (HI : I ei fei si) by (eapply H; eauto).
        destruct (eval_bucle cond cuerpo post f ei fei si false) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
        destruct ctrlb; try (inversion Heval; subst; discriminate).
        inversion Heval; subst.
        eapply hoare_bucle; [exact Hcond | exact Hfalse | exact Hbreak | exact H' | exact HI | exact Hb].
    Qed.

    (** Tácticas auxiliares para resolver estados de terminación imposibles *)
    Ltac solve_zero H :=
      discriminate H ||
      (inversion H; subst;
       match goal with
       | [ Hcontra : Yul_Error _ = Yul_Running |- _ ] => discriminate Hcontra
       | [ Hcontra : Yul_Error _ = Yul_Continue |- _ ] => discriminate Hcontra
       | [ Hcontra : Yul_Error _ = Yul_Break |- _ ] => discriminate Hcontra
       | [ Hcontra : Yul_Error _ = Yul_Leave |- _ ] => discriminate Hcontra
       | [ Hcontra : Yul_Running = Yul_Error _ |- _ ] => discriminate Hcontra
       | [ Hcontra : Yul_Error _ = Yul_Running \/ Yul_Error _ = Yul_Continue |- _ ] =>
           destruct Hcontra as [Hc|Hc]; discriminate Hc
       end).

    (** [fuel_en H] avanza un nivel de fuel en la hipótesis [H].
        Si encuentra un constructor, lo destruye y simplifica. *)
    Ltac fuel_en H :=
      simpl in H;
      match type of H with
      | context [eval_bucle ?x _ _ _ _ _ _ _ _] =>
          destruct x; [ solve_zero H | simpl in H]
      | context [eval_list ?x _ _ _ _ _] =>
          destruct x; [ solve_zero H | simpl in H]
      | context [eval_yul ?x _ _ _ _ _] =>
          destruct x; [ solve_zero H | simpl in H]
      | context [eval_argumentos ?x _ _ _ _ _] =>
          destruct x; [ solve_zero H | simpl in H]
      end.

    (** [rec_fuel_en H] repite [fuel_en H] hasta que falle. *)
    Ltac rec_fuel_en H := repeat (fuel_en H).

    (** [eval_expr_en H Hvar] evalúa completamente una expresión en la
        hipótesis [H], usando [Hvar].Repite si es necesario (lectura + asignación) *)
    Ltac eval_expr_en H Hvar :=
      rec_fuel_en H;
      rewrite Hvar in H;
      simpl in H;
      rec_fuel_en H;
      try (rewrite Hvar in H; simpl in H; rec_fuel_en H).

    (** [resuelve_buscar] resuelve goals de la forma
        [buscar_variable "X" (("X", v) :: ...) = Some v].*)
    Ltac resuelve_buscar :=
      try unfold abrir_entorno_vars; try unfold cerrar_entorno_vars;
      simpl;
      unfold buscar_variable;
      match goal with
      | |- context [string_dec ?s1 ?s2] =>
        destruct (string_dec s1 s2); [reflexivity | contradiction]
      | |- ?x = ?x => reflexivity
      | |- Some _ = Some _ => f_equal; reflexivity
      end.

 	End YulHoare.