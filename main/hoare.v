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
    Notation "P <<->> Q" := (P->>Q and Q->>P) (at level 80).

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
        - (* f = 0 *)
            simpl in Heval. inversion Heval.
        - (* f = S f' *)
            simpl in Heval. inversion Heval. subst.
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

    Theorem hoare_consequence : forall (P P' Q Q' : Assertion) e,
        {{ P' }} e {{ Q' }} ->
        P ->> P' ->
        Q' ->> Q ->
        {{ P }} e {{ Q }}.
    Proof.
        intros P P' Q Q' e Hht HP HQ.
        unfold hoare_triple.
        intros f env fenv state res env' fenv' state' Heval Hpre.
        apply HQ.
        apply (Hht f env fenv state res env' fenv' state').
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
End YulHoare.