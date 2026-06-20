From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.
Open Scope list_scope.
Require Import LenguajeYul.dialect.
Require Import main.ast. 

Module YulSemantica (D : DIALECT) (A : AST_INTERFACE D).
    Import A.
    Inductive yul_control :=
    | Yul_Running
    | Yul_Break
    | Yul_Continue
    | Yul_Leave
    | Yul_Error (msg : string).

    Definition is_true (l : list D.value_t) : bool :=
    match l with
    | val :: _ => D.is_true_value val
    | nil => false
    end.

  Fixpoint buscar_variable (nombre : string) (env : A.yul_env) : option D.value_t :=
    match env with
    | [] => None
    | (n, v) :: resto =>
        if string_dec nombre n then Some v 
        else buscar_variable nombre resto
    end.

  Fixpoint buscar_funcion (nombre : string) (fenv : A.yul_fun_env) : option A.yul_funcion :=
    match fenv with
    | [] => None
    | (n, f) :: resto => 
      if string_dec nombre n then Some f 
      else buscar_funcion nombre resto
    end.

  Fixpoint combinar_params (nombres : list string) (valores : list D.value_t) : A.yul_env :=
    match nombres, valores with
    | n :: ns, v :: vs => (n, v) :: combinar_params ns vs
    | _, _ => []
    end.

  Fixpoint extraer_retornos (rets : list string) (env : A.yul_env) : list D.value_t :=
    match rets with
    | [] => []
    | r :: rs =>
        match buscar_variable r env with
        | Some v => v :: extraer_retornos rs env
        | None => D.default_value :: extraer_retornos rs env
        end
    end.

  Definition restringe_env (env_nuevo : A.yul_env) (env_orig : A.yul_env) : A.yul_env :=
    filter (fun '(n, _) => existsb (fun '(m, _) => String.eqb n m) env_orig) env_nuevo.

  Fixpoint eval_yul (f : nat) (expr : A.yul_expr) (env : A.yul_env) (fenv: A.yul_fun_env) (state : D.dialect_state_t) {struct f} : (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * yul_control) :=
    match f with
    | O => ([], env, fenv, state, Yul_Error "f agotado")
    | S f' => 
      match expr with
      | A.YulConst v => ([v], env, fenv, state, Yul_Running)
      | A.YulBreak =>
        ([], env, fenv, state, Yul_Break)
      | A.YulContinue =>
        ([], env, fenv, state, Yul_Continue)
      | A.YulLeave =>
        ([], env, fenv, state, Yul_Leave)
      | A.YulOp op args =>
        let '(vals, env_final, fenv_final, s_final, st) := eval_argumentos f' args env fenv state in
        match st with
        | Yul_Running =>
          let '(res, s_r, status) :=
            D.execute_opcode s_final op vals in
          match status with
          | Status.Running => (res, env_final, fenv_final, s_r, Yul_Running)
          | Status.Terminated => (res, env_final, fenv_final, s_r, Yul_Error "terminated")
          | Status.Reverted => (res, env_final, fenv_final, s_r, Yul_Error "reverted")
          | Status.Error msg => (res, env_final, fenv_final, s_r, Yul_Error msg)
          end
        | _ => ([], env_final, fenv_final, s_final, st)
        end
      | A.YulLet nombres var_expr =>
        let '(valores, env_i, fenv_i, state_i, st) := eval_yul f' var_expr env fenv state in
        match st with
        | Yul_Running =>
            let fix asignar (ns : list string) (vs : list D.value_t) (e : yul_env) : option yul_env :=
              match ns, vs with
              | [], [] => Some e
              | n::ns', v::vs' => asignar ns' vs' ((n, v) :: e)
              | _, _ => None 
              end
            in
            match asignar nombres valores env_i with
            | Some nuevo_env => ([], nuevo_env, fenv_i, state_i, Yul_Running)
            | None => ([], env_i, fenv_i, state_i, Yul_Error "El numero de variables no coincide con los valores que devuelve la funcion")
            end
        | _ => (valores, env_i, fenv_i, state_i, st)
        end
      | A.YulVar nom =>
        match buscar_variable nom env with
        | Some v => ([v], env, fenv, state, Yul_Running)
        | None => ([], env, fenv, state, Yul_Error ("Variable no definida: " ++ nom))
        end
      | A.YulIf cond inst =>
        let '(res, env1, fenv1, state1, status1) := eval_yul f' cond env fenv state in
            match status1 with
            | Yul_Running => 
                if (is_true res) 
                then let '(res2,env2,fenv2,state2,status2) := eval_list f' inst env1 fenv1 state1 in
                (res2,restringe_env env2 env1,fenv2,state2,status2)
                else ([], env1, fenv1, state1, Yul_Running)
            | _ => (res, env1, fenv1, state1, status1)
            end
      | A.YulFunc nom params rets inst =>
        let n_func := {| f_params := params; f_ret := rets; f_inst := inst |} in
        ([], env, (nom, n_func) :: fenv, state, Yul_Running)
      | A.YulSwitch cond casos def =>
        let '(res_c, env_c, fenv_c, state_c, st_c) := eval_yul f' cond env fenv state in
        match st_c with
        | Yul_Running =>
            let v_evaluado :=
            match res_c with
            | v :: _ => v
            | [] => D.default_value
            end in
            let fix buscar (l : list (D.value_t * list A.yul_expr)) :=
              match l with
              | [] =>
                  let '(r,e,fe,s,st) :=
                    eval_list f' def env_c fenv_c state_c in
                  (r, restringe_env e env_c, fe, s, st)

              | (val_caso, cuerpo) :: resto =>
                  if D.eqb v_evaluado val_caso then
                    let '(r,e,fe,s,st) :=
                      eval_list f' cuerpo env_c fenv_c state_c in
                    (r, restringe_env e env_c, fe, s, st)
                  else buscar resto
              end
            in buscar casos
        | fallo => ([], env_c, fenv_c, state_c, fallo)
        end
      | A.YulFor init cond post cuerpo =>
        let (p, ctrl) := eval_list f' init env fenv state in
        let (p0, si) := p in
        let (p1, fei) := p0 in
        let (_, ei) := p1 in
        match ctrl with
        | Yul_Running => eval_bucle cond cuerpo post env f' ei fei si
        | Yul_Leave => ([], ei, fei, si, Yul_Leave)
        | _ => ([], ei, fei, si, ctrl)
        end
      | A.YulCall nom args =>
        let '(vals, env_a, fenv_a, state_a, st) := eval_argumentos f' args env fenv state in
        match st with
        | Yul_Running =>
          match buscar_funcion nom fenv_a with
          | Some func =>
            let env_local := combinar_params (f_params func) vals in
            let '(_, env_post, _, state_post, st_post) := eval_list f' (f_inst func) env_local fenv_a state_a in
            match st_post with
            | Yul_Running | Yul_Leave =>
                let ret_vals := extraer_retornos (f_ret func) env_post in
                (ret_vals, env_a, fenv_a, state_post, Yul_Running)
            | _ => ([], env_a, fenv_a, state_post, st_post)
            end
          | None => ([], env_a, fenv_a, state_a, Yul_Error ("Función no definida: " ++ nom))
          end
        | _ => ([], env_a, fenv_a, state_a, st)
        end
      end
    end
  with eval_list (f : nat) (l : list A.yul_expr) (env : A.yul_env) (fenv : A.yul_fun_env) (state : D.dialect_state_t) {struct f}: (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * yul_control) :=
    match f with
    | O => ([], env, fenv, state, Yul_Error "error")
    | S f' =>
        match l with
        | nil => ([], env, fenv, state, Yul_Running)
        | e :: rest =>
            let '(res, env1, fenv1, state1, status1) := eval_yul f' e env fenv state in
            match status1 with
            | Yul_Running => eval_list f' rest env1 fenv1 state1
            | _ => (res, env1, fenv1, state1, status1)
            end
        end
    end
  with eval_argumentos (f : nat) (l : list A.yul_expr) (e : A.yul_env) (fe : A.yul_fun_env) (s : D.dialect_state_t) {struct f}: (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * yul_control) :=
    match f with
    | O => ([], e, fe, s, Yul_Error "Sin fuel en argumentos")
    | S f' =>
      match l with
      | [] => ([], e, fe, s, Yul_Running)
      | x :: xs => 
        let '(rest, e', fe', s', st') := eval_argumentos f' xs e fe s in
        match st' with
        | Yul_Running => 
          let '(res, e'', fe'', s'', st'') := eval_yul f' x e' fe' s' in
          match st'' with
          | Yul_Running => ((res ++ rest)%list, e'', fe'', s'', Yul_Running)
          | _ => ([], e'', fe'', s'', st'')
          end
        | _ => ([], e', fe', s', st')
        end
      end
    end
    with eval_bucle(cond : yul_expr) (cuerpo post : list yul_expr) (env_orig : yul_env) (f : nat) (ei : yul_env) (fei : yul_fun_env) (si : D.dialect_state_t) {struct f}:=
      match f with
      | O => ([], ei, fei, si, Yul_Error "error en For")
      | S f' =>
        match eval_yul f' cond ei fei si with
        | (res_c, e_c, fe_c, s_c, Yul_Running) =>
          if is_true res_c then
            match eval_list f' cuerpo e_c fe_c s_c with
            | (_, e_b, fe_b, s_b, Yul_Break) =>
              ([], restringe_env (restringe_env e_b e_c) env_orig, fe_b, s_b, Yul_Running)
            | (_, e_b, fe_b, s_b, Yul_Running)
            | (_, e_b, fe_b, s_b, Yul_Continue) =>
              match eval_list f' post (restringe_env e_b e_c) fe_b s_b with
              | (_, e_p, fe_p, s_p, Yul_Break) =>
                ([], restringe_env (restringe_env e_b e_c) env_orig, fe_b, s_b, Yul_Running)
              | (_, e_p, fe_p, s_p, Yul_Running)
              | (_, e_p, fe_p, s_p, Yul_Continue) =>
                eval_bucle cond cuerpo post env_orig f' (restringe_env e_p (restringe_env e_b e_c)) fe_p s_p
              | (_, e_p, fe_p, s_p, Yul_Leave) =>
                ([], restringe_env (restringe_env e_b e_c) env_orig, fe_b, s_b, Yul_Leave)
              | (_, e_p, fe_p, s_p, Yul_Error msg) =>
                ([], restringe_env (restringe_env e_b e_c) env_orig, fe_b, s_b, Yul_Error msg)
              end
            | (_, e_b, fe_b, s_b, Yul_Leave) =>
              ([], restringe_env (restringe_env e_b e_c) env_orig, fe_b, s_b, Yul_Leave)
            | (_, e_b, fe_b, s_b, Yul_Error _ as st) =>
              ([], restringe_env (restringe_env e_b e_c) env_orig, fe_b, s_b, st)
            end
          else ([], e_c, fe_c, s_c, Yul_Running)
        | (_, e_c, fe_c, s_c, st) =>
          ([], restringe_env e_c env_orig, fe_c, s_c, st)
        end
      end.

  Definition ejecutar_eval_bloque (ast_list : list A.yul_expr) (env : A.yul_env) (fenv : A.yul_fun_env) (state : D.dialect_state_t) : (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * Status.t) :=
    let '(res, env_f, fenv_f, state_f, final_c) := eval_list 5000 ast_list env fenv state in
    let final_s :=
      match final_c with
      | Yul_Running => Status.Running
      | Yul_Break => Status.Error "break"
      | Yul_Continue => Status.Error "continue"
      | Yul_Leave => Status.Error "leave"
      | Yul_Error msg => Status.Error msg
      end
    in (res,env_f,fenv_f,state_f,final_s).

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
              destruct expr as [ v | op args | ns y | nombre_var
                              | cond inst | cond casos def
                              | ini cond post cuerpo
                              | nom params rets inst
                              | nom args | | | ];
                simpl in H, H1.
              * inversion H1; subst. split.
                ++ repeat split; discriminate.
                ++ exact H0.
              * revert H1.
                destruct (eval_argumentos f' args env fenv state) as [[[[ra ea] fea] sa] ctrla] eqn:Ha.
                intro H1.
                destruct (IHa' args env fenv state ra ea fea sa ctrla H H0 Ha) as [[Ha1 [Ha2 Ha3]] Hfea].
                destruct ctrla. try congruence.
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
                set (opt := (fix asignar (ns0 : list string) (vs : list D.value_t)
                                  (e0 : yul_env) {struct ns0} : option yul_env :=
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
                destruct (eval_yul f' cond env fenv state) as [[[[rc ec] fec] sc] ctrlc] eqn:Hc.
                intro H0.
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
              (* YulCall*)
              * revert H1.
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
                  destruct ctrlb. try congruence.
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
End YulSemantica.