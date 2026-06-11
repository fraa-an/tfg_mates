From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
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
        let '(res_i, env_i, fenv_i, state_i, status_i) := eval_list f' init env fenv state in
        match status_i with
        | Yul_Running =>
          let fix bucle n e fe s :=
          match n with
          | O => ([], e, fe, s, Yul_Error "error en For")
          | S n' =>
            let '(res_c, e_c, fe_c, s_c, status_c) := eval_yul n' cond e fe s in
              match status_c with
              | Yul_Running =>
                if is_true res_c then
                  let '(_, e_b, fe_b, s_b, status_b) := eval_list n' cuerpo e_c fe_c s_c in
                    let e_b' := restringe_env e_b e_c in
                    match status_b with
                    | Yul_Running | Yul_Continue => 
                      let '(_, e_p, fe_p, s_p, status_p) := eval_list n' post e_b' fe_b s_b in
                      let e_p' := restringe_env e_p e_b' in
                        match status_p with
                        | Yul_Running => bucle n' e_p' fe_p s_p
                        | Yul_Continue => bucle n' e_p' fe_p s_p
                        | Yul_Break => ([], restringe_env e_b' env, fe_b, s_b, Yul_Running)
                        | Yul_Leave => ([], restringe_env e_b' env, fe_b, s_b, Yul_Leave)
                        | Yul_Error msg => ([], restringe_env e_b' env, fe_b, s_b, Yul_Error msg)
                        end
                    | Yul_Leave =>
                      ([], restringe_env e_b' env, fe_b, s_b, Yul_Leave)
                    | Yul_Break =>
                      ([], restringe_env e_b' env, fe_b, s_b, Yul_Running)
                    | fallo => 
                      ([], restringe_env e_b' env, fe_b, s_b, fallo)
                    end
                else ([], e_c, fe_c, s_c, Yul_Running)
              | fallo => ([], restringe_env e_c env, fe_c, s_c, fallo)
              end
          end
          in bucle f' env_i fenv_i state_i
        | Yul_Leave =>
          ([], env_i, fenv_i, state_i, Yul_Leave)
        | fallo => (res_i, env_i, fenv_i, state_i, fallo)
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
End YulSemantica.