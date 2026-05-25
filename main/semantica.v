From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.
Require Import LenguajeYul.dialect.
Require Import main.ast. 

Module YulSemantica (D : DIALECT) (A : AST_INTERFACE D).
    Import A.

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

  Fixpoint eval_yul (f : nat) (expr : A.yul_expr) (env : A.yul_env) (fenv: A.yul_fun_env) (state : D.dialect_state_t) {struct f} : (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * Status.t) :=
    match f with
    | O => ([], env, fenv, state, Status.Error "error al evaluar expresion")
    | S f' => 
      match expr with
      | A.YulConst v => ([v], env, fenv, state, Status.Running)
      | A.YulOp op args =>
        let '(vals, env_final, fenv_final, s_final, st) := eval_argumentos f' args env fenv state in
        match st with
        | Status.Running => 
          let '(res, s_r, status) := D.execute_opcode s_final op vals in 
          (res, env_final, fenv_final, s_r, status)
        | _ => ([], env_final, fenv_final, s_final, st)
        end
      | A.YulLet nombres var_expr =>
        let '(valores, env_i, fenv_i, state_i, st) := eval_yul f' var_expr env fenv state in
        match st with
        | Status.Running =>
            let fix asignar_multiples (ns : list string) (vs : list D.value_t) (e : yul_env) : option yul_env :=
              match ns, vs with
              | [], [] => Some e
              | n::ns', v::vs' => asignar_multiples ns' vs' ((n, v) :: e)
              | _, _ => None 
              end
            in
            match asignar_multiples nombres valores env_i with
            | Some nuevo_env => ([], nuevo_env, fenv_i, state_i, Status.Running)
            | None => ([], env_i, fenv_i, state_i, Status.Error "El numero de variables no coincide con los valores que devuelve la funcion")
            end
        | _ => (valores, env_i, fenv_i, state_i, st)
        end
      | A.YulVar nom =>
        match buscar_variable nom env with
        | Some v => ([v], env, fenv, state, Status.Running)
        | None => ([], env, fenv, state, Status.Error ("Variable no definida: " ++ nom))
        end
      | A.YulIf cond inst =>
        let '(res, env1, fenv1, state1, status1) := eval_yul f' cond env fenv state in
            match status1 with
            | Status.Running => 
                if (is_true res) 
                then eval_list f' inst env1 fenv1 state1
                else ([], env1, fenv1, state1, Status.Running)
            | _ => (res, env1, fenv1, state1, status1)
            end
      | A.YulFunc nom params rets inst =>
        let n_func := {| f_params := params; f_ret := rets; f_inst := inst |} in
        ([], env, (nom, n_func) :: fenv, state, Status.Running)
      | A.YulSwitch cond casos def =>
        let '(res_c, env_c, fenv_c, state_c, status_c) := eval_yul f' cond env fenv state in
        match status_c with
        | Status.Running =>
            let fix buscar_caso (l : list (D.value_t * list yul_expr)) :=
              match l with
              | nil => eval_list f' def env_c fenv_c state_c
              | (val_caso, cuerpo) :: resto =>
                  let v_evaluado := match res_c with 
                                    | v :: _ => v 
                                    | nil => D.default_value 
                                    end in
                  if D.eqb v_evaluado val_caso
                  then eval_list f' cuerpo env_c fenv_c state_c
                  else buscar_caso resto
              end
            in buscar_caso casos
        | _ => (res_c, env_c, fenv_c, state_c, status_c)
        end
      | A.YulFor init cond post cuerpo =>
        let '(res_i, env_i, fenv_i, state_i, status_i) := eval_list f' init env fenv state in
        match status_i with
        | Status.Running =>
          let fix bucle n e fe s :=
          match n with
          | O => ([], e, fe, s, Status.Error "error en For")
          | S n' =>
            let '(res_c, e_c, fe_c, s_c, status_c) := eval_yul n' cond e fe s in
              match status_c with
              | Status.Running =>
                if is_true res_c then
                  let '(_, e_b, fe_b, s_b, status_b) := eval_list n' cuerpo e_c fe_c s_c in
                    match status_b with
                    | Status.Running => 
                      let '(_, e_p, fe_p, s_p, status_p) := eval_list n' post e_b fe_b s_b in
                        match status_p with
                        | Status.Running => bucle n' e_p fe_p s_p
                        | fallo => ([], e_p, fe_p, s_p, fallo)
                        end
                    | fallo => ([], e_b, fe_b, s_b, fallo)
                    end
                else ([], e_c, fe_c, s_c, Status.Running)
              | fallo => ([], e_c, fe_c, s_c, fallo)
              end
          end
          in bucle f' env_i fenv_i state_i
        | fallo => (res_i, env_i, fenv_i, state_i, fallo)
        end
      | A.YulCall nom args =>
        let '(vals, env_a, fenv_a, state_a, st) := eval_argumentos f' args env fenv state in
        match st with
        | Status.Running =>
          match buscar_funcion nom fenv_a with
          | Some func =>
            let env_local := combinar_params (f_params func) vals in
            let '(_, env_post, _, state_post, st_post) := eval_list f' (f_inst func) env_local fenv_a state_a in
            match st_post with
            | Status.Running =>
                let ret_vals := extraer_retornos (f_ret func) env_post in
                (ret_vals, env_a, fenv_a, state_post, Status.Running)
            | _ => ([], env_a, fenv_a, state_post, st_post)
            end
          | None => ([], env_a, fenv_a, state_a, Status.Error ("Función no definida: " ++ nom))
          end
        | _ => ([], env_a, fenv_a, state_a, st)
        end
      end
    end
  with eval_list (f : nat) (l : list A.yul_expr) (env : A.yul_env) (fenv : A.yul_fun_env) (state : D.dialect_state_t) {struct f}: (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * Status.t) :=
    match f with
    | O => ([], env, fenv, state, Status.Error "error")
    | S f' =>
        match l with
        | nil => ([], env, fenv, state, Status.Running)
        | e :: rest =>
            let '(res, env1, fenv1, state1, status1) := eval_yul f' e env fenv state in
            match status1 with
            | Status.Running => eval_list f' rest env1 fenv1 state1
            | _ => (res, env1, fenv1, state1, status1)
            end
        end
    end
  with eval_argumentos (f : nat) (l : list A.yul_expr) (e : A.yul_env) (fe : A.yul_fun_env) (s : D.dialect_state_t) {struct f}: (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * Status.t) :=
    match f with
    | O => ([], e, fe, s, Status.Error "Sin fuel en argumentos")
    | S f' =>
      match l with
      | [] => ([], e, fe, s, Status.Running)
      | x :: xs => 
        let '(res, e', fe', s', st) := eval_yul f' x e fe s in
        match st with
        | Status.Running => 
          let '(rest, e'', fe'', s'', st') := eval_argumentos f' xs e' fe' s' in
          match st' with
          | Status.Running => ((res ++ rest)%list, e'', fe'', s'', Status.Running)
          | _ => ([], e'', fe'', s'', st')
          end
        | _ => ([], e', fe', s', st)
        end
      end
    end.

  Definition ejecutar_eval_bloque (ast_list : list A.yul_expr) (env : A.yul_env) (fenv : A.yul_fun_env) (state : D.dialect_state_t) : (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * Status.t) :=
    eval_list 5000 ast_list env fenv state.

End YulSemantica.