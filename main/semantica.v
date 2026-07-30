From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.
Open Scope list_scope.
Require Import LenguajeYul.dialect.
Require Import main.ast. 

Module YulSemantica (D : DIALECT) (A : AST_INTERFACE D).
  Import A.
  (*
    Ampliación del State de DIALECT para manejar cómodamente el flujo de control 
    de bucles (break y continue) y de salida de funciones (leave)
  *)
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

  (*Obtención de variables del entorno*)
  Fixpoint buscar_variable (nombre : string) (env : A.yul_env) : option D.value_t :=
    match env with
    | [] => None
    (*Se hace match sobre los entornos anidados hasta encontrar un nombre de entorno que coincida*)
    | (n, v) :: resto => 
        if string_dec nombre n then Some v 
        else buscar_variable nombre resto
    end.

  (*Obtención de funciones del entorno (de funciones)*)
  Fixpoint buscar_funcion (nombre : string) (fenv : A.yul_fun_env) : option A.yul_funcion :=
    match fenv with
    | [] => None
    | (n, f) :: resto => 
      if string_dec nombre n then Some f 
      else buscar_funcion nombre resto
    end.

  (*Necesaria en la llamada a funciones: asigna los parámetros de la función con los valores concretos en su llamada*)
  Fixpoint combinar_params (nombres : list string) (valores : list D.value_t) : A.yul_env :=
    match nombres, valores with
    | n :: ns, v :: vs => (n, v) :: combinar_params ns vs
    | _, _ => []
    end.

  (*
    Busca en el entorno de ejecución de la llamada a una función la variable que ha de devolver como resultado.    
  *)
  Fixpoint extraer_retornos (rets : list string) (env : A.yul_env) : list D.value_t :=
    match rets with
    | [] => []
    | r :: rs =>
        match buscar_variable r env with
        | Some v => v :: extraer_retornos rs env
        | None => D.default_value :: extraer_retornos rs env
        end
    end.

  (*Añade nuevas variables al entorno: se utiliza en declaraciones*)
  Fixpoint agregar_vars (ns : list string) (vs : list D.value_t) (e : yul_env) : option yul_env :=
    match ns, vs with
    | [], [] => Some e
    | n::ns', v::vs' =>
      match buscar_variable n e with
        | Some _ => None (*shadowing no permitido*)
        | None =>  agregar_vars ns' vs' ((n, v) :: e)
        end
    | _, _ => None
    end.

  (*Reemplaza el valor de una variable in-place para no alterar su posición en el entorno*)
  Fixpoint reemplazar_var (n : string) (v : D.value_t) (e : yul_env) : yul_env :=
    match e with
    | [] => []
    | (k, val) :: e' =>
        if string_dec n k then (k, v) :: e'
        else (k, val) :: reemplazar_var n v e'
    end.

  Lemma buscar_reemplazar_mismo : forall n v env v_old,
    buscar_variable n env = Some v_old ->
    buscar_variable n (reemplazar_var n v env) = Some v.
  Proof.
    intros n v env v_old H.
    induction env as [| [k val] env_tail IH].
    - inversion H.
    - simpl in *. destruct (string_dec n k) as [Heq | Hneq].
      + simpl. destruct (string_dec n k). reflexivity. contradiction.
      + simpl. destruct (string_dec n k). contradiction. apply IH. exact H.
  Qed.

  (*
    Comprueba si una lista de strings contiene nombres duplicados.
    Se usa para rechazar declaraciones y asignaciones del tipo "let x, x := f()".
  *)
  Fixpoint tiene_duplicados (l : list string) : bool :=
    match l with
    | [] => false
    | n :: rest =>
        if List.existsb (String.eqb n) rest then true
        else tiene_duplicados rest
    end.

  (*
    Actualiza las variables del entorno tras asignaciones.
    Rechaza asignaciones con nombres duplicados en el lado izquierdo (por ejemplo, "x, x := f()").
  *)
  Definition actualizar_vars (ns : list string) (vs : list D.value_t) (e : yul_env) : option yul_env :=
    if tiene_duplicados ns then None
    else
      let fix go (ns : list string) (vs : list D.value_t) (e : yul_env) : option yul_env :=
        match ns, vs with
        | [], [] => Some e
        | n::ns', v::vs' =>
            match buscar_variable n e with
            | Some _ => go ns' vs' (reemplazar_var n v e)
            | None => None
            end
        | _, _ => None
        end
      in go ns vs e.
  
  (* Separadores de Scope para Variables *)
  Definition abrir_entorno_vars (env : A.yul_env) : A.yul_env :=
    ("|"%string, D.default_value) :: env.

  Fixpoint cerrar_entorno_vars (env : A.yul_env) : A.yul_env :=
    match env with
    | [] => []
    | (k, v) :: env' =>
        if String.eqb k "|"%string then env'
        else cerrar_entorno_vars env'
    end.

  (* Separadores de Scope para funciones *)
  Definition abrir_entorno_funcs (fenv : A.yul_fun_env) : A.yul_fun_env :=
    ("|"%string, {| f_params := []; f_ret := []; f_inst := [] |}) :: fenv.

  Fixpoint cerrar_entorno_funcs (fenv : A.yul_fun_env) : A.yul_fun_env :=
    match fenv with
    | [] => []
    | (k, f) :: fenv' =>
        if String.eqb k "|"%string then fenv'
        else cerrar_entorno_funcs fenv'
    end.

  (*
    Registra todas las funciones declaradas en la lista de instrucciones de un bloque
    en el entorno de funciones antes de ejecutar ninguna instrucción.
    Esto es necesario según la especificación de Yul:
    "Functions are visible in the whole block (even before their definitions)".
  *)
  Fixpoint hoist_funcs (l : list A.yul_expr) (fenv : A.yul_fun_env) : A.yul_fun_env :=
    match l with
    | [] => fenv
    | (A.YulFunc nom params rets inst) :: rest =>
        let n_func := {| f_params := params; f_ret := rets; f_inst := inst |} in
        hoist_funcs rest ((nom, n_func) :: fenv)
    | _ :: rest => hoist_funcs rest fenv
    end.

  (*
    Función recursiva que calcula la semántica de una expresión en Yul.
    Se utiliza f como "fuel" o "combustible" para garantizar terminación de la recursión.
    También es necesario conocer el estado de la máquina antes de evaluar cada expresión y cuáles son sus entornos.
    Se utiliza un parámetro auxiliar "en_bucle" para saber si la expresión que se está evaluando se encuentra 
    dentro de un bucle: atendiendo a la especificación del lenguaje, "continue" y "break" solo están permitidos dentro de bucles.

  *)
  Fixpoint eval_yul (f : nat) (expr : A.yul_expr) (env : A.yul_env) (fenv: A.yul_fun_env) (state : D.dialect_state_t) (en_bucle: bool) {struct f} : (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * yul_control) :=
    match f with
    (*Cuando se quiera evaluar un programa en Yul, se debe de proporcionar un f lo suficientemente grande para evitar agotar fuel*)
    | O => ([], env, fenv, state, Yul_Error "f agotado")
    | S f' => 
      match expr with
      | A.YulConst v => ([v], env, fenv, state, Yul_Running)
      | A.YulBreak =>
        if en_bucle then ([], env, fenv, state, Yul_Break)
        else ([], env, fenv, state, Yul_Error "break fuera de bucle; no permitido")
      | A.YulContinue =>
        if en_bucle then ([], env, fenv, state, Yul_Continue)
        else ([], env, fenv, state, Yul_Error "continue fuera de bucle; no permitido")
      | A.YulBlock inst => (*se utiliza eval_list para evaluar múltiples instrucciones*)
        (* Hoisting: registrar todas las funciones del bloque antes de ejecutar ninguna instrucción *)
        let fenv_hoisted := hoist_funcs inst (abrir_entorno_funcs fenv) in
        let '(res_b, env_b, fenv_b, state_b, st_b) := eval_list f' inst (abrir_entorno_vars env) fenv_hoisted state en_bucle in
          (res_b, cerrar_entorno_vars env_b, cerrar_entorno_funcs fenv_b, state_b, st_b)
      | A.YulLeave =>
        ([], env, fenv, state, Yul_Leave)
      | A.YulOp op args =>
        (*Primero, se evalúan los argumentos*)
        let '(vals, env_final, fenv_final, s_final, st) := eval_argumentos f' args env fenv state en_bucle in
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
        let '(valores, env_i, fenv_i, state_i, st) := eval_yul f' var_expr env fenv state en_bucle in
        match st with
        | Yul_Running =>
            match agregar_vars nombres valores env_i with
            | Some nuevo_env => ([], nuevo_env, fenv_i, state_i, Yul_Running)
            | None => ([], env_i, fenv_i, state_i, Yul_Error "Variable ya declarada o numero de variables no coincide con los valores que devuelve la funcion")
            end
        | _ => (valores, env_i, fenv_i, state_i, st)
        end
      | A.YulAsignar nombres var_expr =>
        let '(valores, env_i, fenv_i, state_i, st) := eval_yul f' var_expr env fenv state en_bucle in
        match st with
        | Yul_Running =>
            match actualizar_vars nombres valores env_i with
            | Some nuevo_env => ([], nuevo_env, fenv_i, state_i, Yul_Running)
            | None => ([], env_i, fenv_i, state_i, Yul_Error "Variable no definida o número de valores incorrecto")
            end
        | _ => (valores, env_i, fenv_i, state_i, st)
        end
      | A.YulVar nom =>
        match buscar_variable nom env with
        | Some v => ([v], env, fenv, state, Yul_Running)
        | None => ([], env, fenv, state, Yul_Error ("Variable no definida: " ++ nom))
        end
      | A.YulIf cond inst =>
        let '(res, env1, fenv1, state1, status1) := eval_yul f' cond env fenv state en_bucle in
            match status1 with
            | Yul_Running => 
                if (is_true res) 
                then
                  let fenv1_hoisted := hoist_funcs inst (abrir_entorno_funcs fenv1) in
                  let '(res2,env2,fenv2,state2,status2) := eval_list f' inst (abrir_entorno_vars env1) fenv1_hoisted state1 en_bucle in
                  (res2, cerrar_entorno_vars env2, cerrar_entorno_funcs fenv2, state2, status2)
                else ([], env1, fenv1, state1, Yul_Running)
            | _ => (res, env1, fenv1, state1, status1)
            end
      | A.YulFunc nom params rets inst =>
        let n_func := {| f_params := params; f_ret := rets; f_inst := inst |} in
        ([], env, (nom, n_func) :: fenv, state, Yul_Running)
      | A.YulSwitch cond casos def =>
        let '(res_c, env_c, fenv_c, state_c, st_c) := eval_yul f' cond env fenv state en_bucle in
        match st_c with
        | Yul_Running =>
            let v_evaluado :=
            match res_c with
            | v :: _ => v
            | [] => D.default_value
            end in
            let fix buscar (l : list (D.value_t * list A.yul_expr)) :=
              match l with
              | [] => (*default: aplicar hoisting al cuerpo del caso por defecto*)
                  let fenv_def_hoisted := hoist_funcs def (abrir_entorno_funcs fenv_c) in
                  let '(r,e,fe,s,st) :=
                    eval_list f' def (abrir_entorno_vars env_c) fenv_def_hoisted state_c en_bucle in
                  (r, cerrar_entorno_vars e, cerrar_entorno_funcs fe, s, st)
              | (val_caso, cuerpo) :: resto =>
                  if D.eqb v_evaluado val_caso then
                    let fenv_caso_hoisted := hoist_funcs cuerpo (abrir_entorno_funcs fenv_c) in
                    let '(r,e,fe,s,st) := eval_list f' cuerpo (abrir_entorno_vars env_c) fenv_caso_hoisted state_c en_bucle in
                    (r, cerrar_entorno_vars e, cerrar_entorno_funcs fe, s, st)
                  else buscar resto
              end
            in buscar casos
        | fallo => ([], env_c, fenv_c, state_c, fallo)
        end
      | A.YulFor init cond post cuerpo =>
        (*
          ejecución ini: el bloque init abre su propio scope.
          Las funciones declaradas en init son visibles en el resto del for
          (la especificación dice que el scope de init se extiende a todo el bucle).
        *)
        let fenv_init_hoisted := hoist_funcs init (abrir_entorno_funcs fenv) in
        let (p, ctrl) := eval_list f' init (abrir_entorno_vars env) fenv_init_hoisted state en_bucle in
        let (p0, si) := p in
        let (p1, fei) := p0 in
        let (_, ei) := p1 in
        match ctrl with
        | Yul_Running => 
            let '(r_f, e_f, fe_f, s_f, st_f) := eval_bucle cond cuerpo post f' ei fei si false in
            ([], cerrar_entorno_vars e_f, cerrar_entorno_funcs fe_f, s_f, st_f)
        | Yul_Leave => ([], cerrar_entorno_vars ei, cerrar_entorno_funcs fei, si, Yul_Leave)
        | _ => ([], cerrar_entorno_vars ei, cerrar_entorno_funcs fei, si, ctrl)
        end
      | A.YulCall nom args =>
        let '(vals, env_a, fenv_a, state_a, st) := eval_argumentos f' args env fenv state en_bucle in (*Primero evalúa argumentos*)
        match st with
        | Yul_Running =>
          match buscar_funcion nom fenv_a with
          | Some func => (*llamada a función: ejecución de las instrucciones que la conforman con los parámetros de entrada*)
            let env_local := combinar_params (f_params func) vals ++ List.map (fun r => (r, D.default_value)) (f_ret func) in
            let fenv_func_hoisted := hoist_funcs (f_inst func) fenv_a in
            let '(_, env_post, _, state_post, st_post) := eval_list f' (f_inst func) env_local fenv_func_hoisted state_a en_bucle in
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
  with eval_list (f : nat) (l : list A.yul_expr) (env : A.yul_env) (fenv : A.yul_fun_env) (state : D.dialect_state_t) (en_bucle: bool) {struct f}: (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * yul_control) :=
    match f with
    | O => ([], env, fenv, state, Yul_Error "Sin fuel en eval_lista")
    | S f' =>
        match l with
        | nil => ([], env, fenv, state, Yul_Running)
        | e :: rest => (*ejecuta la primera instrucción de la lista*)
            let '(res, env1, fenv1, state1, status1) := eval_yul f' e env fenv state en_bucle in
            match status1 with
            | Yul_Running => eval_list f' rest env1 fenv1 state1 en_bucle (*sigue ejecutando el resto de instrucciones de la lista hasta llegar a la última o agotar fuel*)
            | _ => (res, env1, fenv1, state1, status1)
            end
        end
    end
  with eval_argumentos (f : nat) (l : list A.yul_expr) (e : A.yul_env) (fe : A.yul_fun_env) (s : D.dialect_state_t) (en_bucle : bool) {struct f}: (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * yul_control) :=
    match f with
    | O => ([], e, fe, s, Yul_Error "Sin fuel en argumentos")
    | S f' =>
      match l with
      | [] => ([], e, fe, s, Yul_Running)
      | x :: xs => 
        (*Evalúa argumentos de uno en uno*)
        let '(rest, e', fe', s', st') := eval_argumentos f' xs e fe s en_bucle in 
        match st' with
        | Yul_Running => 
          let '(res, e'', fe'', s'', st'') := eval_yul f' x e' fe' s' en_bucle in
          match st'' with
          | Yul_Running => ((res ++ rest)%list, e'', fe'', s'', Yul_Running)
          | _ => ([], e'', fe'', s'', st'')
          end
        | _ => ([], e', fe', s', st')
        end
      end
    end
    with eval_bucle(cond : yul_expr) (cuerpo post : list yul_expr) (f : nat) (ei : yul_env) (fei : yul_fun_env) (si : D.dialect_state_t) (en_bucle: bool) {struct f} : (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * yul_control) :=
      (*Solo se permite break y continue en el cuerpo de instrucciones: en_bucle solo es true cuando se evalúa cuerpo*)
      match f with
      | O => ([], ei, fei, si, Yul_Error "fuel agotado en For")
      | S f' =>
        match eval_yul f' cond ei fei si false with (*evalúa condición*)
        | (res_c, e_c, fe_c, s_c, Yul_Running) =>
          if is_true res_c then (*condición verdadera -> se ejecuta el cuerpo de instrucciones*)
            let fe_cuerpo_hoisted := hoist_funcs cuerpo (abrir_entorno_funcs fe_c) in
            match eval_list f' cuerpo (abrir_entorno_vars e_c) fe_cuerpo_hoisted s_c true with
            | (_, e_b, fe_b, s_b, Yul_Break) => (*fin ejecución bucle: se finaliza con estado Running*)
              ([], cerrar_entorno_vars e_b, cerrar_entorno_funcs fe_b, s_b, Yul_Running)
            | (_, e_b, fe_b, s_b, Yul_Running)
            | (_, e_b, fe_b, s_b, Yul_Continue) =>
              let e_b_restored := cerrar_entorno_vars e_b in
              let fe_b_restored := cerrar_entorno_funcs fe_b in
              let fe_post_hoisted := hoist_funcs post (abrir_entorno_funcs fe_b_restored) in
              match eval_list f' post (abrir_entorno_vars e_b_restored) fe_post_hoisted s_b false with (*ejecuta post*)
              | (_, e_p, fe_p, s_p, Yul_Running) => (*siguiente iteración*)
                eval_bucle cond cuerpo post f' (cerrar_entorno_vars e_p) (cerrar_entorno_funcs fe_p) s_p false
              | (_, e_p, fe_p, s_p, Yul_Leave) =>
                ([], cerrar_entorno_vars e_p, cerrar_entorno_funcs fe_p, s_p, Yul_Leave)
              | (_, e_p, fe_p, s_p, Yul_Error msg) =>
                ([], cerrar_entorno_vars e_p, cerrar_entorno_funcs fe_p, s_p, Yul_Error msg)
              | (_, _, fe_p, s_p, _ ) =>
                ([], e_b_restored, fe_b_restored, s_b, Yul_Error "break o continue no permitidos en post")
              end
            | (_, e_b, fe_b, s_b, Yul_Leave) =>
              ([], cerrar_entorno_vars e_b, cerrar_entorno_funcs fe_b, s_b, Yul_Leave)
            | (_, e_b, fe_b, s_b, st) =>
              ([], cerrar_entorno_vars e_b, cerrar_entorno_funcs fe_b, s_b, st)
            end
          else ([], e_c, fe_c, s_c, Yul_Running) (*condición evalúa a falso -> fin ejecución bucle*)
        | (_, e_c, fe_c, s_c, st) => (*Error al evaluar condición*)
          ([], e_c, fe_c, s_c, st)
        end
      end.

  Definition ejecutar_eval_bloque (ast_list : list A.yul_expr) (env : A.yul_env) (fenv : A.yul_fun_env) (state : D.dialect_state_t) : (list D.value_t * A.yul_env * A.yul_fun_env * D.dialect_state_t * Status.t) :=
    let '(res, env_f, fenv_f, state_f, final_c) := eval_list 5000 ast_list env fenv state false in
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