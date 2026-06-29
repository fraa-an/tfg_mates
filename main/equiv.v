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

    (*Corrección de búsqueda de variable en entorno*)
    Lemma existsb_env_in : forall (env : A.yul_env) (n : string) (v : D.value_t), In (n, v) env -> existsb (fun '(m, _) => String.eqb n m) env = true.
    Proof.
      (*Inducción sobre el entorno*)
      induction env as [| [n' v'] resto IH]; intros n v Hin.
      - (*Hin: In (n,v) [], lo que es imposible*) contradiction.
      - simpl. destruct Hin as [Heq | Hin].
        + (*Heq: (n',v')=(n,v): la variable está en la cabeza*) 
          inversion Heq; subst. rewrite String.eqb_refl. reflexivity.
        + (*Hin: In (n,v) resto: la variable está en la cola*) 
          apply IH in Hin.
          destruct (String.eqb n n').
          * reflexivity.
          * exact Hin.
    Qed.


    (*Corrección del filtrado en entornos de restringe_env: si todas las variables de env2 están en env1, el filtro no borra ninguna variable*)
    Lemma filter_env_id : forall (env1 env2 : A.yul_env), (forall n v, In (n, v) env1 -> existsb (fun '(m, _) => String.eqb n m) env2 = true) ->
        filter (fun '(n, _) => existsb (fun '(m, _) => String.eqb n m) env2) env1 = env1.
    Proof.
      (*Inducción sobre env1*)
      induction env1 as [| [k v'] resto IH]; intros env2 H.
      - (*filter sobre [] = []*) reflexivity.
      - simpl.
        assert (H_h : existsb (fun '(m, _) => String.eqb k m) env2 = true).
        { apply (H k v'). left. reflexivity. }
        rewrite H_h. 
        (*(k,v')::filter...resto=(k,v')::resto*)
        f_equal. (*filter...resto=resto*)
        apply IH. (*aplica IH*)
        intros n' v'' Hin. (*Hin: In (n',v'') resto*)
        apply (H n' v''). (*la cabeza del entorno no coincide con (n',v'')-> debe coincidir el resto -> aplica Hin*)
        right. exact Hin.
    Qed.

    (*Si se restringe un entorno a sí mismo, se obtiene el propio entorno*)
    Lemma restringe_env_mismo : forall (env : A.yul_env), restringe_env env env = env.
    Proof.
      intros env.
      unfold restringe_env.
      apply filter_env_id.
      intros n v Hin.
      apply (existsb_env_in env n v).
      exact Hin.
    Qed.

    (*Dos expresiones son equivalentes si para el mismo estado, entornos y fuel, producen el mismo resultado*)
    Definition expr_equiv (e1 e2 : yul_expr) : Prop :=
        forall f env fenv state en_bucle,
            eval_yul f e1 env fenv state en_bucle = eval_yul f e2 env fenv state en_bucle.

    (*Dos conjuntos de instrucciones (o listas) son equivalentes si para el mismo estado, entornos y fuel, producen el mismo resultado*)
    Definition list_equiv (l1 l2 : list yul_expr) : Prop :=
        forall f env fenv state en_bucle,
            eval_list f l1 env fenv state en_bucle = eval_list f l2 env fenv state en_bucle.
    
    Definition expr_list_equiv (e : yul_expr) (l : list yul_expr) : Prop :=
    forall env fenv state en_bucle res env' fenv' state',
      (exists f, eval_yul f e env fenv state en_bucle = (res, env', fenv', state', Yul_Running)) <->
      (exists f, eval_list f l env fenv state en_bucle = (res, env', fenv', state', Yul_Running)).

    (*Yul no tiene explícitamente skip como instrucción: se considera una lista de instrucciones vacía*)
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
      rewrite app_nil_r. (*l++[]=l*)
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

    (*Un condicional cuando la condición es falsa no ejecuta nada*)
    Theorem yul_if_false : forall (v : D.value_t) (inst : list yul_expr),
      D.is_true_value v = false -> expr_list_equiv (YulIf (YulConst v) inst) ([]).
    Proof.
      intros v inst Hv.
      unfold expr_list_equiv.
      intros env fenv state res env' fenv' state'.
      split; intros H.
      - (*->*)
        destruct H as [f Hif].
        destruct f as [|f']; inversion Hif.
        destruct f' as [|f'']. inversion Hif.
        simpl in Hif. (*despelegado del condicional*)
        rewrite Hv in Hif. (*Hv: D.is_true_value v = false -> se 'sale' del condicional*)
        inversion Hif. subst.
        exists 1. (*fuel necesario para ejecutar []*) 
        simpl. rewrite Hv. reflexivity.
      - (*<-*)
        destruct H as [f H'].
        destruct f as [|f']. inversion H'.
        simpl in H'. inversion H'. subst.
        exists 2. (*fuel necesario para eval_yul->YulIf y para evaluar condición*)
        simpl. rewrite Hv. reflexivity.
    Qed.

    (*Bucle con condición falsa no ejecuta ninguna instrucción de cuerpo ni post*)
    Theorem yul_for_false : forall (v : D.value_t) (post cuerpo : list yul_expr),
      D.is_true_value v = false -> expr_list_equiv (YulFor [] (YulConst v) post cuerpo) ([]).
    Proof.
      intros v post cuerpo Hv.
      unfold expr_list_equiv.
      intros env fenv state res env' fenv' state'.
      split; intros H.
      - (*->*)
        destruct H as [f Hfor].
        destruct f as [|f']. inversion Hfor.
        destruct f' as [|f'']. inversion Hfor.
        destruct f'' as [|f''']. inversion Hfor.
        simpl in Hfor.
        rewrite Hv in Hfor.
        inversion Hfor. subst.
        exists 1. simpl. reflexivity.
      - (*<-*)
        destruct H as [f H'].
        destruct f as [|f']. inversion H'.
        simpl in H'. inversion H'. subst.
        exists 3. (*fuel necesario para eval_yul->YulFor, evaluar [] de init y evaluar condición del bucle*)
        simpl. 
        rewrite Hv. reflexivity.
    Qed.

    Definition cond_equiv_true (cond : yul_expr) : Prop :=
    forall f env fenv state en_bucle res env' fenv' state',
      eval_yul f cond env fenv state en_bucle = (res, env', fenv', state', Sem.Yul_Running) ->
      match res with
      | v :: _ => D.is_true_value v = true
      | []     => False
      end.

    (*Lema para probar que no puede aparecer break/continue fuera de un bucle*)
    Lemma no_break_continue : forall f,
      (*eval_yul con en_bucle=false no puede devolver un estado de control break/continue*)
      (forall expr env fenv state res env' fenv' state' ctrl,
         eval_yul f expr env fenv state false = (res, env', fenv', state', ctrl) ->
         ctrl <> Yul_Break /\ ctrl <> Yul_Continue)
      /\
      (*eval_list con en_bucle=false no puede devolver un estado de control break/continue*)
      (forall l env fenv state res env' fenv' state' ctrl,
         eval_list f l env fenv state false = (res, env', fenv', state', ctrl) ->
         ctrl <> Yul_Break /\ ctrl <> Yul_Continue)
      /\
      (*eval_argumentos con en_bucle=false no puede devolver un estado de control break/continue*)
      (forall args env fenv state res env' fenv' state' ctrl,
         eval_argumentos f args env fenv state false = (res, env', fenv', state', ctrl) ->
         ctrl <> Yul_Break /\ ctrl <> Yul_Continue)
      /\
      (*eval_bucle no puede devolver un estado de control break/continue: la ejecución de un bucle
       siempre termina o en estado Running o con error. Si dentro del bucle (en el cuerpo) hay break/continue,
       se trata dentro del bucle *)
      (forall cond cuerpo post env_orig ei fei si en_bucle res env' fenv' state' ctrl,
         eval_bucle cond cuerpo post env_orig f ei fei si en_bucle 
           = (res, env', fenv', state', ctrl) ->
         ctrl <> Yul_Break /\ ctrl <> Yul_Continue).
    Proof.
      intro f.
      induction f as [f IH] using (well_founded_induction Wf_nat.lt_wf). (*inducción fuerte sobre f*)
      (*Pe: propiedad sobre eval_yul expr*)
      set (Pe := fun g => forall expr env fenv state res env' fenv' state' ctrl,
        eval_yul g expr env fenv state false = (res, env', fenv', state', ctrl) ->
        ctrl <> Yul_Break /\ ctrl <> Yul_Continue).
      (*Pe: propiedad sobre eval_list*)
      set (Pl := fun g => forall l env fenv state res env' fenv' state' ctrl,
        eval_list g l env fenv state false = (res, env', fenv', state', ctrl) ->
        ctrl <> Yul_Break /\ ctrl <> Yul_Continue).
      (*Pe: propiedad sobre eval_argumentos*)
      set (Pa := fun g => forall args env fenv state res env' fenv' state' ctrl,
        eval_argumentos g args env fenv state false = (res, env', fenv', state', ctrl) ->
        ctrl <> Yul_Break /\ ctrl <> Yul_Continue).
      (*Pe: propiedad sobre eval_bucle*)
      set (Pb := fun g => forall cond cuerpo post env_orig ei fei si en_bucle res env' fenv' state' ctrl,
        eval_bucle cond cuerpo post env_orig g ei fei si en_bucle = (res, env', fenv', state', ctrl) ->
        ctrl <> Yul_Break /\ ctrl <> Yul_Continue).
      assert (IHe : forall g, g < f -> Pe g) by (intros g Hg; exact (proj1 (IH g Hg))).
      assert (IHl : forall g, g < f -> Pl g) by (intros g Hg; exact (proj1 (proj2 (IH g Hg)))).
      assert (IHa : forall g, g < f -> Pa g) by (intros g Hg; exact (proj1 (proj2 (proj2(IH g Hg))))).
      assert (IHb : forall g, g < f -> Pb g) by (intros g Hg; exact (proj2 (proj2 (proj2 (IH g Hg))))).
      destruct f as [| f'].
      - (* f = 0 *)
        split; [| split; [| split]].
        + intros expr env fenv state res env' fenv' state' ctrl Heval.
          simpl in Heval. inversion Heval. subst. split; discriminate.
        + intros l env fenv state res env' fenv' state' ctrl Heval.
          simpl in Heval. inversion Heval. subst. split; discriminate.
        + intros args env fenv state res env' fenv' state' ctrl Heval.
          simpl in Heval. inversion Heval. subst. split; discriminate.
        + intros cond cuerpo post env_orig ei fei si en_bucle res env' fenv' state' ctrl Heval.
          simpl in Heval. inversion Heval. subst. split; discriminate.
      - (* f = S f' *)
        assert (Hf' : f' < S f') by lia.
        split; [| split; [| split]].
        + (* eval_yul *)
          intros expr env fenv state res env' fenv' state' ctrl Heval.
          destruct expr as [v|op args|nombres valor|nombres valor|nombre_var|cond inst|cond casos default|ini cond post inst|nombre params ret inst|nombre args|inst_b| | |]; simpl in Heval.
          * (*YulConst*)
            inversion Heval; subst; split; discriminate.
          * (*YulOp*)
            destruct (eval_argumentos f' args env fenv state false) as [[[[ra ea] fea] sa] ctrla] eqn:Ha.
            pose proof (IHa f' Hf' _ _ _ _ _ _ _ _ _ Ha) as Hxa.
            (*En Heval, ninguna rama produce break ni continue: se prueba por reducción al absurdo que dichos resultados son imposibles
              El resto de posibles estados se obtienen con Heval, y son por construcción distintos a break/continue*)
            destruct ctrla; try (exfalso; apply (proj1 Hxa); reflexivity); try (exfalso; apply (proj2 Hxa); reflexivity); try (inversion Heval; subst; split; discriminate).
            destruct (D.execute_opcode sa op ra) as [[ro so] stso].
            destruct stso; inversion Heval; subst; split; discriminate.
          * (*YulLet*)
            destruct (eval_yul f' valor env fenv state false) as [[[[rv ev] fev] sv] ctrlv] eqn:Hv.
            pose proof (IHe f' Hf' _ _ _ _ _ _ _ _ _ Hv) as Hxv.
            destruct ctrlv; try (exfalso; apply (proj1 Hxv); reflexivity); try (exfalso; apply (proj2 Hxv); reflexivity); try (inversion Heval; subst; split; discriminate).
            destruct (agregar_vars nombres rv ev); inversion Heval; subst; split; discriminate.
          * (*YulAsignar*)
            destruct (eval_yul f' valor env fenv state false) as [[[[rv ev] fev] sv] ctrlv] eqn:Hv.
            pose proof (IHe f' Hf' _ _ _ _ _ _ _ _ _ Hv) as Hxv.
            destruct ctrlv; try (exfalso; apply (proj1 Hxv); reflexivity); try (exfalso; apply (proj2 Hxv); reflexivity); try (inversion Heval; subst; split; discriminate).
            destruct (actualizar_vars nombres rv ev); inversion Heval; subst; split; discriminate.
          * (*YulVar*)
            destruct (buscar_variable nombre_var env); inversion Heval; subst; split; discriminate.
          * (*YulIf*)
            destruct (eval_yul f' cond env fenv state false) as [[[[rc ec] fec] sc] ctrlc] eqn:Hc.
            pose proof (IHe f' Hf' _ _ _ _ _ _ _ _ _ Hc) as Hxc.
            destruct ctrlc; try (exfalso; apply (proj1 Hxc); reflexivity); try (exfalso; apply (proj2 Hxc); reflexivity); try (inversion Heval; subst; split; discriminate).
            destruct (is_true rc).
            -- (*rc=true*)
              destruct (eval_list f' inst ec fec sc false) as [[[[ri ei] fei] si] ctrli] eqn:Hi.
              pose proof (IHl f' Hf' _ _ _ _ _ _ _ _ _ Hi) as Hxi.
              destruct ctrli; try (exfalso; apply (proj1 Hxi); reflexivity); try (exfalso; apply (proj2 Hxi); reflexivity); try (inversion Heval; subst; split; discriminate).
            -- (*rc=false*)
              inversion Heval; subst; split; discriminate.
          * (*YulSwitch*)
            destruct (eval_yul f' cond env fenv state false) as [[[[rc ec] fec] sc] ctrlc] eqn:Hc.
            pose proof (IHe f' Hf' _ _ _ _ _ _ _ _ _ Hc) as Hxc.
            destruct ctrlc; try (exfalso; apply (proj1 Hxc); reflexivity); try (exfalso; apply (proj2 Hxc); reflexivity); try (inversion Heval; subst; split; discriminate).
            revert Heval.
            induction casos as [| [vc cc] casos' IHcasos].
            -- simpl.
               destruct (eval_list f' default ec fec sc false) as [[[[rd ed] fed] sd] ctrld] eqn:Hd.
               intro Heval. pose proof (IHl f' Hf' _ _ _ _ _ _ _ _ _ Hd) as Hxd.
               destruct ctrld; try (exfalso; apply (proj1 Hxd); reflexivity); try (exfalso; apply (proj2 Hxd); reflexivity); try (inversion Heval; subst; split; discriminate).
            -- simpl.
               destruct (D.eqb (match rc with v :: _ => v | [] => D.default_value end) vc).
               ++ destruct (eval_list f' cc ec fec sc false) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
                  intro Heval. pose proof (IHl f' Hf' _ _ _ _ _ _ _ _ _ Hb) as Hxb.
                  destruct ctrlb; try (exfalso; apply (proj1 Hxb); reflexivity); try (exfalso; apply (proj2 Hxb); reflexivity); try (inversion Heval; subst; split; discriminate).
               ++ apply IHcasos.
          * (*YulFor*)
            destruct (eval_list f' ini env fenv state false) as [[[[ri ei] fei] si] ctrli] eqn:Hi.
            pose proof (IHl f' Hf' _ _ _ _ _ _ _ _ _ Hi) as Hxi.
            destruct ctrli; try (exfalso; apply (proj1 Hxi); reflexivity); try (exfalso; apply (proj2 Hxi); reflexivity); try (inversion Heval; subst; split; discriminate).
            apply (IHb f' Hf' cond inst post env ei fei si false res env' fenv' state' ctrl Heval).
          * (*YulFunc*)
            inversion Heval; subst; split; discriminate.
          * (*YulCall*)
            destruct (eval_argumentos f' args env fenv state false) as [[[[ra ea] fea] sa] ctrla] eqn:Ha.
            pose proof (IHa f' Hf' _ _ _ _ _ _ _ _ _ Ha) as Hxa.
            destruct ctrla; try (exfalso; apply (proj1 Hxa); reflexivity); try (exfalso; apply (proj2 Hxa); reflexivity); try (inversion Heval; subst; split; discriminate).
            destruct (buscar_funcion nombre fea) as [y|]; try (inversion Heval; subst; split; discriminate).
            destruct (eval_list f' (f_inst y) (combinar_params (f_params y) ra ++ List.map (fun r => (r, D.default_value)) (f_ret y)) fea sa false) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
            pose proof (IHl f' Hf' _ _ _ _ _ _ _ _ _ Hb) as Hxb.
            destruct ctrlb; try (exfalso; apply (proj1 Hxb); reflexivity); try (exfalso; apply (proj2 Hxb); reflexivity); try (inversion Heval; subst; split; discriminate).
          * (*YulBlock*)
            destruct (eval_list f' inst_b env fenv state false) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
            pose proof (IHl f' Hf' _ _ _ _ _ _ _ _ _ Hb) as Hxb.
            destruct ctrlb; try (exfalso; apply (proj1 Hxb); reflexivity); try (exfalso; apply (proj2 Hxb); reflexivity); inversion Heval; subst; split; discriminate.
          * (*YulBreak fuera del cuerpo de un bucle -> produce Yul_Error*)
            inversion Heval; subst; split; discriminate.
          * (*YulContinue fuera del cuerpo de un bucle -> produce Yul_Error*)
            inversion Heval; subst; split; discriminate.
          * (*YulLeave -> distinto de break y continue por construcción*)
            inversion Heval; subst; split; discriminate.
        + (* eval_list *)
          intros l env fenv state res env' fenv' state' ctrl Heval.
          destruct l as [| h t].
          * (*para []*) 
            simpl in Heval. inversion Heval; subst; split; discriminate.
          * (*para una lista (h::t)*)
            simpl in Heval.
            destruct (eval_yul f' h env fenv state false) as [[[[rh eh] feh] sh] ctrlh] eqn:Hh.
            pose proof (IHe f' Hf' _ _ _ _ _ _ _ _ _ Hh) as Hxh.
            destruct ctrlh; try (exfalso; apply (proj1 Hxh); reflexivity); try (exfalso; apply (proj2 Hxh); reflexivity); try (inversion Heval; subst; split; discriminate).
            apply (IHl f' Hf') in Heval. exact Heval.
        + (* eval_argumentos *)
          intros args env fenv state res env' fenv' state' ctrl Heval.
          destruct args as [| h t].
          * (*para []*)
            simpl in Heval. inversion Heval; subst; split; discriminate.
          * (*para (h::t)*)
            simpl in Heval.
            destruct (eval_argumentos f' t env fenv state false) as [[[[rt et] fet] st] ctrlt] eqn:Ht.
            pose proof (IHa f' Hf' _ _ _ _ _ _ _ _ _ Ht) as Hxt.
            destruct ctrlt; try (exfalso; apply (proj1 Hxt); reflexivity); try (exfalso; apply (proj2 Hxt); reflexivity); try (inversion Heval; subst; split; discriminate).
            destruct (eval_yul f' h et fet st false) as [[[[rh eh] feh] sh] ctrlh] eqn:Hh.
            pose proof (IHe f' Hf' _ _ _ _ _ _ _ _ _ Hh) as Hxh.
            destruct ctrlh; try (exfalso; apply (proj1 Hxh); reflexivity); try (exfalso; apply (proj2 Hxh); reflexivity); try (inversion Heval; subst; split; discriminate).
        + (* eval_bucle *)
          intros cond cuerpo post env_orig ei fei si en_bucle res env' fenv' state' ctrl Heval.
          cbn [eval_bucle] in Heval. (*reescribe eval_bucle en Heval*)
          destruct (eval_yul f' cond ei fei si false) as [[[[rc ec] fec] sc] ctrlc] eqn:Hc.
          pose proof (IHe f' Hf' _ _ _ _ _ _ _ _ _ Hc) as Hxc.
          destruct ctrlc; try (exfalso; apply (proj1 Hxc); reflexivity); try (exfalso; apply (proj2 Hxc); reflexivity); try (inversion Heval; subst; split; discriminate).
          destruct (is_true rc) eqn:Htrue.
          * (*rc=true por Htrue*)
            destruct (eval_list f' cuerpo ec fec sc true) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb.
            destruct ctrlb.
            -- (*Running -> se ejecuta post*)
              destruct (eval_list f' post (restringe_env eb ec) feb sb false) as [[[[rp ep] fep] sp] ctrlp] eqn:Hp.
              pose proof (IHl f' Hf' _ _ _ _ _ _ _ _ _ Hp) as Hxp.
              destruct ctrlp; try (exfalso; apply (proj1 Hxp); reflexivity); try (exfalso; apply (proj2 Hxp); reflexivity); try (inversion Heval; subst; split; discriminate).
              apply (IHb f' Hf' cond cuerpo post env_orig (restringe_env ep (restringe_env eb ec)) fep sp false res env' fenv' state' ctrl Heval).
            -- (*Break*)
              inversion Heval; subst; split; discriminate.
            -- (*Continue -> se ejecuta post*)
              destruct (eval_list f' post (restringe_env eb ec) feb sb false) as [[[[rp ep] fep] sp] ctrlp] eqn:Hp.
              pose proof (IHl f' Hf' _ _ _ _ _ _ _ _ _ Hp) as Hxp.
              destruct ctrlp; try (exfalso; apply (proj1 Hxp); reflexivity); try (exfalso; apply (proj2 Hxp); reflexivity); try (inversion Heval; subst; split; discriminate).
              apply (IHb f' Hf' cond cuerpo post env_orig (restringe_env ep (restringe_env eb ec)) fep sp false res env' fenv' state' ctrl Heval).
            -- (*Leave*)
              inversion Heval; subst; split; discriminate.
            -- (*Error*)
              inversion Heval; subst; split; discriminate.
          * (*rc=false*)
            inversion Heval; subst; split; discriminate.
    Qed.

    (*eval_list de una lista vacía no produce ningún resultado y devuelve estado Running*)
    Lemma eval_list_vacia :
    forall f env fenv state en_bucle,
      f>0 ->
      eval_list f [] env fenv state en_bucle = ([], env, fenv, state, Yul_Running).
    Proof.
      intros f env fenv state en_bucle.
      destruct f; unfold eval_list. lia. reflexivity.
    Qed.

    (*
      Lema que prueba que un bucle donde la condición siempre es cierta y donde no hay breaks en el cuerpo,
      nunca puede finalizar con estado Running: solo finaliza por agotamiento de fuel (con Error) o con otro error de ejecución.
    *)
    Lemma bucle_no_running :
    forall cond post cuerpo, 
      cond_equiv_true cond ->
      (forall f env fenv state res env' fenv' state',
         eval_list f cuerpo env fenv state true 
           <> (res, env', fenv', state', Yul_Break)) ->
      forall n env e fe s res env' fenv' state' en_bucle,
        eval_bucle cond cuerpo post env n e fe s en_bucle = (res, env', fenv', state', Yul_Running) -> False.
    Proof.
      intros cond post cuerpo Hcond_equiv Hcuerpo.
      (*Inducción sobre fuel*)
      induction n as [|n IH]; intros env e fe s res env' fenv' state' en_bucle Heval.
      - (*n=0*)
        simpl in Heval. inversion Heval.
      - (*n>0*)
        cbn [eval_bucle] in Heval. (*reescribe eval_bucle en Heval *)
        destruct (no_break_continue n) as [Pe [Pl _]].
        destruct (eval_yul n cond e fe s false) as [[[[rc ec] fec] sc] ctrlc] eqn: Hc. (*ejecución condición*)
        destruct ctrlc; try inversion Heval.
        pose proof (Hcond_equiv n e fe s false rc ec fec sc Hc) as Htrue. (*condición siempre verdadera por hipótesis*)
        assert (Htrue': is_true rc=true).
        {destruct rc as [|v t]; simpl in *.
          - contradiction.
          - exact Htrue. }
        rewrite Htrue' in Heval.
        destruct (eval_list n cuerpo ec fec sc true) as [[[[rb eb] feb] sb] ctrlb] eqn:Hb. (*ejecución cuerpo*)
        destruct ctrlb.
        + (*Running -> ejecuta post*)
          destruct (eval_list n post (restringe_env eb ec) feb sb false) as [[[[rp ep] fep] sp] ctrlp] eqn:Hp.
          destruct ctrlp.
          * (*Running -> nueva iteración*)
            exact (IH env (restringe_env ep (restringe_env eb ec)) fep sp res env' fenv' state' false Heval).
          * (*Break -> imposible en post -> absurdo*) 
            exfalso. exact (proj1 (Pl post (restringe_env eb ec) feb sb rp ep fep sp Yul_Break Hp) eq_refl).
          * (*Continue -> imposible en post -> absurdo*) 
            exfalso. exact (proj2 (Pl post (restringe_env eb ec) feb sb rp ep fep sp Yul_Continue Hp) eq_refl).
          * (*Error*)
            inversion Heval.
          * (*Leave*)
            inversion Heval.
        + (*Break en cuerpo -> contradicción con la hipótesis*)
          exfalso. exact (Hcuerpo n ec fec sc rb eb feb sb Hb).
        + (*Continue -> ejecuta post y siguiente iteración*)
          destruct (eval_list n post (restringe_env eb ec) feb sb false) as [[[[rp ep] fep] sp] ctrlp] eqn:Hp.
          destruct ctrlp.
          * exact (IH env (restringe_env ep (restringe_env eb ec)) fep sp res env' fenv' state' false Heval).
          * exfalso. exact (proj1 (Pl post (restringe_env eb ec) feb sb rp ep fep sp Yul_Break Hp) eq_refl).
          * exfalso. exact (proj2 (Pl post (restringe_env eb ec) feb sb rp ep fep sp Yul_Continue Hp) eq_refl).
          * inversion Heval.
          * inversion Heval.
        + (*Error*)
          inversion Heval.
        + (*Leave*)
          inversion Heval.
    Qed.

    (*
      Teorema para probar que while true do skip no produce un cómputo terminante.
      Adaptado a la sintaxis de Yul, se prueba sobre for [] true cuerpo post, donde cuerpo no tiene ningún break.
      *)
    Theorem yul_while_true_no_running :
      forall f cond post cuerpo, 
        cond_equiv_true cond ->
        (forall f' env fenv state res env' fenv' state',
           eval_list f' cuerpo env fenv state true 
             <> (res, env', fenv', state', Yul_Break)) ->
        forall env state res env' fenv' state' en_bucle,
          eval_yul f (YulFor [] cond post cuerpo) env [] state en_bucle = (res, env', fenv', state', Yul_Running) -> False.
    Proof.
      intros [|f1] cond post cuerpo Hcond Hcuerpo env state res env' fenv' state' en_bucle Heval.
      - (*fuel=0*)
        simpl in Heval. inversion Heval.
      - (*fuel>0*)
        simpl in Heval.
        destruct f1 as [|f2].
        + (*sin fuel para evaluar condición*)
          simpl in Heval. inversion Heval.
        + (*se aplican eval_list_vacia por init y bucle_no_running*)
          rewrite (eval_list_vacia (S f2) env [] state en_bucle) in Heval; [| lia].
          eapply (bucle_no_running cond post cuerpo Hcond Hcuerpo (S f2) env env [] state res env' fenv' state' en_bucle Heval).
    Qed.

End YulEquivalences.