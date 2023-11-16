Require Import Kami.AllNotations.

Section Named.
  Variable sz: nat.
  Variable name: string.
  Local Notation "@^ x" := (name ++ "_" ++ x)%string (at level 0).

  Definition IncrementerSpec :=
    MODULE {
      Register @^"counter" : Bit sz <- Default
      
      with Rule @^"send_and_inc_spec" :=
      ( Read counter: Bit sz <- @^"counter" ;
        Call "counterVal"(#counter + $2: _);
        Write @^"counter" <- #counter + $1;
        Retv )
      }.  
  
  (* The implementation which keeps incrementing a counter in one step and sends the value of the counter in the other *)
  Definition IncrementerImpl :=
    MODULE {
      Register @^"counter" : Bit sz <- Default
      with Register @^"pipe" : Bit sz <- Default
      with Register @^"pipeValid": Bool <- false

      with Rule @^"inc" :=
      ( Read pipeValid: Bool <- @^"pipeValid" ;
        If !#pipeValid
        then (  
          Read counter: Bit sz <- @^"counter" ;
          Write @^"pipe" <- #counter + $2;
          Write @^"counter" <- #counter + $1;
          Write @^"pipeValid" <- $$true;
          Retv )
        else Retv;
        Retv)

      with Rule @^"send" :=
      ( Read pipeValid: Bool <- @^"pipeValid" ;
        If #pipeValid
        then (  
          Read pipe: Bit sz <- @^"pipe" ;
          Call "counterVal"(#pipe: _);
          Write @^"pipeValid" <- $$false ;
          Retv )
        else Retv;
        Retv )
    }.
      

  (* The invariant connecting the state of the implementation with the
    state of the spec, including specifying the list of register register names, their types and values *)
  Record Incrementer_invariant (impl spec: RegsT) : Prop :=
    { counterImpl: word sz ;
      counterSpec: word sz ;
      pipeImpl: word sz;
      pipeValid: bool ;
      implEq : impl = (@^"counter", existT _ (SyntaxKind (Bit sz)) counterImpl)
                        :: (@^"pipe", existT _ (SyntaxKind (Bit sz)) pipeImpl)
                        :: (@^"pipeValid", existT _ (SyntaxKind Bool) pipeValid) :: nil ;
      specEq : spec = (@^"counter", existT _ (SyntaxKind (Bit sz))
                                           counterSpec)
                        :: nil;
      pipeImplRelation: pipeValid = true -> pipeImpl = counterSpec ^+ $2 ;
      counterSpecImpl1: pipeValid = true -> counterImpl = counterSpec ^+ $1;
      counterSpecImpl2: pipeValid = false -> counterImpl = counterSpec;
    }.

Ltac bsimplify_simulatingRule name :=
  right;
  exists name;
  eexists; split; [eauto| do 2 eexists; split; [discharge_SemAction|]].

(* 
  (* Proving the trace inclusion of the implementation with respect to the spec *)
  Theorem Incrementer_TraceInclusion:
    TraceInclusion (Base IncrementerImpl) (Base IncrementerSpec).
  Proof.
    (* discharge_simulation with the name of the record holding the invariant will discharge most
       of the trivial goals and requires the user to specify, for each implementation rule or method,
       either a specification rule or method that produces the same method calls
       while maintaining the state invariant or a nil step in the specification.
       The former is simplified using simplify_simulatingRule, with the rule name.
       The latter is simplified using simplify_nilStep.
       discharge_CommonRegisterAuto discharges the goals that require that two methods or a method and rule of
       the implementation are not combinable by automatically searching for at least one register
       with the two actions write to *)
    discharge_simulation Incrementer_invariant; discharge_CommonRegisterAuto; try discriminate.
    - specialize (pipeImplRelation H0).
      specialize (counterSpecImpl1 H0).
      bsimplify_simulatingRule @^"send_and_inc_spec"; subst.
      + rewrite wzero_wplus; auto.
      + simpl. discharge_string_dec.
        repeat (econstructor; eauto; simpl; subst); intro; try discriminate.
        rewrite wzero_wplus; auto.
    - simplify_nilStep.
      specialize (counterSpecImpl2 H0).
      econstructor; simpl; eauto; subst.
    - simplify_nilStep.
      destruct rv; [discriminate | ].
      specialize (counterSpecImpl2 eq_refl); subst.
      econstructor; simpl; eauto; subst; intro; try discriminate; rewrite wzero_wplus; auto.
    - simplify_nilStep.
      destruct rv; [ | discriminate].
      specialize (counterSpecImpl1 eq_refl).
      specialize (pipeImplRelation eq_refl).
      econstructor; simpl; eauto; subst.
      
      (* Note that while this example does not create spurious existentials, usually, there is a plethora of existentials created that can be instantiated with arbitrary values as they do not affect the proof. These goals are discharged with the following two commands*)
      Unshelve.
      all: repeat constructor.
Qed.
*)
End Named.
