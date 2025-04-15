Require Import Kami.Syntax Kami.Notations.
Require Import Psatz Kami.Lib.Word PeanoNat.

Definition lgCeil i := S (Nat.log2_iter (pred (pred i)) 0 1 0).

Lemma lgCeilGe1: forall x, lgCeil x >= 1.
Proof.
  unfold lgCeil.
  induction x; simpl; lia.
Qed.

Lemma lgCeil_log2: forall x, S (Nat.log2 (pred x)) = lgCeil x.
Proof.
  intros; auto.
Qed.
  
Lemma pow2_lgCeil: forall x, 2 ^ (lgCeil x) >= x.
Proof.
  setoid_rewrite <- lgCeil_log2.
  intros.
  destruct x; simpl; try lia.
  destruct x; simpl; try lia.
  pose proof (Nat.log2_spec (S x) ltac:(lia)) as [? ?].
  simpl in *.
  lia.
Qed.

Lemma pow2_pow2: forall x, 2 ^ x + 2 ^ x = 2 ^ (S x).
Proof.
  induction x; simpl; try lia.
Qed.

Lemma pow2Ge1: forall x, 2 ^ x >= 1.
Proof.
  induction x; simpl; lia.
Qed.

Lemma lgCeil_pow2: forall x, x > 0 -> x = lgCeil (2 ^ x).
Proof.
  setoid_rewrite <- lgCeil_log2.
  intros.
  destruct x; simpl; try lia.
  repeat setoid_rewrite <- plus_n_O.
  rewrite pow2_pow2.
  rewrite Nat.log2_pred_pow2; try lia.
Qed.

Definition extractArbitraryRange ty sz (inst: LetExprSyntax ty (Bit sz)) (range: nat * nat):
  LetExprSyntax ty (Bit (fst range + 1 - snd range)) :=
  (LetE inst (fun i =>
                NormExpr (ConstExtract (snd range) (fst range + 1 - snd range) (sz - 1 - fst range)
                            (ZeroExtendTruncLsb _ (Var _ (SyntaxKind _) i))))).

Notation extractFieldExpr sz e start width :=
  (UniBit (TruncMsb start width)
     (UniBit (TruncLsb (start + width) (sz - (start + width))) e)).

Notation extractFieldExprDynamicWidth e start width :=
  (UniBit (TruncMsb start width)
     (ZeroExtendTruncLsb (start + width) e)).

Section ty.
  Variable ty: Kind -> Type.
  Definition TruncToSizeSigned sz m n (e: Bit n @# ty) :=
    SignExtendTruncLsb m (ZeroExtendTruncLsb sz e).

  Definition TruncToSizeUnsigned sz m n (e: Bit n @# ty) :=
    ZeroExtendTruncLsb m (ZeroExtendTruncLsb sz e).

  Definition ShuffleArray n k (inp: Array n k @# ty) m (inpStart: Bit m @# ty) : Array n k @# ty :=
    BuildArray (fun i => ReadArray inp (CABit Add [Const _ (natToWord _ (FinFun.Fin2Restrict.f2n i)); inpStart])).

  Definition TruncToDynamicSizeArrayUnsigned n k (a: Array n k @# ty) m (sz: Bit m @# ty) :=
    BuildArray
      (fun i =>
         ITE (BinBitBool (LessThan _) (Const _ (natToWord _ (FinFun.Fin2Restrict.f2n i))) sz)
           (ReadArrayConst a i)
           (Const ty Default)).

  Definition TruncToDynamicSizeArraySigned n width (a: Array n (Bit width) @# ty) m (sz: Bit m @# ty) :=
    BuildArray
      (fun i =>
         ITE (BinBitBool (LessThan _) (Const _ (natToWord _ (FinFun.Fin2Restrict.f2n i))) sz)
           (ReadArrayConst a i)
           (ITE (unpack Bool (ZeroExtendTruncMsb 1
                                (ReadArray a (CABit Add [sz; Const _ (wones m) ]))))
              (Const ty (wones width)) (Const ty (wzero width)))).

  Definition StaticIf (filter : bool) (pred: Bool @# ty) k (tExpr fExpr: k @# ty) :=
    if filter then ITE pred tExpr fExpr else fExpr.

End ty.

Definition Maybe k :=  STRUCT_TYPE {
                           "valid" :: Bool;
                           "data"  :: k }.

Definition Pair (A B: Kind) := STRUCT_TYPE {
                                   "fst" :: A;
                                   "snd" :: B }.

Section BitsCombiner.
  Variable ty: Kind -> Type.

  Fixpoint bitsCombiner (ls: list {x: nat * nat & Bit (snd x) @# ty}) :=
    match ls return Bit (fold_right (fun new sum => snd (projT1 new) + sum) 0 ls) @# ty with
    | nil => Const ty WO
    | x :: xs => BinBit (Concat _ _) (bitsCombiner xs) (projT2 x)
    end.
End BitsCombiner.

Local Open Scope kami_action.
Local Open Scope kami_expr.

Definition mkPair ty A B (a: A @# ty) (b: B @# ty) : Pair A B @# ty :=
  STRUCT { "fst" ::= a; "snd" ::= b }.

Definition Invalid {ty: Kind -> Type} {k} := STRUCT { "valid" ::= $$ false ; "data" ::= $$ (getDefaultConst k) }.

Definition nullStruct: Kind :=
  (Struct (fun i => @Fin.case0 _ i)).

Fixpoint BuildStructActionCont
         (ty: Kind -> Type) k
         n:
  forall (nameKinds : Fin.t n -> string * Kind)
         (acts  : forall i, ActionT ty (snd (nameKinds i)))
         (cont: (forall i, Expr ty (SyntaxKind (snd (nameKinds i)))) -> ActionT ty k),
    ActionT ty k :=
  match n return forall (nameKinds : Fin.t n -> string * Kind)
                        (acts  : forall i, ActionT ty (snd (nameKinds i)))
                        (cont  : (forall i, Expr ty (SyntaxKind (snd (nameKinds i)))) ->
                                 ActionT ty k), ActionT ty k with
  | 0 => fun nameKinds acts cont =>
           cont (fun i => @Fin.case0 (fun _ => Expr ty (SyntaxKind (snd (nameKinds i)))) i)
  | S m => fun nameKinds acts cont =>
             LETA next <- acts Fin.F1;
               @BuildStructActionCont
                 ty k m (fun i => nameKinds (Fin.FS i))
                 (fun i => acts (Fin.FS i))
                 (fun exps =>
                    cont (fun i =>
                            match i in Fin.t (S m) return
                                  forall (ks:
                                            Fin.t (S m) -> string * Kind),
                                    ty (snd (ks Fin.F1)) ->
                                    (forall i: Fin.t m, Expr ty (SyntaxKind (snd (ks (Fin.FS i))))) ->
                                    Expr ty (SyntaxKind (snd (ks i)))
                            with
                            | Fin.F1 _ => fun ks next exps => #next
                            | Fin.FS _ j => fun ks next exps => exps j
                            end nameKinds next exps))
end.

Definition BuildStructAction ty n (nameKinds: Fin.t n -> (string * Kind))
  (acts: forall i, ActionT ty (snd (nameKinds i))) :=
  BuildStructActionCont nameKinds acts (fun x => Return (BuildStruct nameKinds x)).

Lemma WfConcatActionT_BuildStructActionCont:
 forall m k n nameKinds acts cont,
   (forall (i:Fin.t n), WfConcatActionT (acts i) m) ->
   (forall x, WfConcatActionT (cont x) m) ->
   @WfConcatActionT type k (@BuildStructActionCont type k
                                              n nameKinds acts cont) m.
Proof.
  induction n; simpl; intros; auto.
  econstructor; [|intros; eapply IHn]; eauto.
Qed.

Section TruncExtend.
  Variable ty: Kind -> Type.
  Definition ZeroExtendTo outSz inSz (e: Bit inSz @# ty) := ZeroExtend (outSz - inSz) e.
  Definition SignExtendTo outSz inSz (e: Bit inSz @# ty) := SignExtend (outSz - inSz) e.
  Definition TruncLsbTo outSz restSz (e: Bit (outSz + restSz) @# ty) := UniBit (TruncLsb outSz restSz) e.
  Definition TruncMsbTo outSz restSz (e: Bit (restSz + outSz) @# ty) := UniBit (TruncMsb restSz outSz) e.
End TruncExtend.

Section Misc.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.
  Fixpoint countOnes ni no :=
    match ni as ni0 return Bit ni0 @# ty -> Bit no @# ty with
    | 0 => fun _ : Bit 0 @# ty => Const ty (wzero no)
    | S m => fun e : Bit (S m) @# ty =>
               (ITE (unpack Bool (TruncMsbTo 1 m (castBits (eq_sym (Nat.add_1_r m)) e))) (Const ty (natToWord no 1)) (Const ty (wzero no))) +
                 @countOnes m no (TruncLsbTo m 1 (castBits (eq_sym (Nat.add_1_r m)) e))
    end.

  Definition lg_bit n (e: Bit n @# ty) : Bit (Nat.log2_up (S n)) @# ty := ITE (isNotZero e) ($n + ~ (countLeadingZeros _ e)) $0.

  Definition lgFrac_bit n (e: Bit n @# ty) : Bool @# ty := countOnes (Nat.log2_up (S n)) e > $1.

  Definition lgCeil_bit n (e: Bit n @# ty) : Bit (Nat.log2_up (S n)) @# ty :=
    ($n + ~ (countLeadingZeros _ e)) + (ITE (countOnes (Nat.log2_up (S n)) e == $1) $0 $1).

  Definition remainderNonZero n (e: Bit n @# ty) (numBits: Bit (Nat.log2_up (S n)) @# ty): Bool @# ty :=
    isNotZero (e << ($n - numBits)).
End Misc.

Section Reducer.
  Variable A: Type.
  Variable ty: Kind -> Type.

  Section Struct.
    Variable sMap: A -> string.

    Section SameKindStruct.
      Context {k: Kind}.
      Theorem structIndexSameKind ls i:
        (snd (nth_Fin (map (fun a => (sMap a, k)) ls) i)) = k.
      Proof.
        induction ls.
        - apply Fin.case0.
          exact i.
        - fin_dep_destruct i.
          + reflexivity.
          + apply IHls.
      Defined.

      Definition castReadStructExpr {ls i ty} (e: snd (nth_Fin (map (fun a => (sMap a, k)) ls) i) @# ty) : k @# ty :=
        eq_rect _ (fun x => x @# ty) e _ (structIndexSameKind ls i).
    End SameKindStruct.

    Variable kMap: A -> Kind.
    Definition StructKind ls := Struct (fun i => nth_Fin (map (fun x => (sMap x, kMap x)) ls) i).

    Section Let.
      Variable letMap: forall a, kMap a ## ty.

      Local Open Scope kami_expr.
      Local Fixpoint structLetHelp (exprs: list { x : string * Kind & snd x @# ty }) (ls: list A):
        Struct (fun i => nth_Fin (map (@projT1 _ _) exprs ++ map (fun x => (sMap x, kMap x)) ls) i) ## ty.
      refine
        (match ls with
         | nil => RetE (@eq_rect _ _ _ (getStructVal exprs) _ _)
         | x :: xs => ( LETE next : kMap x <- letMap x;
                        (@eq_rect _ _ _ (structLetHelp (exprs ++ [existT _ (sMap x, kMap x) #next]) xs) _ _) )
         end).
      - abstract (rewrite app_nil_r; reflexivity).
      - abstract (rewrite map_app, <- app_assoc; reflexivity).
      Defined.

      Definition structLet: forall ls, StructKind ls ## ty := structLetHelp [].
    End Let.

    Section Action.
      Variable actionMap: forall a, ActionT ty (kMap a).

      Local Open Scope kami_expr.
      Local Open Scope kami_action.
      Local Fixpoint structActionHelp (exprs: list { x : string * Kind & snd x @# ty }) (ls: list A):
        ActionT ty (Struct (fun i => nth_Fin (map (@projT1 _ _) exprs ++ map (fun x => (sMap x, kMap x)) ls) i)).
      refine
        (match ls with
         | nil => Ret (@eq_rect _ _ _ (getStructVal exprs) _ _)
         | x :: xs => ( LETA next : kMap x <- actionMap x;
                        (@eq_rect _ _ _ (structActionHelp (exprs ++ [existT _ (sMap x, kMap x) #next]) xs) _ _) )
         end).
      - abstract (rewrite app_nil_r; reflexivity).
      - abstract (rewrite map_app, <- app_assoc; reflexivity).
      Defined.

      Definition structAction: forall ls, ActionT ty (StructKind ls) := structActionHelp [].
    End Action.
  End Struct.

  Section Red.
    Variable K: Kind.
    Variable RK: Kind.
    Variable red: list (K @# ty) -> RK @# ty.
    
    Section Let.
      Variable letMap: A -> K ## ty.

      Local Open Scope kami_expr.
      Local Fixpoint redLetHelp (exprs: list (K @# ty)) (ls: list A): RK ## ty :=
        (match ls with
         | nil => RetE (red exprs)
         | x :: xs => ( LETE next : K <- letMap x;
                        redLetHelp (exprs ++ [#next]) xs )
         end).

      Definition redLet: forall ls, RK ## ty := redLetHelp [].
    End Let.

    Section Action.
      Variable actionMap: A -> ActionT ty K.

      Local Open Scope kami_expr.
      Local Open Scope kami_action.
      Local Fixpoint redActionHelp (exprs: list (K @# ty)) (ls: list A): ActionT ty RK :=
        (match ls with
         | nil => Ret (red exprs)
         | x :: xs => ( LETA next : K <- actionMap x;
                        redActionHelp (exprs ++ [#next]) xs )
         end).

      Definition redAction: forall ls, ActionT ty RK := redActionHelp [].
    End Action.
  End Red.
End Reducer.

Section ReadWriteRegs.
  Local Open Scope kami_action.
  Definition readRegs prefix n (regs: list (RegInfo n)) ty (addr: Bit n @# ty) k : ActionT ty k :=
    redAction (@Kor _ k)
      (fun x => ( If (addr == Const ty (regAddr x))
                  then ( Read retVal : k <- ((prefix ++ "_") ++ (regName x))%string;
                         Ret #retVal )
                  else Ret (Const ty Default) as ret;
                  Ret #ret )) regs.

  Definition writeRegsPred prefix n (regs: list (RegInfo n)) ty
    (pred: Bool @# ty) (addr: Bit n @# ty) k (val: k @# ty) :=
    fold_right (fun x rest => ( If (addr == Const ty (regAddr x))
                                then (WriteIf pred Then ((prefix ++ "_") ++ (regName x))%string : k <- val; Retv)
                                else Retv;
                                rest ) ) Retv regs.

  Definition writeRegs prefix n (regs: list (RegInfo n)) ty (addr: Bit n @# ty) k (val: k @# ty) :=
    fold_right (fun x rest => ( If (addr == Const ty (regAddr x))
                                then ( Write ((prefix ++ "_") ++ (regName x))%string : k <- val; Retv )
                                else Retv;
                                rest ) ) Retv regs.

  Definition callReadRegFile k (name: string) ty n (idx: Bit n @# ty) : ActionT ty k :=
    ( Call ret : Array 1 k <- name (idx: Bit n);
      Ret (ReadArrayConst #ret Fin.F1) ).

  Definition callWriteRegFile (name: string) ty n (idx: Bit n @# ty) k (v: k @# ty) : ActionT ty Void :=
    ( Call name (STRUCT { "addr" ::= idx;
                          "data" ::= BuildArray (fun _ => v) } : WriteRq n (Array 1 k));
      Retv ).
End ReadWriteRegs.
