Require Import Kami.Syntax Kami.Notations.

(* TODO: move to KamiStdLib? *)
Definition extractArbitraryRange ty sz (inst: LetExprSyntax ty (Bit sz)) (range: nat * nat):
  LetExprSyntax ty (Bit (fst range + 1 - snd range)) :=
  (LetE inst (fun i =>
                NormExpr (ConstExtract (snd range) (fst range + 1 - snd range) (sz - 1 - fst range)
                            (ZeroExtendTruncLsb _ (Var _ (SyntaxKind _) i))))).

Notation extractFieldExpr sz e start width :=
  (UniBit (TruncMsb start width)
     (UniBit (TruncLsb (start + width) (sz - (start + width))) e)).

Notation extractFieldExprDynamicWidth e start width :=
  (UniBit (TruncLsb start width)
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

(* Useful Struct:
   TODO: move notation versions to StdLibKami*)
Definition Maybe k :=  STRUCT_TYPE {
                           "valid" :: Bool;
                           "data"  :: k }.

Definition Pair (A B: Kind) := STRUCT_TYPE {
                                   "fst" :: A;
                                   "snd" :: B }.

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
