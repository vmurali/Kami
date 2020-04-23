Require Import Kami.Syntax Program.

Axiom cheat : forall {X},X.

Section Constants.

Fixpoint all_left_list{X Y}(zs : list (X + Y)) : option (list X) :=
  match zs with
  | [] => Some []
  | inl x :: zs' => match all_left_list zs' with
                    | None => None
                    | Some xs => Some (x :: xs)
                    end
  | inr _ :: _ => None
  end.

Definition FinFunc_cons{n}{X : Fin.t (S n) -> Type}(x : X F1)(f : forall i, X (FS i)) : forall i, X i.
Proof.
  intro i.
  dependent destruction i.
  - exact x.
  - exact (f i).
Defined.

Fixpoint all_left_Fin{n} : forall {X Y : Fin.t n -> Type}, (forall i : Fin.t n, X i + Y i) -> option (forall i, X i) :=
  match n return forall X Y : Fin.t n -> Type, (forall i : Fin.t n, X i + Y i) -> option (forall i, X i) with
  | 0 => fun X Y _ => Some (case0 _)
  | S m => fun X Y f => match f F1 with
                        | inl x => match @all_left_Fin m (fun i => X (FS i)) (fun i => Y (FS i)) (fun i => f (FS i)) with
                                   | None => None
                                   | Some g => Some (FinFunc_cons x g)
                                   end
                        | inr _ => None
                        end
  end.

Definition coerce_Const_Bool : ConstT Bool -> bool.
Proof.
  intro c.
  dependent destruction c.
  exact b.
Defined.

Definition back_to_Expr{ty k}(s : ConstT k + Expr ty (SyntaxKind k)) : Expr ty (SyntaxKind k) :=
  match s with
  | inl c => Const ty c
  | inr e => e
  end.

Definition squash_CABool{ty}(xs : list (ConstT Bool  + Expr ty (SyntaxKind Bool)))(op : CABoolOp) :
  ConstT Bool + Expr ty (SyntaxKind Bool) :=
  match all_left_list xs with
  | None => inr (CABool op (map back_to_Expr xs))
  | Some cs => inl (ConstBool (evalCABool op (map coerce_Const_Bool cs)))
  end.

Search _ (Fin.t _ -> bool).

Fixpoint Const_eqb{k} : ConstT k -> ConstT k -> bool.
Proof.
  destruct k; intros c1 c2;
  dependent destruction c1;
  dependent destruction c2.
  - exact (Bool.eqb b b0).
  - exact (weqb w w0).
  - exact (Fin_forallb (fun i => Const_eqb (k i) (fv i) (fv0 i))).
  - exact (Fin_forallb (fun i => Const_eqb k (fk i) (fk0 i))).
Defined.

Lemma weqb_refl : forall (n : nat)(x : word n), weqb x x = true.
Proof.
  intros.
  destruct (weqb x x) eqn:G.
  - reflexivity.
  - elim (weqb_false _ _ G eq_refl).
Qed.

Lemma Const_eqb_correct : forall (k : Kind)(c1 c2 : ConstT k), Const_eqb c1 c2 = true <-> c1 = c2.
Proof.
  dependent induction c1; dependent destruction c2.
  - split; intro.
    + destruct (eqb_true_iff b b0).
      rewrite (H0 H); reflexivity.
    + inversion H; apply eqb_true_iff; auto.
  - split; intro.
    + rewrite (weqb_true _ _ H); reflexivity.
    + rewrite H.
      apply weqb_refl.
  - split; intro.
    + f_equal.
      apply functional_extensionality_dep.
      intro.
      simpl in H0.
      unfold simplification_existT1 in H0.
      unfold solution_left in H0.
      unfold eq_rect_r in H0.
      unfold eq_rect in H0.
      unfold eq_sym in H0.
      unfold f_equal in H0.
      unfold simplification_existT2 in H0.
      assert (Eqdep.EqdepTheory.inj_pair2 nat (fun n => t n -> string) n fs fs eq_refl = eq_refl).
      admit.
      rewrite H1 in H0.
      assert (Eqdep.EqdepTheory.inj_pair2 nat (fun n => t n -> Kind) n fk fk eq_refl = eq_refl).
      admit.
      rewrite H2 in H0.
      rewrite H1 in H0.
      rewrite H2 in H0.
      simpl.
      Search _ Fin_forallb.
      rewrite Fin_forallb_correct in H0.
      apply H.
      apply H0.
    + simpl.
      unfold simplification_existT1.
      unfold solution_left.
      unfold eq_rect_r.
      unfold eq_rect.
      unfold eq_sym.
      unfold f_equal.
      unfold simplification_existT2.
      assert (Eqdep.EqdepTheory.inj_pair2 nat (fun n0 => t n0 -> string) n fs fs eq_refl = eq_refl).
      admit.
      rewrite H1.
      assert (Eqdep.EqdepTheory.inj_pair2 nat (fun n0 => t n0 -> Kind) n fk fk eq_refl = eq_refl).
      admit.
      rewrite H2.
      rewrite H1.
      rewrite H2.
      rewrite Fin_forallb_correct.
      intro.
      apply H.
      inversion H0.
      assert (fv = fv0).
      admit.
      rewrite H3; reflexivity.
  - split; intro.
    + f_equal.
      apply functional_extensionality.
      intro.
      simpl in H0.
      unfold solution_left in H0.
      unfold eq_rect_r in H0.
      unfold eq_rect in H0.
      unfold eq_sym in H0.
      unfold f_equal in H0.
      rewrite Fin_forallb_correct in H0.
      apply H.
      apply H0.
    + simpl.
      unfold solution_left.
      unfold eq_rect_r.
      unfold eq_rect.
      unfold eq_sym.
      unfold f_equal.
      rewrite Fin_forallb_correct.
      intro.
      apply H.
      assert (fk = fk0).
      admit.
      rewrite H1; reflexivity.
Admitted.

(* simplifies subexpressions which are composed entirely of constants and does branch elim
   when a predicate is constant *)
Fixpoint simplify_consts{ty k}(e : Expr ty (SyntaxKind k)) : ConstT k + Expr ty (SyntaxKind k).
Proof.
  dependent destruction e.
  (* Var *)
  - exact (inr (Var _ _ f)).
  (* Const *)
  - exact (inl c).
  (* UniBool *)
  - destruct (simplify_consts _ _ e) eqn:G.
    + dependent destruction c.
      destruct u eqn:U.
      exact (inl (ConstBool (negb b))).
    + exact (inr (UniBool u e0)).
  (* CABool *)
  - exact (squash_CABool (map (simplify_consts _ _) l) c).
  (* UniBit *)
  - admit.
  (* CABit *)
  - admit.
  (* BinBit *)
  - admit.
  (* BinBitBool *)
  - admit.
  (* ITE *)
  - destruct (simplify_consts _ _ e1) eqn:G1.
    + dependent destruction c.
      exact (simplify_consts _ _ (if b then e2 else e3)).
    + exact (inr (ITE e (back_to_Expr (simplify_consts _ _ e2))
                        (back_to_Expr (simplify_consts _ _ e3)))).
  (* Eq *)
  - destruct (simplify_consts _ _ e1) eqn:G1; destruct (simplify_consts _ _ e2) eqn:G2.
    + exact (inl (ConstBool (Const_eqb c c0))).
    + exact (inr (Eq (Const ty c) e)).
    + exact (inr (Eq e (Const ty c))).
    + exact (inr (Eq e e0)).
  (* ReadStruct *)
  - destruct (simplify_consts _ _ e) eqn:G.
    + dependent destruction c.
      exact (inl (fv i)).
    + exact (inr (ReadStruct e0 i)).
  (* BuildStruct *)
  - destruct (all_left_Fin (fun i => simplify_consts _ _ (fv i))).
    + exact (inl (ConstStruct _ _ c)).
    + exact (inr (BuildStruct _ _ (fun i => back_to_Expr (simplify_consts _ _ (fv i))))).
  (* ReadArray *)
  - admit.
  (* ReadArrayConst *)
  - admit.
  (* BuildArray *)
  - admit.
  (* Kor *)
  - admit.
  (* ToNative *)
  - admit.
Admitted.

End Constants.

Section AssocComConstantSquashing.

(* putting this in mothballs for now *)

Inductive Binop := AndOp | OrOp | XorOp.

Inductive PassedExpr ty k :=
  | JustConst : ConstT k -> PassedExpr ty k
  | JustVar : Expr ty (SyntaxKind k) -> PassedExpr ty k
  | Mixed : ConstT k -> Expr ty (SyntaxKind k) -> Binop -> PassedExpr ty k.

Fixpoint sep_consts{ty k}(e : Expr ty (SyntaxKind k)) : PassedExpr ty k.
Proof.
  dependent destruction e.
  (* Var *)
  - exact (JustVar (Var _ _ f)).
  (* Const *)
  - exact (JustConst _ c).
  (* UniBool *)
  - destruct (sep_consts _ _ e) eqn:G.
    (* JustConst *)
    + dependent destruction c.
      exact (JustConst ty (negb b)).
    (* JustVar *)
    + exact (JustVar (UniBool u e0)).
    (* Mixed *)
    + dependent destruction c.
      destruct b0.
      (* AndOp *)
      * exact (Mixed (negb b) (UniBool Neg e0) OrOp).
      (* OrOp *)
      * exact (Mixed (negb b) (UniBool Neg e0) AndOp).
      (* XorOp *)
      * exact (Mixed (negb b) e0 XorOp).
  (* CABool *)
  - admit.
  (* UniBit *)
  - admit.
  (* CABit *)
  - admit.
  (* BinBit *)
  - admit.
  (* BinBitBool *)
Admitted.

End AssocComConstantSquashing.
























