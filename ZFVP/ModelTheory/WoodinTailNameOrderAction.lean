import ZFVP.ModelTheory.WoodinTailNamePoolAction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def tailTripleForcingFormula (φ : SetTheorySemisentence 3) : SetTheorySemisentence 6 :=
  f“P R x y z p. !(ordinaryForcingTranslation φ) P R P P p
    (!assignmentPrependFormula (!(numeralFormula 2))
      (!assignmentPrependFormula (!(numeralFormula 1))
        (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) z) y) x)”

@[irreducible] def tailValueOrderLawFormula : SetTheorySemisentence 12 :=
  f“P R o p Q S f g t u a b. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧ p ∈ P ∧
    !forcingNameFormula P Q ∧ !forcingNameFormula P S ∧ !forcingNameFormula P f ∧
    !forcingNameFormula P g ∧ !forcingNameFormula P t ∧ !forcingNameFormula P u ∧
    !forcingNameFormula P a ∧ !forcingNameFormula P b ∧ !tailInversePairForcingFormula P R Q S f g o ∧
    o ∈ !atomicMembershipFormula P R t Q ∧ o ∈ !atomicMembershipFormula P R u Q ∧
    !tailValueForcingFormula P R f t a o ∧ !tailValueForcingFormula P R f u b o →
    (!(tailTripleForcingFormula boundedPairMemberFormula) P R S t u p ↔
      !(tailTripleForcingFormula boundedPairMemberFormula) P R S a b p)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance tailTripleForcingFormula_defined (φ : SetTheorySemisentence 3) :
    Defined (fun v : Fin 6 → V ↦ v 5 ∈ forcingFormula (v 0) (v 1) φ
      (standardTuple ![v 2, v 3, v 4])) (tailTripleForcingFormula φ) := by
  refine ⟨fun v ↦ ?_⟩
  simp [tailTripleForcingFormula, standardTuple, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h
    exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
    exact h

theorem tailFunctionValueForcing_order_countable [Countable V]
    {P R top p : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (Q S f g τ σ a b : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hτ : top ∈ atomicMembership P R τ.val Q.val)
    (hσ : top ∈ atomicMembership P R σ.val Q.val)
    (ha : top ∈ tailFunctionValueForcing P R f.val τ.val a.val)
    (hb : top ∈ tailFunctionValueForcing P R f.val σ.val b.val) :
    p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, τ.val, σ.val]) ↔
      p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, a.val, b.val]) := by
  have hv (x y z : ForcingName P) :
      (fun i : Fin 3 ↦ (![x, y, z] i).val) = ![x.val, y.val, z.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl
      (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
  have hs := forcingFormula_iff_all_generics hR ht hp boundedPairMemberFormula ![S, τ, σ]
  have ht' := forcingFormula_iff_all_generics hR ht hp boundedPairMemberFormula ![S, a, b]
  rw [hv S τ σ] at hs
  rw [hv S a b] at ht'
  rw [hs, ht']
  apply forall_congr'
  intro G
  apply forall_congr'
  intro hG
  apply imp_congr_right
  intro hpG
  let A : ForcingContext V := ⟨P, R, top, G, hR, ht, hG⟩
  have htG : top ∈ G := hG.1.2.2.1 p hpG top ht.1 (ht.2 p hp)
  have h := (Defined.eval_iff _).mp
    ((A.formula_truth tailInversePairFormula ![Q, S, f, g]).mpr ⟨top, htG, hi⟩)
  have htQ : A.ofName τ ∈ A.ofName Q :=
    (forcingQuotientMk_mem_iff P R G hR hG.1 τ Q).mpr ⟨top, htG, hτ⟩
  have hsQ : A.ofName σ ∈ A.ofName Q :=
    (forcingQuotientMk_mem_iff P R G hR hG.1 σ Q).mpr ⟨top, htG, hσ⟩
  have hav := (A.tailFunctionValueForcing_truth f τ a).mp ⟨top, htG, ha⟩
  have hbv := (A.tailFunctionValueForcing_truth f σ b).mp ⟨top, htG, hb⟩
  have he := h.1.2.2.2 _ htQ _ hsQ
  change (⟨A.ofName τ, A.ofName σ⟩ₖ ∈ A.ofName S ↔
    ⟨(A.ofName f) ‘ (A.ofName τ), (A.ofName f) ‘ (A.ofName σ)⟩ₖ ∈ A.ofName S) at he
  rw [hav.2, hbv.2] at he
  change boundedPairMemberFormula.Evalb (fun i ↦ A.ofName (![S, τ, σ] i)) ↔
    boundedPairMemberFormula.Evalb (fun i ↦ A.ofName (![S, a, b] i))
  simpa [Defined.eval_iff, Matrix.vecHead, Matrix.vecTail] using he

private theorem tail_order_forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩
private theorem tail_order_forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩
private theorem tail_order_forall_seven_eq {β : Type*} (a b c d e f g : β)
    (F : β → β → β → β → β → β → β → Prop) :
    (∀ u v w x y z t, u = a → v = b → w = c → x = d → y = e → z = f → t = g →
      F u v w x y z t) ↔ F a b c d e f g :=
  ⟨fun h ↦ h a b c d e f g rfl rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z t hu hv hw hx hy hz ht ↦ by subst u v w x y z t; exact h⟩

theorem eval_tailValueOrderLawFormula (v : Fin 12 → V) :
    tailValueOrderLawFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) → v 3 ∈ v 0 →
        IsForcingName (v 0) (v 4) → IsForcingName (v 0) (v 5) →
        IsForcingName (v 0) (v 6) → IsForcingName (v 0) (v 7) →
        IsForcingName (v 0) (v 8) → IsForcingName (v 0) (v 9) →
        IsForcingName (v 0) (v 10) → IsForcingName (v 0) (v 11) →
        v 2 ∈ forcingFormula (v 0) (v 1) tailInversePairFormula
          (standardTuple ![v 4, v 5, v 6, v 7]) →
        v 2 ∈ atomicMembership (v 0) (v 1) (v 8) (v 4) →
        v 2 ∈ atomicMembership (v 0) (v 1) (v 9) (v 4) →
        v 2 ∈ tailFunctionValueForcing (v 0) (v 1) (v 6) (v 8) (v 10) →
        v 2 ∈ tailFunctionValueForcing (v 0) (v 1) (v 6) (v 9) (v 11) →
        (v 3 ∈ forcingFormula (v 0) (v 1) boundedPairMemberFormula
          (standardTuple ![v 5, v 8, v 9]) ↔
        v 3 ∈ forcingFormula (v 0) (v 1) boundedPairMemberFormula
          (standardTuple ![v 5, v 10, v 11]))) := by
  simp [tailValueOrderLawFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Matrix.empty_eq, Fin.forall_fin_succ, tail_order_forall_three_eq,
    tail_order_forall_six_eq, tail_order_forall_seven_eq]

theorem tailFunctionValueForcing_order {P R top p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (Q S f g τ σ a b : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hτ : top ∈ atomicMembership P R τ.val Q.val)
    (hσ : top ∈ atomicMembership P R σ.val Q.val)
    (ha : top ∈ tailFunctionValueForcing P R f.val τ.val a.val)
    (hb : top ∈ tailFunctionValueForcing P R f.val σ.val b.val) :
    p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, τ.val, σ.val]) ↔
      p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, a.val, b.val]) := by
  have hv : tailValueOrderLawFormula.Evalb
      ![P, R, top, p, Q.val, S.val, f.val, g.val, τ.val, σ.val, a.val, b.val] :=
    eval_of_countable_zf tailValueOrderLawFormula (by
      intro W _ _ _ _ w
      apply (eval_tailValueOrderLawFormula w).mpr
      intro hR ht hp hQ hS hf hg htau hs ha hb hi hm hn hfτ hfσ
      exact tailFunctionValueForcing_order_countable hR ht hp ⟨w 4, hQ⟩ ⟨w 5, hS⟩
        ⟨w 6, hf⟩ ⟨w 7, hg⟩ ⟨w 8, htau⟩ ⟨w 9, hs⟩ ⟨w 10, ha⟩ ⟨w 11, hb⟩ hi hm hn hfτ hfσ)
      ![P, R, top, p, Q.val, S.val, f.val, g.val, τ.val, σ.val, a.val, b.val]
  exact (eval_tailValueOrderLawFormula
    ![P, R, top, p, Q.val, S.val, f.val, g.val, τ.val, σ.val, a.val, b.val]).mp
      hv hR ht hp Q.property S.property f.property g.property τ.property σ.property a.property b.property hi hτ hσ ha hb

end ZFVP





