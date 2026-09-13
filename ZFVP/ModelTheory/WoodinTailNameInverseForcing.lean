import ZFVP.ModelTheory.WoodinTailNameActionTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def tailInversePairForcingFormula : SetTheorySemisentence 7 :=
  f“P R Q S f g p. !(ordinaryForcingTranslation tailInversePairFormula) P R P P p
    (!assignmentPrependFormula (!(numeralFormula 3))
      (!assignmentPrependFormula (!(numeralFormula 2))
        (!assignmentPrependFormula (!(numeralFormula 1))
          (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) g) f) S) Q)”

@[irreducible] def tailValueForcingFormula : SetTheorySemisentence 6 :=
  f“P R f t n p. !tailApplicationWitnessFormula P R (!kpair.dfn f t) n p”

@[irreducible] def tailValueInverseLawFormula : SetTheorySemisentence 10 :=
  f“P R o Q S f g t a b. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingNameFormula P Q ∧ !forcingNameFormula P S ∧ !forcingNameFormula P f ∧
    !forcingNameFormula P g ∧ !forcingNameFormula P t ∧ !forcingNameFormula P a ∧
    !forcingNameFormula P b ∧ !tailInversePairForcingFormula P R Q S f g o ∧
    o ∈ !atomicMembershipFormula P R t Q ∧ !tailValueForcingFormula P R f t a o ∧
    !tailValueForcingFormula P R g a b o → o ∈ !atomicEqualityFormula P R b t”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance tailInversePairForcingFormula_defined :
    Defined (fun v : Fin 7 → V ↦ v 6 ∈ forcingFormula (v 0) (v 1) tailInversePairFormula
      (standardTuple ![v 2, v 3, v 4, v 5])) tailInversePairForcingFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [tailInversePairForcingFormula, standardTuple, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h
    exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
    exact h

instance tailValueForcingFormula_defined :
    Defined (fun v : Fin 6 → V ↦ v 5 ∈ tailFunctionValueForcing (v 0) (v 1)
      (v 2) (v 3) (v 4)) tailValueForcingFormula := by
  refine ⟨fun v ↦ ?_⟩
  have h := eval_tailApplicationWitnessFormula (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
  simpa [tailValueForcingFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb] using h

theorem tailFunctionValueForcing_inverse_countable [Countable V]
    {P R top : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S f g τ σ ν : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hτ : top ∈ atomicMembership P R τ.val Q.val)
    (hf : top ∈ tailFunctionValueForcing P R f.val τ.val σ.val)
    (hg : top ∈ tailFunctionValueForcing P R g.val σ.val ν.val) :
    top ∈ atomicEquality P R ν.val τ.val := by
  apply atomicEquality_of_all_generics hR ht ht.1 ν τ
  intro G hG htG
  let A : ForcingContext V := ⟨P, R, top, G, hR, ht, hG⟩
  have h := (Defined.eval_iff _).mp
    ((A.formula_truth tailInversePairFormula ![Q, S, f, g]).mpr ⟨top, htG, hi⟩)
  have hm : A.ofName τ ∈ A.ofName Q :=
    (forcingQuotientMk_mem_iff P R G hR hG.1 τ Q).mpr ⟨top, htG, hτ⟩
  have hfv := (A.tailFunctionValueForcing_truth f τ σ).mp ⟨top, htG, hf⟩
  have hgv := (A.tailFunctionValueForcing_truth g σ ν).mp ⟨top, htG, hg⟩
  rw [← hgv.2, ← hfv.2]
  exact h.2.2 _ hm

private theorem tail_inv_forall_two_eq {β : Type*} (a b : β) (F : β → β → Prop) :
    (∀ u v, u = a → v = b → F u v) ↔ F a b :=
  ⟨fun h ↦ h a b rfl rfl, fun h u v hu hv ↦ by subst u v; exact h⟩
private theorem tail_inv_forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩
private theorem tail_inv_forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩
private theorem tail_inv_forall_seven_eq {β : Type*} (a b c d e f g : β)
    (F : β → β → β → β → β → β → β → Prop) :
    (∀ u v w x y z t, u = a → v = b → w = c → x = d → y = e → z = f → t = g →
      F u v w x y z t) ↔ F a b c d e f g :=
  ⟨fun h ↦ h a b c d e f g rfl rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z t hu hv hw hx hy hz ht ↦ by subst u v w x y z t; exact h⟩

theorem eval_tailValueInverseLawFormula (v : Fin 10 → V) :
    tailValueInverseLawFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsForcingName (v 0) (v 3) → IsForcingName (v 0) (v 4) →
        IsForcingName (v 0) (v 5) → IsForcingName (v 0) (v 6) →
        IsForcingName (v 0) (v 7) → IsForcingName (v 0) (v 8) → IsForcingName (v 0) (v 9) →
        v 2 ∈ forcingFormula (v 0) (v 1) tailInversePairFormula
          (standardTuple ![v 3, v 4, v 5, v 6]) →
        v 2 ∈ atomicMembership (v 0) (v 1) (v 7) (v 3) →
        v 2 ∈ tailFunctionValueForcing (v 0) (v 1) (v 5) (v 7) (v 8) →
        v 2 ∈ tailFunctionValueForcing (v 0) (v 1) (v 6) (v 8) (v 9) →
        v 2 ∈ atomicEquality (v 0) (v 1) (v 9) (v 7)) := by
  simp [tailValueInverseLawFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Matrix.empty_eq, Fin.forall_fin_succ, tail_inv_forall_three_eq,
    tail_inv_forall_six_eq, tail_inv_forall_seven_eq]

theorem tailFunctionValueForcing_inverse {P R top : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S f g τ σ ν : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hτ : top ∈ atomicMembership P R τ.val Q.val)
    (hf : top ∈ tailFunctionValueForcing P R f.val τ.val σ.val)
    (hg : top ∈ tailFunctionValueForcing P R g.val σ.val ν.val) :
    top ∈ atomicEquality P R ν.val τ.val := by
  have hv : tailValueInverseLawFormula.Evalb
      ![P, R, top, Q.val, S.val, f.val, g.val, τ.val, σ.val, ν.val] :=
    eval_of_countable_zf tailValueInverseLawFormula (by
      intro W _ _ _ _ w
      apply (eval_tailValueInverseLawFormula w).mpr
      intro hR ht hQ hS hf hg htau hs hn hi hm ha hb
      exact tailFunctionValueForcing_inverse_countable hR ht ⟨w 3, hQ⟩ ⟨w 4, hS⟩
        ⟨w 5, hf⟩ ⟨w 6, hg⟩ ⟨w 7, htau⟩ ⟨w 8, hs⟩ ⟨w 9, hn⟩ hi hm ha hb)
      ![P, R, top, Q.val, S.val, f.val, g.val, τ.val, σ.val, ν.val]
  exact (eval_tailValueInverseLawFormula
    ![P, R, top, Q.val, S.val, f.val, g.val, τ.val, σ.val, ν.val]).mp
      hv hR ht Q.property S.property f.property g.property τ.property σ.property ν.property hi hτ hf hg

theorem normalizedTailFunctionValueName_inverse {P R top : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S f g τ : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hg : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![g.val]))
    (hτ : top ∈ atomicMembership P R τ.val Q.val)
    (hn : forcingLeastRankName P R top τ.val = τ.val) :
    normalizedTailFunctionValueName P R top g.val
      (normalizedTailFunctionValueName P R top f.val τ.val) = τ.val := by
  let σ : ForcingName P := ⟨normalizedTailFunctionValueName P R top f.val τ.val,
    normalizedTailFunctionValueName_isName hR ht.1⟩
  let ν : ForcingName P := ⟨normalizedTailFunctionValueName P R top g.val σ.val,
    normalizedTailFunctionValueName_isName hR ht.1⟩
  have he := tailFunctionValueForcing_inverse hR ht Q S f g τ σ ν hi hτ
    (normalizedTailFunctionValueName_forces hR ht f τ hf)
    (normalizedTailFunctionValueName_forces hR ht g σ hg)
  have h := forcingLeastRankName_congr hR ht.1 ν.property τ.property he
  rw [show forcingLeastRankName P R top ν.val = ν.val from
    normalizedTailFunctionValueName_normalized hR ht.1, hn] at h
  exact h

@[irreducible] def tailValueMemberLawFormula : SetTheorySemisentence 9 :=
  f“P R o Q S f g t a. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingNameFormula P Q ∧ !forcingNameFormula P S ∧ !forcingNameFormula P f ∧
    !forcingNameFormula P g ∧ !forcingNameFormula P t ∧ !forcingNameFormula P a ∧
    !tailInversePairForcingFormula P R Q S f g o ∧
    o ∈ !atomicMembershipFormula P R t Q ∧ !tailValueForcingFormula P R f t a o →
    o ∈ !atomicMembershipFormula P R a Q”

theorem eval_tailValueMemberLawFormula (v : Fin 9 → V) :
    tailValueMemberLawFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsForcingName (v 0) (v 3) → IsForcingName (v 0) (v 4) →
        IsForcingName (v 0) (v 5) → IsForcingName (v 0) (v 6) →
        IsForcingName (v 0) (v 7) → IsForcingName (v 0) (v 8) →
        v 2 ∈ forcingFormula (v 0) (v 1) tailInversePairFormula
          (standardTuple ![v 3, v 4, v 5, v 6]) →
        v 2 ∈ atomicMembership (v 0) (v 1) (v 7) (v 3) →
        v 2 ∈ tailFunctionValueForcing (v 0) (v 1) (v 5) (v 7) (v 8) →
        v 2 ∈ atomicMembership (v 0) (v 1) (v 8) (v 3)) := by
  simp [tailValueMemberLawFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Matrix.empty_eq, Fin.forall_fin_succ, tail_inv_forall_three_eq,
    tail_inv_forall_six_eq, tail_inv_forall_seven_eq]

theorem tailFunctionValueForcing_member_countable [Countable V]
    {P R top : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S f g τ σ : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hτ : top ∈ atomicMembership P R τ.val Q.val)
    (hf : top ∈ tailFunctionValueForcing P R f.val τ.val σ.val) :
    top ∈ atomicMembership P R σ.val Q.val := by
  apply atomicMembership_of_all_generics hR ht ht.1 σ Q
  intro G hG htG
  let A : ForcingContext V := ⟨P, R, top, G, hR, ht, hG⟩
  have h := (Defined.eval_iff _).mp
    ((A.formula_truth tailInversePairFormula ![Q, S, f, g]).mpr ⟨top, htG, hi⟩)
  have hm : A.ofName τ ∈ A.ofName Q :=
    (forcingQuotientMk_mem_iff P R G hR hG.1 τ Q).mpr ⟨top, htG, hτ⟩
  have hv := (A.tailFunctionValueForcing_truth f τ σ).mp ⟨top, htG, hf⟩
  change A.ofName σ ∈ A.ofName Q
  rw [← hv.2]
  exact function_value_mem h.1.1 hm

theorem tailFunctionValueForcing_member {P R top : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S f g τ σ : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hτ : top ∈ atomicMembership P R τ.val Q.val)
    (hf : top ∈ tailFunctionValueForcing P R f.val τ.val σ.val) :
    top ∈ atomicMembership P R σ.val Q.val := by
  have hv : tailValueMemberLawFormula.Evalb
      ![P, R, top, Q.val, S.val, f.val, g.val, τ.val, σ.val] :=
    eval_of_countable_zf tailValueMemberLawFormula (by
      intro W _ _ _ _ w
      apply (eval_tailValueMemberLawFormula w).mpr
      intro hR ht hQ hS hf hg htau hs hi hm ha
      exact tailFunctionValueForcing_member_countable hR ht ⟨w 3, hQ⟩ ⟨w 4, hS⟩
        ⟨w 5, hf⟩ ⟨w 6, hg⟩ ⟨w 7, htau⟩ ⟨w 8, hs⟩ hi hm ha)
      ![P, R, top, Q.val, S.val, f.val, g.val, τ.val, σ.val]
  exact (eval_tailValueMemberLawFormula
    ![P, R, top, Q.val, S.val, f.val, g.val, τ.val, σ.val]).mp
      hv hR ht Q.property S.property f.property g.property τ.property σ.property hi hτ hf

end ZFVP




