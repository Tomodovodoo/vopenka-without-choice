import ZFVP.ModelTheory.ForcingNameNormalization
import ZFVP.ModelTheory.SaturatedTwoStepTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def nameInHierarchyFormula : SetTheorySemisentence 2 :=
  f“x d. x ∈ !hierarchyFormula d”

def forcingNameNormalizationFormula : SetTheorySemisentence 6 :=
  f“P R o d t p. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !choicelessInaccessibleFormula d ∧ P ∈ !hierarchyFormula d ∧
    !forcingNameFormula P t ∧ p ∈ P ∧
    !(binaryForcingTruthFormula nameInHierarchyFormula) p P R t (!checkNameFormula o d) →
      ∃ n ∈ !(parameterRecursionFormula forcingNameHierarchyStepFormula) P d,
        p ∈ !atomicEqualityFormula P R n t”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance nameInHierarchyFormula_defined :
    ℒₛₑₜ-relation[V] (fun x d ↦ x ∈ hierarchy d) via nameInHierarchyFormula :=
  ⟨fun v ↦ by simp [nameInHierarchyFormula]⟩

theorem atomicEquality_of_all_generics [Countable V] {P R one p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (σ τ : ForcingName P)
    (he : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), p ∈ G →
      (ForcingContext.mk P R one G hR ht hG).ofName σ =
        (ForcingContext.mk P R one G hR ht hG).ofName τ) :
    p ∈ atomicEquality P R σ.val τ.val := by
  apply (atomicEquality_regular hR σ.val τ.val).2.2 p hp
  intro q hq hqp
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  have hpG := hG.1.2.2.1 q hqG p hp hqp
  obtain ⟨r, hrG, hr⟩ := (forcingQuotientMk_eq_iff P R G hR hG.1 σ τ).mp (he G hG hpG)
  obtain ⟨s, hsG, hsr, hsq⟩ := hG.1.2.2.2 r hrG q hqG
  exact ⟨s, atomicEquality_mono hR hr (hG.1.1 s hsG) hsr, hsq⟩

theorem forcingName_normalization_countable [Countable V] {P R one δ p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P)
    (τ : ForcingName P)
    (hτ : p ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName one δ])) :
    ∃ ν ∈ forcingNameHierarchy P δ, p ∈ atomicEquality P R ν τ.val := by
  obtain ⟨ν, hνδ, hν, hv⟩ := small_forcing_name_normalization hR ht hδ hP τ
  refine ⟨ν, hνδ, atomicEquality_of_all_generics hR ht hp ⟨ν, hν⟩ τ ?_⟩
  intro G hG hpG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  apply hv G hG
  exact (Defined.eval_iff _).mp ((A.formula_truth nameInHierarchyFormula
    ![τ, ⟨checkName one δ, checkName_isName ht.1 δ⟩]).mpr ⟨p, hpG, hτ⟩)

theorem eval_forcingNameNormalizationFormula (v : Fin 6 → V) :
    forcingNameNormalizationFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsChoicelessInaccessible (v 3) → v 0 ∈ hierarchy (v 3) → IsForcingName (v 0) (v 4) →
        v 5 ∈ v 0 → v 5 ∈ forcingFormula (v 0) (v 1) nameInHierarchyFormula
          (standardTuple ![v 4, checkName (v 2) (v 3)]) →
        ∃ ν ∈ forcingNameHierarchy (v 0) (v 3), v 5 ∈ atomicEquality (v 0) (v 1) ν (v 4)) := by
  simp [forcingNameNormalizationFormula]

private theorem forcingNameNormalization_valid (v : Fin 6 → V) :
    forcingNameNormalizationFormula.Evalb v := by
  apply eval_of_countable_zf forcingNameNormalizationFormula
  intro W _ _ _ _ w
  apply (eval_forcingNameNormalizationFormula w).mpr
  intro hR ht hδ hP hτ hp hf
  exact forcingName_normalization_countable hR ht hδ hP hp ⟨w 4, hτ⟩ hf

/-- Normalization inside the forcing relation, over arbitrary ZF models. -/
theorem forcingName_normalization {P R one δ p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P)
    (τ : ForcingName P)
    (hτ : p ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName one δ])) :
    ∃ ν ∈ forcingNameHierarchy P δ, p ∈ atomicEquality P R ν τ.val :=
  (eval_forcingNameNormalizationFormula ![P, R, one, δ, τ.val, p]).mp
    (forcingNameNormalization_valid _) hR ht hδ hP τ.property hp hτ

/-- Saturation admits the normalized representative as an actual two-step
condition while keeping the prescribed first coordinate. -/
theorem saturated_twoStep_name_representative {P R one δ p Q t : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P)
    (τ : ForcingName P)
    (hτ : p ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName one δ]))
    (hm : p ∈ atomicMembership P R τ.val Q) :
    ∃ ν ∈ forcingNameHierarchy P δ,
      ⟨p, ν⟩ₖ ∈ twoStepConditions P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q) t ∧
        p ∈ atomicEquality P R ν τ.val := by
  let := hδ.1
  obtain ⟨ν, hνδ, he⟩ := forcingName_normalization hR ht hδ hP hp τ hτ
  have hν := forcingNameHierarchy_names P δ ν hνδ
  have hνQ : p ∈ atomicMembership P R ν Q :=
    ((atomicEquality_membership_iff hR he Q).1).mpr hm
  refine ⟨ν, hνδ, (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hp, ?_, ?_⟩, he⟩
  · exact mem_union_iff.mpr (Or.inl (forcingSaturatedName_mem_domain hνδ hp hν hνQ))
  · exact forcingSaturatedName_forces_member hR hνδ hp hν hνQ

end ZFVP
