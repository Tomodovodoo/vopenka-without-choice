import ZFVP.SetTheory.StarDependentChoiceFailure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedFunctionClosedFormula : SetTheorySemisentence 3 :=
  “H D B. ∀ f ∈ H, !boundedFunctionFormula f D B → f ∈ B”

theorem boundedFunctionClosedFormula_bounded : IsBoundedSetFormula boundedFunctionClosedFormula :=
  .all (.bvar 0) (.or (boundedFunctionFormula_bounded.subst _).neg (.rel _ _))

def boundedStarDCFormula : SetTheorySemisentence 3 :=
  “κ D H. ∀ B ∈ H,
    (!boundedFunctionClosedFormula H D B ∧ κ ∈ B ∧ D ∈ B ∧
      !IsTransitive.dfn B ∧ !functionRestrictionClosedFormula B) →
      ¬!boundedDependentChoiceFailureFormula κ B”

theorem boundedStarDCFormula_bounded : IsBoundedSetFormula boundedStarDCFormula :=
  .all (.bvar 2) (.or
    (IsBoundedSetFormula.and (boundedFunctionClosedFormula_bounded.subst _) (.and (.rel _ _) (.and (.rel _ _)
      (.and (isTransitiveFormula_bounded.subst _) (functionRestrictionClosedFormula_bounded.subst _))))).neg
    (boundedDependentChoiceFailureFormula_bounded.subst _).neg)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsBoundedFunctionClosed (H D B : V) : Prop := ∀ f ∈ H, f ∈ B ^ D → f ∈ B

instance boundedFunctionClosedFormula_defined :
    ℒₛₑₜ-relation₃[V] IsBoundedFunctionClosed via boundedFunctionClosedFormula :=
  ⟨fun v ↦ by simp [boundedFunctionClosedFormula, IsBoundedFunctionClosed]⟩

theorem boundedFunctionClosed_rank_iff {γ D B : V} (hγ : Cn 1 γ)
    (hD : D ∈ hierarchy γ) (hB : B ∈ hierarchy γ) :
    IsBoundedFunctionClosed (hierarchy γ) D B ↔ B ^ D ⊆ B := by
  constructor
  · intro h f hf
    let := hγ.ordinal
    exact h f (subset_mem_hierarchy_limit hγ.successor_closed
      (prod_mem_hierarchy_limit hγ.successor_closed hD hB) (subset_prod_of_mem_function hf)) hf
  · intro h f _hf hfD
    exact h f hfD

theorem eval_boundedStarDCFormula (κ D H : V) :
    boundedStarDCFormula.Evalb ![κ, D, H] ↔
      ∀ B ∈ H, IsBoundedFunctionClosed H D B → κ ∈ B → D ∈ B →
        IsTransitive B → IsFunctionRestrictionClosed B → ¬IsBoundedDependentChoiceFailure κ B := by
  simp [boundedStarDCFormula]

/-- Star reflection turns failure of DC into a bounded certificate below
the correct rank. Function closure prevents a false certificate caused by
omitting branch functions. -/
theorem boundedStarDC_iff_at {δ γ κ α : V} (hδ : IsWoodinSupercompact δ)
    (hγ : IsSigmaOneStarCorrect γ) (hα : α ∈ γ) (hκ : κ ∈ α) :
    boundedStarDCFormula.Evalb ![κ, hierarchy α, hierarchy γ] ↔ InternalDependentChoiceAt κ := by
  let := hγ.1.ordinal
  let := IsOrdinal.of_mem hα
  let := IsOrdinal.of_mem hκ
  have hD : hierarchy α ∈ hierarchy γ := hγ.1.hierarchy_closed inferInstance
    (ordinal_mem_hierarchy_iff.mpr hα)
  rw [eval_boundedStarDCFormula]
  constructor
  · intro h
    by_contra hn
    obtain ⟨B, hB, hc, hDB, hκB, ht, hr, hf⟩ := hγ.dependentChoice_failure_witness_at hδ hα hκ hn
    exact h B hB ((boundedFunctionClosed_rank_iff hγ.1 hD hB).mpr hc) hκB hDB ht hr hf
  · intro hDC B hB hc hκB hDB ht hr hf
    have hcD := (boundedFunctionClosed_rank_iff hγ.1 hD hB).mp hc
    have hκD : κ ⊆ hierarchy α := (hierarchy_transitive α).transitive κ
      (ordinal_mem_hierarchy_iff.mpr hκ)
    have hcκ : B ^ κ ⊆ B := fun f hff ↦ hr.function_mem hcD hDB hκB hκD ⟨κ, hκB⟩ hff
    exact hf.not_dependentChoice (closedContainer_shortFunctions ht hr hκB hcκ) hDC

theorem boundedStarDC_iff {δ γ κ : V} (hδ : IsWoodinSupercompact δ)
    (hγ : IsSigmaOneStarCorrect γ) (hκ : κ ∈ γ) :
    boundedStarDCFormula.Evalb ![κ, hierarchy (succ κ), hierarchy γ] ↔ InternalDependentChoiceAt κ :=
  boundedStarDC_iff_at hδ hγ (hγ.1.successor_closed κ hκ) (mem_succ_self κ)

end ZFVP
