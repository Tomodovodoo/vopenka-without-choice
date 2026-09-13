import ZFVP.SetTheory.WoodinSupercompactFunctionClosure
import ZFVP.SetTheory.FunctionRestrictionClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def restrictionContainerFormula : SetTheorySemisentence 2 :=
  “a b. a ∈ b ∧ !IsTransitive.dfn b ∧ !functionRestrictionClosedFormula b”

theorem restrictionContainerFormula_bounded : IsBoundedSetFormula restrictionContainerFormula :=
  .and (.rel _ _) (.and (isTransitiveFormula_bounded.subst _)
    (functionRestrictionClosedFormula_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.exists_rankClosed_restrictionContainer {δ : V}
    (hδ : IsWoodinSupercompact δ) (α a : V) [IsOrdinal α] :
    ∃ b : V, IsRankFunctionClosed α b ∧ a ∈ b ∧ IsTransitive b ∧ IsFunctionRestrictionClosed b := by
  let := hδ.1.1
  obtain ⟨b, hc, hb⟩ := hδ.exists_functionClosed_spec restrictionContainerFormula_bounded
    (fun u hu ↦ by simpa [restrictionContainerFormula] using
      (show u ∈ hierarchy δ ∧ IsTransitive (hierarchy δ) ∧ IsFunctionRestrictionClosed (hierarchy δ)
        from ⟨hu, hierarchy_transitive δ, hδ.inaccessible.functionRestrictionClosed⟩)) α a
  exact ⟨b, hc, by simpa [restrictionContainerFormula] using hb⟩

/-- Arbitrary domain closure follows by extending functions to a rank and
then using the bounded restriction closure of the containing set. -/
theorem IsWoodinSupercompact.exists_functionClosed_on {δ : V}
    (hδ : IsWoodinSupercompact δ) (X a : V) :
    ∃ b : V, b ^ X ⊆ b ∧ a ∈ b ∧ X ∈ b ∧ IsTransitive b ∧ IsFunctionRestrictionClosed b := by
  let α := succ (rank X)
  let D := hierarchy α
  obtain ⟨b, hc, hp, ht, hr⟩ := hδ.exists_rankClosed_restrictionContainer α ⟨a, D⟩ₖ
  let := ht
  obtain ⟨ha, hD⟩ := kpair_components_mem_transitive hp
  have hXD : X ∈ D := (mem_hierarchy_iff_rank_mem _ _).mpr (by simp [α])
  have hX : X ∈ b := ht.mem_trans hXD hD
  have hsub : X ⊆ D := (hierarchy_transitive α).transitive X hXD
  have hne : IsNonempty b := ⟨a, ha⟩
  refine ⟨b, ?_, ha, hX, ht, hr⟩
  intro f hf
  exact hr.function_mem hc hD hX hsub hne hf

end ZFVP
