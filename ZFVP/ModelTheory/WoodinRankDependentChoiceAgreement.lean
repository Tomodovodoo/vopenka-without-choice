import ZFVP.SetTheory.WoodinBoundedDCFailures
import ZFVP.ModelTheory.TransitiveZFDependentChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessInaccessible.eventually_rank_dependentChoice_iff {δ γ : V}
    (hδ : IsChoicelessInaccessible δ) (hγ : γ ∈ δ)
    (hsmall : ∀ κ ∈ γ, ¬InternalDependentChoiceAt κ →
      ∃ B ∈ hierarchy δ, IsRankFunctionClosed (succ κ) B ∧ hierarchy (succ κ) ∈ B ∧
        κ ∈ B ∧ IsTransitive B ∧ IsFunctionRestrictionClosed B ∧
        IsBoundedDependentChoiceFailure κ B) :
    ∃ η ∈ δ, γ ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ κ : SetDomain (hierarchy ξ), κ.val ∈ γ →
        (InternalDependentChoiceAt κ ↔ InternalDependentChoiceAt κ.val) := by
  let := hδ.1
  let := IsOrdinal.of_mem hγ
  obtain ⟨η, hηδ, hcert⟩ := hδ.bounded_dependentChoice_failure_certificates hγ hsmall
  let := IsOrdinal.of_mem hηδ
  let := ordinal_union_ordinal η γ
  let b := succ (η ∪ γ)
  have hbδ : b ∈ δ := regularCardinal_succ_closed hδ.regular (ordinal_union_mem hηδ hγ)
  have hγb : γ ∈ b := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_union_right η γ))
  refine ⟨b, hbδ, hγb, ?_⟩
  intro ξ hbξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  have hηξ : η ∈ ξ := ordinal_mem_of_subset_mem
    (subset_trans (subset_union_left η γ) (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz))) hbξ
  intro κ hκγ
  let := IsOrdinal.of_mem hκγ
  constructor
  · intro hDC
    by_contra hf
    obtain ⟨B, hBη, hc, hD, hκB, ht, hr, hBfail⟩ := hcert κ.val hκγ hf
    have hBξ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hηξ) _ hBη
    have hcκ : B ^ κ.val ⊆ B := fun f hff ↦ hr.function_mem hc hD hκB
      ((hierarchy_transitive (succ κ.val)).transitive κ.val
        (ordinal_mem_hierarchy_iff.mpr (mem_succ_self κ.val))) ⟨κ.val, hκB⟩ hff
    exact TransitiveZF.not_dependentChoice_of_bounded_failure (hierarchy ξ) κ ⟨B, hBξ⟩
      inferInstance hBfail (closedContainer_shortFunctions ht hr hκB hcκ) hDC
  · exact rank_dependentChoice_of_ambient hξ.rankCriterion.2.2.1 κ inferInstance

theorem IsWoodinSupercompact.eventually_rank_dependentChoice_iff {δ γ : V}
    (hδ : IsWoodinSupercompact δ) (hγ : γ ∈ δ) :
    ∃ η ∈ δ, γ ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ κ : SetDomain (hierarchy ξ), κ.val ∈ γ →
        (InternalDependentChoiceAt κ ↔ InternalDependentChoiceAt κ.val) := by
  let := hδ.1.1
  exact hδ.inaccessible.eventually_rank_dependentChoice_iff hγ
    (fun _ hκ hf ↦ hδ.small_dependentChoice_failure_certificate
      (IsOrdinal.toIsTransitive.mem_trans hκ hγ) hf)

end ZFVP
