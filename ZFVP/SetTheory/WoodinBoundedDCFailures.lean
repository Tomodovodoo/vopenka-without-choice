import ZFVP.SetTheory.WoodinSmallDCFailure
import ZFVP.SetTheory.ChoicelessInaccessibleRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessInaccessible.bounded_dependentChoice_failure_certificates {δ γ : V}
    (hδ : IsChoicelessInaccessible δ) (hγ : γ ∈ δ)
    (hsmall : ∀ κ ∈ γ, ¬InternalDependentChoiceAt κ →
      ∃ B ∈ hierarchy δ, IsRankFunctionClosed (succ κ) B ∧ hierarchy (succ κ) ∈ B ∧
        κ ∈ B ∧ IsTransitive B ∧ IsFunctionRestrictionClosed B ∧
        IsBoundedDependentChoiceFailure κ B) :
    ∃ η ∈ δ, ∀ κ ∈ γ, ¬InternalDependentChoiceAt κ →
      ∃ B ∈ hierarchy η, IsRankFunctionClosed (succ κ) B ∧ hierarchy (succ κ) ∈ B ∧
        κ ∈ B ∧ IsTransitive B ∧ IsFunctionRestrictionClosed B ∧
        IsBoundedDependentChoiceFailure κ B := by
  let := hδ.1
  let := IsOrdinal.of_mem hγ
  let D : V := {κ ∈ γ ; ¬InternalDependentChoiceAt κ}
  have hD : D ∈ hierarchy δ := subset_mem_hierarchy_limit
    (fun _ hx ↦ regularCardinal_succ_closed hδ.regular hx)
    (ordinal_mem_hierarchy_iff.mpr hγ) (fun _ hx ↦ (mem_sep_iff.mp hx).1)
  let R : V → V → Prop := fun κ B ↦ IsRankFunctionClosed (succ κ) B ∧ hierarchy (succ κ) ∈ B ∧
    κ ∈ B ∧ IsTransitive B ∧ IsFunctionRestrictionClosed B ∧ IsBoundedDependentChoiceFailure κ B
  have hR : ℒₛₑₜ-relation R := by unfold R; definability
  have hex : ∀ κ ∈ D, ∃ B ∈ hierarchy δ, R κ B := by
    intro κ hκ
    obtain ⟨hκγ, hf⟩ := mem_sep_iff.mp hκ
    exact hsmall κ hκγ hf
  obtain ⟨b, hb, hcollect⟩ := hδ.rankCriterion.2.2.2.collection
    (fun _ hx ↦ regularCardinal_succ_closed hδ.regular hx) hD R hR hex
  refine ⟨rank b, (mem_hierarchy_iff_rank_mem _ _).mp hb, ?_⟩
  intro κ hκ hf
  obtain ⟨B, hB, hRB⟩ := hcollect κ (mem_sep_iff.mpr ⟨hκ, hf⟩)
  exact ⟨B, (mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem hB), hRB⟩

theorem IsWoodinSupercompact.bounded_dependentChoice_failure_certificates {δ γ : V}
    (hδ : IsWoodinSupercompact δ) (hγ : γ ∈ δ) :
    ∃ η ∈ δ, ∀ κ ∈ γ, ¬InternalDependentChoiceAt κ →
      ∃ B ∈ hierarchy η, IsRankFunctionClosed (succ κ) B ∧ hierarchy (succ κ) ∈ B ∧
        κ ∈ B ∧ IsTransitive B ∧ IsFunctionRestrictionClosed B ∧
        IsBoundedDependentChoiceFailure κ B := by
  let := hδ.1.1
  exact hδ.inaccessible.bounded_dependentChoice_failure_certificates hγ
    (fun _ hκ hf ↦ hδ.small_dependentChoice_failure_certificate
      (IsOrdinal.toIsTransitive.mem_trans hκ hγ) hf)

end ZFVP
