import ZFVP.ModelTheory.WoodinRecursionHistory
import ZFVP.ModelTheory.WoodinIterationDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isWoodinIterationHistory_definable : ℒₛₑₜ-relation₄[V] IsWoodinIterationHistory := by
  have h : ℒₛₑₜ-relation₄ (fun δ θ H J : V ↦ IsForcingIterationHistory θ H ∧
      (IsFunction J ∧ domain J = θ) ∧
      (∀ i ∈ θ, IsWoodinIteration δ (succ i) (H ‘ i) (J ‘ i)) ∧
      (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → J ‘ i ⊆ J ‘ j)) := by definability
  apply Language.Definable.of_iff h
  intro v
  exact ⟨fun h ↦ ⟨h.codes, ⟨h.cardinals.function, h.cardinals.domain_eq⟩, h.stage, h.increasing⟩,
    fun h ↦ ⟨h.1, ⟨h.2.1.1, h.2.1.2⟩, h.2.2.1, h.2.2.2⟩⟩

/-- Coherence of the actual recursive history follows from stage validity alone. -/
theorem woodinIterationHistory_of_stages {δ θ : V} [IsOrdinal θ]
    (hs : ∀ i ∈ θ, IsWoodinIteration δ (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i))) :
    IsWoodinIterationHistory δ θ (woodinHistoryCodes (woodinIterationHistory θ))
      (woodinHistoryCardinals (woodinIterationHistory θ)) := by
  have hall := transfinite_induction
    (fun ξ : V ↦ (∀ i ∈ ξ, IsWoodinIteration δ (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i))) →
      IsWoodinIterationHistory δ ξ (woodinHistoryCodes (woodinIterationHistory ξ))
        (woodinHistoryCardinals (woodinIterationHistory ξ))) (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal θ) hs
  intro ξ ih hξ
  apply woodinIterationHistory_of_previous hξ
  intro i hi
  let := IsOrdinal.of_mem hi
  apply ih (IsOrdinal.toOrdinal i) hi
  intro j hj
  exact hξ j (IsOrdinal.toIsTransitive.mem_trans hj hi)

theorem woodinIterationPrefix_of_stages {δ θ : V} [IsOrdinal θ]
    (hs : ∀ i ∈ θ, IsWoodinIteration δ (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i))) :
    IsWoodinIteration δ θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) :=
  (woodinIterationHistory_of_stages hs).union_iteration

end ZFVP
