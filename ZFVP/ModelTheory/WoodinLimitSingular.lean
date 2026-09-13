import ZFVP.ModelTheory.WoodinLimitCardinals
import ZFVP.SetTheory.RegularLimitInaccessible

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.limitCardinal_omega_mem {δ θ s K : V}
    (h : IsWoodinIteration δ θ s K) (h0 : ∅ ∈ θ) : (ω : V) ∈ woodinLimitCardinal K :=
  h.cardinal_subset_limit h0 _ (h.inaccessible ∅ h0).2.1

theorem IsWoodinIteration.limitCardinal_succ_closed {δ θ s K : V}
    (h : IsWoodinIteration δ θ s K) :
    ∀ α ∈ woodinLimitCardinal K, succ α ∈ woodinLimitCardinal K := by
  intro α hα
  obtain ⟨i, hi, hαi⟩ := h.limitCardinal_cofinal hα
  exact h.cardinal_subset_limit hi _ (regularCardinal_succ_closed (h.inaccessible i hi).regular hαi)

theorem IsWoodinIteration.limitCardinal_inaccessibles_cofinal {δ θ s K : V}
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ i ∈ θ, succ i ∈ θ) :
    ∀ α ∈ woodinLimitCardinal K, ∃ κ ∈ woodinLimitCardinal K, IsChoicelessInaccessible κ ∧ α ∈ κ := by
  intro α hα
  obtain ⟨i, hi, hαi⟩ := h.limitCardinal_cofinal hα
  exact ⟨K ‘ i, h.cardinal_mem_limit hlim hi, h.inaccessible i hi, hαi⟩

theorem IsWoodinIteration.limitCardinal_singular {δ θ s K : V}
    (h : IsWoodinIteration δ θ s K) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal K)) :
    internalCofinality (woodinLimitCardinal K) ∈ woodinLimitCardinal K := by
  let := h.limitCardinal_ordinal
  exact cofinality_mem_of_noninaccessible_limit
    (IsOrdinal.toIsTransitive.transitive _ (h.limitCardinal_omega_mem h0))
    (h.limitCardinal_inaccessibles_cofinal hlim) hn

end ZFVP
