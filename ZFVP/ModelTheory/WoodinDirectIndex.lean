import ZFVP.ModelTheory.WoodinLimitCardinals
import ZFVP.ModelTheory.ForcingLimitCode
import ZFVP.SetTheory.DirectLimitClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.index_eq_regular_limit {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hreg : IsRegularCardinal (woodinLimitCardinal K)) : θ = woodinLimitCardinal K := by
  let := hreg.1.1
  rcases IsOrdinal.subset_iff.mp (h.index_subset_limit hlim) with he | hlt
  · exact he
  obtain ⟨β, hβ, hb⟩ := regularCardinal_maps_bounded hreg hlt
    (h.cardinals.mem_function (fun i hi ↦ h.cardinal_mem_limit hlim hi))
  obtain ⟨i, hi, hβi⟩ := h.limitCardinal_cofinal hβ
  exact False.elim (mem_asymm hβi (hb i hi))

theorem IsWoodinIteration.short_below_direct_cofinality {δ θ s K i α : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal K))
    (hi : i ∈ θ) (hα : α ∈ K ‘ i) : α ∈ internalCofinality θ := by
  have he := h.index_eq_regular_limit hlim hinac.regular
  rw [he, hinac.regular.2.2]
  exact h.cardinal_subset_limit hi _ hα

theorem IsWoodinIteration.direct_family_common_support {δ θ s K i α f : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal K))
    (hi : i ∈ θ) (hα : α ∈ K ‘ i)
    (hf : f ∈ ((forcingCodeP (forcingDirectCode θ s)) ‘ θ) ^ α) :
    ∃ k ∈ θ, ∀ j ∈ α, IsThreadSupport θ (forcingCodeE s) (f ‘ j) k := by
  simp only [forcingDirectCode, forcingThreadCode_poset] at hf
  exact forcingDirectLimit_common_support h.code.system.split
    (h.short_below_direct_cofinality hlim hinac hi hα) hf

end ZFVP
