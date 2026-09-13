import ZFVP.SetTheory.ForcingSectionMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Comparison of supported threads can be read at their common support. -/
theorem forcingSectionThread_order_iff {θ P R π E U k p q : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hp : p ∈ P ‘ k) (hq : q ∈ P ‘ k)
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hπ : ∀ i ∈ k, ∀ a ∈ P ‘ k, ∀ b ∈ P ‘ k, ⟨a, b⟩ₖ ∈ R ‘ k →
      ⟨(π ‘ ⟨i, k⟩ₖ) ‘ a, (π ‘ ⟨i, k⟩ₖ) ‘ b⟩ₖ ∈ R ‘ i)
    (hE : ∀ i ∈ θ, k ⊆ i → ∀ a ∈ P ‘ k, ∀ b ∈ P ‘ k, ⟨a, b⟩ₖ ∈ R ‘ k →
      ⟨(E ‘ ⟨k, i⟩ₖ) ‘ a, (E ‘ ⟨k, i⟩ₖ) ‘ b⟩ₖ ∈ R ‘ i) :
    ⟨forcingSectionThread θ π E k p, forcingSectionThread θ π E k q⟩ₖ ∈
      forcingThreadOrder θ R (forcingDirectLimit θ P π E U) ↔ ⟨p, q⟩ₖ ∈ R ‘ k := by
  constructor
  · intro hpq
    have hc := ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hpq).2.2 k hk
    simpa only [forcingSectionThread_value hk, forcingSectionValue_self h hk hp,
      forcingSectionValue_self h hk hq] using hc
  · intro hpq
    have hc := forcingThreadSection_monotone h hk hU hp hq hpq hπ hE
    simpa only [forcingThreadSection_value hp, forcingThreadSection_value hq] using hc

/-- Different-stage representatives are compared after inclusion in any common later stage. -/
theorem forcingSectionThread_order_iff_common_stage {θ P R π E U i j k p q : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hi : i ∈ θ) (hj : j ∈ θ) (hk : k ∈ θ)
    (hik : i ⊆ k) (hjk : j ⊆ k) (hp : p ∈ P ‘ i) (hq : q ∈ P ‘ j)
    (hU : ∀ l ∈ θ, P ‘ l ⊆ U)
    (hπ : ∀ l ∈ k, ∀ a ∈ P ‘ k, ∀ b ∈ P ‘ k, ⟨a, b⟩ₖ ∈ R ‘ k →
      ⟨(π ‘ ⟨l, k⟩ₖ) ‘ a, (π ‘ ⟨l, k⟩ₖ) ‘ b⟩ₖ ∈ R ‘ l)
    (hE : ∀ l ∈ θ, k ⊆ l → ∀ a ∈ P ‘ k, ∀ b ∈ P ‘ k, ⟨a, b⟩ₖ ∈ R ‘ k →
      ⟨(E ‘ ⟨k, l⟩ₖ) ‘ a, (E ‘ ⟨k, l⟩ₖ) ‘ b⟩ₖ ∈ R ‘ l) :
    ⟨forcingSectionThread θ π E i p, forcingSectionThread θ π E j q⟩ₖ ∈
      forcingThreadOrder θ R (forcingDirectLimit θ P π E U) ↔
      ⟨(E ‘ ⟨i, k⟩ₖ) ‘ p, (E ‘ ⟨j, k⟩ₖ) ‘ q⟩ₖ ∈ R ‘ k := by
  rw [← forcingSectionThread_comp h hi hk hik hp hU,
    ← forcingSectionThread_comp h hj hk hjk hq hU]
  exact forcingSectionThread_order_iff h hk (h.secMaps i hi k hk hik p hp)
    (h.secMaps j hj k hk hjk q hq) hU hπ hE

end ZFVP
