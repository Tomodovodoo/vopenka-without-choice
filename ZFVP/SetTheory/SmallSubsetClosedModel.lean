import ZFVP.ModelTheory.TransitiveZFCoding
import ZFVP.SetTheory.RegularSmallRank
import ZFVP.SetTheory.MeasuredWellFounded

/-! Recovering small transitive sets and function graphs from subset closure. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem small_transitive_subset_of_subset_closure {M A lam : V} [IsTransitive A]
    (hempty : (∅ : V) ∈ M)
    (hclosed : ∀ y, y ⊆ M → IsNonempty y → y ≤# lam → y ∈ M)
    (hcard : A ≤# lam) : A ⊆ M := by
  apply projectedRank_induction A id (by definability) (fun x ↦ x ∈ M) (by definability)
  intro x hx ih
  by_cases hn : IsNonempty x
  · exact hclosed x (fun y hy ↦ ih y ((inferInstance : IsTransitive A).mem_trans hy hx)
      (rank_mem hy)) hn ((cardLE_of_subset ((inferInstance : IsTransitive A).transitive x hx)).trans hcard)
  · have he : x = ∅ := by
      apply mem_ext
      intro y
      simp only [not_mem_empty, iff_false]
      exact fun hy ↦ hn ⟨y, hy⟩
    exact he ▸ hempty

theorem small_transitive_mem_of_subset_closure {M A lam : V} [IsTransitive A]
    (hempty : (∅ : V) ∈ M)
    (hclosed : ∀ y, y ⊆ M → IsNonempty y → y ≤# lam → y ∈ M)
    (hcard : A ≤# lam) : A ∈ M := by
  by_cases hn : IsNonempty A
  · exact hclosed A (small_transitive_subset_of_subset_closure hempty hclosed hcard) hn hcard
  · have he : A = ∅ := by
      apply mem_ext
      intro y
      simp only [not_mem_empty, iff_false]
      exact fun hy ↦ hn ⟨y, hy⟩
    exact he ▸ hempty

theorem function_mem_of_small_subset_closure {M A B f lam : V}
    [IsTransitive M] [Nonempty (SetDomain M)] [(SetDomain M)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hclosed : ∀ y, y ⊆ M → IsNonempty y → y ≤# lam → y ∈ M)
    (hf : f ∈ B ^ A) (hA : A ⊆ M) (hB : B ⊆ M) (hcard : A ≤# lam) : f ∈ M := by
  let := IsFunction.of_mem hf
  have hsub : f ⊆ M := by
    intro z hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    obtain ⟨hx, hy⟩ := mem_of_mem_functions hf hz
    exact (TransitiveZF.sequenceSupport M).kpair_closed x (hA x hx) y (hB y hy)
  by_cases hn : IsNonempty f
  · apply hclosed f hsub hn
    have hc := function_cardLE_domain f
    rw [domain_eq_of_mem_function hf] at hc
    exact hc.trans hcard
  · have he : f = ∅ := by
      apply mem_ext
      intro y
      simp only [not_mem_empty, iff_false]
      exact fun hy ↦ hn ⟨y, hy⟩
    rw [he]
    simpa only [TransitiveZF.empty_val M] using (∅ : SetDomain M).property

end ZFVP
