import ZFVP.SetTheory.ForcingRegular

/-! The regular-open implication has the usual forcing condition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingImplication_iff {P R A B p : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) (hB : IsForcingRegular P R B) :
    p ∈ forcingClosure P R (forcingNegation P R A ∪ B) ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → q ∈ A → q ∈ B := by
  rw [mem_forcingClosure_iff]
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨hp, ?_⟩
    intro q hq hqp hqA
    apply hB.2.2 q hq
    intro r hr hrq
    obtain ⟨s, hs, hsr⟩ := hd r hr (hR.2.2 r hr q hq p hp hrq hqp)
    rcases mem_union_iff.mp hs with hs | hs
    · have hsP := forcingNegation_subset P R A s hs
      have hsA := hA.2.1 q hqA s hsP (hR.2.2 s hsP r hr q hq hsr hrq)
      exact False.elim (forcingNegation_disjoint hR hs hsA)
    · exact ⟨s, hs, hsr⟩
  · rintro ⟨hp, hi⟩
    refine ⟨hp, ?_⟩
    intro q hq hqp
    by_cases hqA : q ∈ A
    · exact ⟨q, mem_union_iff.mpr (Or.inr (hi q hq hqp hqA)), hR.2.1 q hq⟩
    · obtain ⟨r, hr, hrq⟩ := exists_forcingNegation_of_not_mem hq hqA hA.2.2
      exact ⟨r, mem_union_iff.mpr (Or.inl hr), hrq⟩

end ZFVP
