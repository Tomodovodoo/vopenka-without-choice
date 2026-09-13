import ZFVP.SetTheory.ForcingBoundSectionCompatibility
import ZFVP.SetTheory.IterationTableUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem coherentForcingBound_of_prefixes {θ P R π B i I : V} [IsOrdinal θ]
    (h : ∀ k ∈ θ, ∃ C, IsCoherentForcingBound (succ k) P R π C i I ∧
      ∀ j ∈ succ k, B ‘ j = C ‘ j) : IsCoherentForcingBound θ P R π B i I := by
  constructor
  · intro j hj hij f hf p hp hb
    obtain ⟨C, hc, he⟩ := h j hj
    rw [he j (mem_succ_self j)]
    exact hc.bound j (mem_succ_self j) hij f hf p hp hb
  · intro j hj k hk hij hjk f hf p hp hb
    obtain ⟨C, hc, he⟩ := h k hk
    have hj' : j ∈ succ k := by
      let := IsOrdinal.of_mem hj
      let := IsOrdinal.of_mem hk
      rcases IsOrdinal.subset_iff.mp hjk with rfl | hjk
      · exact mem_succ_self j
      · exact mem_succ_iff.mpr (Or.inr hjk)
    rw [he k (mem_succ_self k), he j hj']
    exact hc.commute j hj' k (mem_succ_self k) hij hjk f hf p hp hb

theorem sectionCompatibleForcingBound_of_prefixes {θ P R π E B i I : V} [IsOrdinal θ]
    (h : ∀ k ∈ θ, ∃ C, IsSectionCompatibleForcingBound (succ k) P R π E C i I ∧
      ∀ j ∈ succ k, B ‘ j = C ‘ j) : IsSectionCompatibleForcingBound θ P R π E B i I := by
  constructor
  intro j hj k hk hij hjk f hf p hp hb
  obtain ⟨C, hc, he⟩ := h k hk
  have hj' : j ∈ succ k := by
    let := IsOrdinal.of_mem hj
    let := IsOrdinal.of_mem hk
    rcases IsOrdinal.subset_iff.mp hjk with rfl | hjk
    · exact mem_succ_self j
    · exact mem_succ_iff.mpr (Or.inr hjk)
  rw [he k (mem_succ_self k), he j hj']
  exact hc.compatible j hj' k (mem_succ_self k) hij hjk f hf p hp hb

theorem forcingBound_tableUnion {θ P R π E i I : V} [IsOrdinal θ] {F : V → V}
    (hF : ℒₛₑₜ-function₁ F) (ht : ∀ k ∈ θ, IsIterationTable (succ k) (F k))
    (hd : ∀ j ∈ θ, ∀ k ∈ θ, ∃ l ∈ θ, F j ⊆ F l ∧ F k ⊆ F l)
    (hb : ∀ k ∈ θ, IsCoherentForcingBound (succ k) P R π (F k) i I)
    (hc : ∀ k ∈ θ, IsSectionCompatibleForcingBound (succ k) P R π E (F k) i I) :
    IsIterationTable θ (iterationTableUnion θ F hF) ∧
    IsCoherentForcingBound θ P R π (iterationTableUnion θ F hF) i I ∧
    IsSectionCompatibleForcingBound θ P R π E (iterationTableUnion θ F hF) i I := by
  have he (k : V) (hk : k ∈ θ) (j : V) (hj : j ∈ succ k) :
      (iterationTableUnion θ F hF) ‘ j = (F k) ‘ j := by
    apply iterationTableUnion_value hF (fun a ha ↦ (ht a ha).function) hd hk
    rwa [(ht k hk).domain_eq]
  refine ⟨iterationTableUnion_family hF ht hd, ?_, ?_⟩
  · exact coherentForcingBound_of_prefixes (fun k hk ↦ ⟨F k, hb k hk, he k hk⟩)
  · exact sectionCompatibleForcingBound_of_prefixes (fun k hk ↦ ⟨F k, hc k hk, he k hk⟩)

end ZFVP
