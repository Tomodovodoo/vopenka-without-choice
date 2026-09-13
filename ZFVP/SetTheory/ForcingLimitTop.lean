import ZFVP.SetTheory.ForcingTopExtension
import ZFVP.SetTheory.ForcingLimitColumns

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingSectionThread_top_value {θ P R π E t k i : V} [IsOrdinal θ]
    (h : IsToppedSplitForcingSystem θ P R π E t) (hk : k ∈ θ) (hi : i ∈ θ) :
    (forcingSectionThread θ π E k (t ‘ k)) ‘ i = t ‘ i := by
  classical
  rw [forcingSectionThread_value hi]
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem hi
  by_cases hik : i ∈ k
  · simp only [forcingSectionValue, ite_eq_left hik]
    exact h.projTop i hi k hk (IsOrdinal.toIsTransitive.transitive _ hik)
  · simp only [forcingSectionValue, ite_eq_right hik]
    apply h.secTop k hk i hi
    rcases IsOrdinal.mem_trichotomy i k with hik' | rfl | hki
    · exact (hik hik').elim
    · exact fun x hx ↦ hx
    · exact IsOrdinal.toIsTransitive.transitive _ hki

theorem forcingLimit_toppedColumn {θ P R π E t U C k : V} [IsOrdinal θ]
    (s : IsSplitForcingSystem θ P π E) (h : IsToppedSplitForcingSystem θ P R π E t)
    (hk : k ∈ θ) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hD : forcingDirectLimit θ P π E U ⊆ C) (hI : C ⊆ forcingInverseLimit θ P π U) :
    IsToppedSplitForcingColumn θ t C (forcingThreadOrder θ R C)
      (forcingLimitProjectionColumn θ C) (forcingLimitSectionColumn θ P π E)
      (forcingSectionThread θ π E k (t ‘ k)) := by
  have hu := hD _ (forcingSectionThread_mem s hk (h.top k hk).1 hU)
  refine ⟨⟨hu, ?_⟩, ?_, ?_⟩
  · intro f hf
    apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
    refine ⟨hf, hu, ?_⟩
    intro i hi
    rw [forcingSectionThread_top_value h hk hi]
    exact (h.top i hi).2 _ (((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hI f hf)).2.1 i hi)
  · intro i hi
    rw [forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value hu]
    exact forcingSectionThread_top_value h hk hi
  · intro i hi
    rw [forcingLimitSectionColumn_value hi, forcingThreadSection_value (h.top i hi).1]
    let := IsOrdinal.of_mem hk
    let := IsOrdinal.of_mem hi
    rcases IsOrdinal.mem_trichotomy i k with hik | rfl | hki
    · have hik' : i ⊆ k := IsOrdinal.toIsTransitive.transitive _ hik
      have hc := forcingSectionThread_comp s hi hk hik' (h.top i hi).1 hU
      rw [h.secTop i hi k hk hik'] at hc
      exact hc.symm
    · rfl
    · have hki' : k ⊆ i := IsOrdinal.toIsTransitive.transitive _ hki
      have hc := forcingSectionThread_comp s hk hi hki' (h.top k hk).1 hU
      rwa [h.secTop k hk i hi hki'] at hc

end ZFVP
