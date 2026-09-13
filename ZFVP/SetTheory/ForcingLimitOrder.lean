import ZFVP.SetTheory.ForcingOrderExtension
import ZFVP.SetTheory.ForcingLimitColumns

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingLimit_below_section {θ P R π E U C k f p : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (o : IsOrderedSplitForcingSystem θ P R π E)
    (hk : k ∈ θ) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hD : forcingDirectLimit θ P π E U ⊆ C) (hI : C ⊆ forcingInverseLimit θ P π U)
    (hf : f ∈ C) (hp : p ∈ P ‘ k) :
    ⟨f, (forcingThreadSection θ P π E k) ‘ p⟩ₖ ∈ forcingThreadOrder θ R C ↔
      ⟨f ‘ k, p⟩ₖ ∈ R ‘ k := by
  rw [forcingThreadSection_value hp]
  constructor
  · intro hle
    have hkval := ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hle).2.2 k hk
    rwa [forcingSectionThread_value hk, forcingSectionValue_self h hk hp] at hkval
  · intro hle
    have hf' := (mem_forcingInverseLimit_iff _ _ _ _ _).mp (hI f hf)
    let := IsOrdinal.of_mem hk
    apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
    refine ⟨hf, hD _ (forcingSectionThread_mem h hk hp hU), ?_⟩
    intro i hi
    let := IsOrdinal.of_mem hi
    rw [forcingSectionThread_value hi]
    rcases IsOrdinal.mem_trichotomy i k with hik | rfl | hki
    · have hik' : i ⊆ k := IsOrdinal.toIsTransitive.transitive _ hik
      rw [← hf'.2.2 k hk i hik hi]
      simpa only [forcingSectionValue, ite_eq_left hik] using
        o.projMono i hi k hk hik' _ (hf'.2.1 k hk) p hp hle
    · rwa [forcingSectionValue_self h hk hp]
    · have hki' : k ⊆ i := IsOrdinal.toIsTransitive.transitive _ hki
      have hik : i ∉ k := fun hik ↦ mem_irrefl i (hki' i hik)
      simp only [forcingSectionValue, ite_eq_right hik]
      apply (o.below k hk i hi hki' _ (hf'.2.1 i hi) p hp).mpr
      rwa [hf'.2.2 i hi k hki hk]

/-- Every intermediate limit carrier inherits the coordinate order laws. -/
theorem forcingLimit_orderedColumn {θ P R π E U C : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (o : IsOrderedSplitForcingSystem θ P R π E)
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hD : forcingDirectLimit θ P π E U ⊆ C) (hI : C ⊆ forcingInverseLimit θ P π U) :
    IsOrderedSplitForcingColumn θ P R C (forcingThreadOrder θ R C)
      (forcingLimitProjectionColumn θ C) (forcingLimitSectionColumn θ P π E) := by
  refine ⟨forcingThreadOrder_preorder o.preorder ?_, ?_, ?_⟩
  · intro f hf i hi
    exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hI f hf)).2.1 i hi
  · intro i hi f hf g hg hfg
    rw [forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value hf,
      forcingThreadCoordinate_value hg]
    exact ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hfg).2.2 i hi
  · intro i hi f hf p hp
    rw [forcingLimitProjectionColumn_value hi, forcingLimitSectionColumn_value hi,
      forcingThreadCoordinate_value hf]
    exact forcingLimit_below_section h o hi hU hD hI hf hp

end ZFVP
