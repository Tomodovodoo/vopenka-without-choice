import ZFVP.ModelTheory.ForcingSplitProjection
import ZFVP.ModelTheory.DirectLimitProjection
import ZFVP.SetTheory.ForcingSectionMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingThread_below_section_of_subset {θ P R π E U C k f p : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ)
    (hC : C ⊆ forcingInverseLimit θ P π U)
    (hsplit : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      IsForcingSplitProjection (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) (E ‘ ⟨i, j⟩ₖ))
    (hf : f ∈ C) (hp : p ∈ P ‘ k)
    (hsec : forcingSectionThread θ π E k p ∈ C) :
    ⟨f, (forcingThreadSection θ P π E k) ‘ p⟩ₖ ∈
      forcingThreadOrder θ R C ↔ ⟨f ‘ k, p⟩ₖ ∈ R ‘ k := by
  rw [forcingThreadSection_value hp]
  constructor
  · intro hle
    have hkval := ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hle).2.2 k hk
    rwa [forcingSectionThread_value hk, forcingSectionValue_self h hk hp] at hkval
  · intro hle
    have hf' := (mem_forcingInverseLimit_iff _ _ _ _ _).mp
      (hC f hf)
    let := IsOrdinal.of_mem hk
    apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
    refine ⟨hf, hsec, ?_⟩
    intro i hi
    let := IsOrdinal.of_mem hi
    rw [forcingSectionThread_value hi]
    rcases IsOrdinal.mem_trichotomy i k with hik | rfl | hki
    · have hik' : i ⊆ k := IsOrdinal.toIsTransitive.transitive _ hik
      rw [← hf'.2.2 k hk i hik hi]
      simpa only [forcingSectionValue, ite_eq_left hik] using
        (hsplit i hi k hk hik').projection.monotone _ (hf'.2.1 k hk) p hp hle
    · rwa [forcingSectionValue_self h hk hp]
    · have hki' : k ⊆ i := IsOrdinal.toIsTransitive.transitive _ hki
      have hik : i ∉ k := fun hik ↦ mem_irrefl i (hki' i hik)
      simp only [forcingSectionValue, ite_eq_right hik]
      apply ((hsplit k hk i hi hki').below _ (hf'.2.1 i hi) p hp).mpr
      rwa [hf'.2.2 i hi k hki hk]

theorem forcingThread_below_section {θ P R π E U k f p : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hsplit : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      IsForcingSplitProjection (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) (E ‘ ⟨i, j⟩ₖ))
    (hf : f ∈ forcingDirectLimit θ P π E U) (hp : p ∈ P ‘ k) :
    ⟨f, (forcingThreadSection θ P π E k) ‘ p⟩ₖ ∈
      forcingThreadOrder θ R (forcingDirectLimit θ P π E U) ↔ ⟨f ‘ k, p⟩ₖ ∈ R ‘ k := by
  exact forcingThread_below_section_of_subset h hk
    (forcingDirectLimit_subset θ P π E U) hsplit hf hp
    (forcingSectionThread_mem h hk hp hU)

theorem forcingDirectLimit_splitProjection {θ P R π E U k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hsplit : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      IsForcingSplitProjection (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) (E ‘ ⟨i, j⟩ₖ)) :
    IsForcingSplitProjection (P ‘ k) (R ‘ k) (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
      (forcingThreadCoordinate (forcingDirectLimit θ P π E U) k)
      (forcingThreadSection θ P π E k) := by
  refine ⟨forcingDirectLimit_coordinate_projection h hk hU
    (fun i hi j hj hij ↦ (hsplit i hi j hj hij).projection)
    (fun i hi j hj hij p hp q hq hpq ↦ (hsplit i hi j hj hij).monotone hp hq hpq),
    forcingThreadSection_maps h hk hU,
    fun p hp ↦ forcingThreadSection_retraction h hk hp hU, ?_⟩
  intro f hf p hp
  rw [forcingThreadCoordinate_value hf]
  exact forcingThread_below_section h hk hU hsplit hf hp

end ZFVP
