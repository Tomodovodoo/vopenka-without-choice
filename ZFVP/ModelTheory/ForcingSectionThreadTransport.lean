import ZFVP.ModelTheory.ForcingRecodedLimits
import ZFVP.ModelTheory.ForcingNormalizedLimits

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s m k p : V} [IsOrdinal θ]

theorem forcingNormalized_sectionThread
    (hs : IsForcingIterationCode θ s) (hm : IsForcingNormalizationFamily θ s m)
    (hk : k ∈ θ) (hp : p ∈ (forcingNormalizationCarriers θ s m) ‘ k) :
    forcingSectionThread θ (forcingNormalizationProjections θ s m) (forcingNormalizationSections θ s m) k p =
      forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) k p := by
  classical
  unfold forcingSectionThread
  apply functions_eq_of_domain_values
  · rw [domain_definableGraph, domain_definableGraph]
  · intro i hi
    rw [domain_definableGraph] at hi
    simp only [value_definableGraph _ _ _ hi]
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hk
    by_cases hik : i ∈ k
    · simp only [forcingSectionValue, ite_eq_left hik]
      exact forcingNormalizationProjections_apply hm hs hi hk (IsOrdinal.toIsTransitive.transitive _ hik) hp
    · have hki : k ⊆ i := by
        rcases IsOrdinal.mem_trichotomy i k with hh | rfl | hh
        · exact (hik hh).elim
        · exact subset_refl _
        · exact IsOrdinal.toIsTransitive.transitive _ hh
      simp only [forcingSectionValue, ite_eq_right hik]
      exact forcingNormalizationSections_apply hm hs hk hi hki hp

theorem forcingRecoded_sectionThread {Q T : V}
    (hs : IsForcingIterationCode θ s)
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hk : k ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ k) :
    forcingThreadAction θ m (forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) k p) =
      forcingSectionThread θ (forcingRecodedProjections θ s m) (forcingRecodedSections θ s m) k ((m ‘ k) ‘ p) := by
  classical
  unfold forcingThreadAction forcingSectionThread
  apply functions_eq_of_domain_values
  · rw [domain_definableGraph, domain_definableGraph]
  · intro i hi
    rw [domain_definableGraph] at hi
    simp only [value_definableGraph _ _ _ hi]
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hk
    by_cases hik : i ∈ k
    · simp only [forcingSectionValue, ite_eq_left hik]
      exact (forcingRecodedProjections_image hs hm hi hk (IsOrdinal.toIsTransitive.transitive _ hik) hp).symm
    · have hki : k ⊆ i := by
        rcases IsOrdinal.mem_trichotomy i k with hh | rfl | hh
        · exact (hik hh).elim
        · exact subset_refl _
        · exact IsOrdinal.toIsTransitive.transitive _ hh
      simp only [forcingSectionValue, ite_eq_right hik]
      exact (forcingRecodedSections_image hs hm hk hi hki hp).symm

end ZFVP
