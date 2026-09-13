import ZFVP.ModelTheory.ForcingRecodedLimits
import ZFVP.ModelTheory.ForcingNormalizedLimits

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s m f i b : V} [IsOrdinal θ]

theorem forcingNormalized_threadSplice
    (hs : IsForcingIterationCode θ s) (hm : IsForcingNormalizationFamily θ s m)
    (hi : i ∈ θ) (hb : b ∈ (forcingNormalizationCarriers θ s m) ‘ i)
    (hf : ∀ j ∈ θ, f ‘ j ∈ (forcingNormalizationCarriers θ s m) ‘ j) :
    forcingThreadSplice θ (forcingNormalizationProjections θ s m) (forcingNormalizationLifts θ s m) f i b =
      forcingThreadSplice θ (forcingCodeπ s) (forcingCodeL s) f i b := by
  classical
  unfold forcingThreadSplice
  apply functions_eq_of_domain_values
  · rw [domain_definableGraph, domain_definableGraph]
  · intro j hj
    rw [domain_definableGraph] at hj
    simp only [value_definableGraph _ _ _ hj]
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hj
    by_cases hji : j ∈ i
    · simp only [forcingSpliceValue, ite_eq_left hji]
      exact forcingNormalizationProjections_apply hm hs hj hi (IsOrdinal.toIsTransitive.transitive _ hji) hb
    · simp only [forcingSpliceValue, ite_eq_right hji]
      exact forcingNormalizationLifts_apply hi hj (hf j hj) hb

theorem forcingRecoded_threadSplice {Q T : V}
    (hs : IsForcingIterationCode θ s)
    (hm : ∀ j ∈ θ, IsForcingIsomorphism ((forcingCodeP s) ‘ j) ((forcingCodeR s) ‘ j)
      (Q ‘ j) (T ‘ j) (m ‘ j))
    (hi : i ∈ θ) (hb : b ∈ (forcingCodeP s) ‘ i)
    (hf : ∀ j ∈ θ, f ‘ j ∈ (forcingCodeP s) ‘ j) :
    forcingThreadAction θ m (forcingThreadSplice θ (forcingCodeπ s) (forcingCodeL s) f i b) =
      forcingThreadSplice θ (forcingRecodedProjections θ s m) (forcingRecodedLifts θ s Q m)
        (forcingThreadAction θ m f) i ((m ‘ i) ‘ b) := by
  classical
  unfold forcingThreadAction forcingThreadSplice
  apply functions_eq_of_domain_values
  · rw [domain_definableGraph, domain_definableGraph]
  · intro j hj
    rw [domain_definableGraph] at hj
    simp only [value_definableGraph _ _ _ hj]
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hj
    by_cases hji : j ∈ i
    · simp only [forcingSpliceValue, ite_eq_left hji]
      exact (forcingRecodedProjections_image hs hm hj hi (IsOrdinal.toIsTransitive.transitive _ hji) hb).symm
    · simp only [forcingSpliceValue, ite_eq_right hji]
      simpa only [value_definableGraph _ _ _ hj] using
        (forcingRecodedLifts_image hm hi hj (hf j hj) hb).symm

end ZFVP
