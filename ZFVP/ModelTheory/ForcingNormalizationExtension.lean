import ZFVP.ModelTheory.ForcingNormalizationFamily

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingNormalizationFamily.extend {θ s m Q T ρ F M u N R n : V} [IsOrdinal θ]
    (h : IsForcingNormalizationFamily θ s m)
    (hr : IsForcingRetraction N R Q T n) (hR : IsForcingPreorder N R)
    (he : ∀ p ∈ Q, ⟨n ‘ p, p⟩ₖ ∈ T ∧ ⟨p, n ‘ p⟩ₖ ∈ T)
    (ht : n ‘ u = u)
    (hπ : ∀ i ∈ θ, ∀ p ∈ Q, (ρ ‘ i) ‘ (n ‘ p) = (m ‘ i) ‘ ((ρ ‘ i) ‘ p))
    (hE : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP s) ‘ i, n ‘ ((F ‘ i) ‘ p) = (F ‘ i) ‘ ((m ‘ i) ‘ p)) :
    IsForcingNormalizationFamily (succ θ) (forcingIterationCodeNext θ s Q T ρ F M u)
      (forcingFamilyNext θ m n) := by
  have old {i : V} (hi : i ∈ θ) : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  unfold forcingIterationCodeNext
  refine ⟨forcingFamilyNext_table _ _ _, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingCodeE_code, forcingCodet_code]
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [forcingFamilyNext_new, forcingFamilyNext_new, forcingFamilyNext_new,
        hr.fixedPoints_eq, hr.orderRestriction_eq hR]
      exact hr
    · simpa only [forcingFamilyNext_old hi] using h.retraction i hi
  · intro i hi p hp
    rcases mem_succ_iff.mp hi with rfl | hi
    · simpa only [forcingFamilyNext_new] using he p (by simpa only [forcingFamilyNext_new] using hp)
    · simpa only [forcingFamilyNext_old hi] using h.equivalent i hi p
        (by simpa only [forcingFamilyNext_old hi] using hp)
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · simpa only [forcingFamilyNext_new] using ht
    · simpa only [forcingFamilyNext_old hi] using h.fixesTop i hi
  · intro j hj i hij hi p hp
    rcases mem_succ_iff.mp hj with rfl | hj
    · simpa only [forcingFamilyNext_new, forcingFamilyNext_old hij, forcingMatrixNext_column hij]
        using hπ i hij p (by simpa only [forcingFamilyNext_new] using hp)
    · have hiθ := IsOrdinal.toIsTransitive.transitive j hj i hij
      simpa only [forcingFamilyNext_old hiθ, forcingFamilyNext_old hj, forcingMatrixNext_old hi hj]
        using h.projection j hj i hij hiθ p (by simpa only [forcingFamilyNext_old hj] using hp)
  · intro i hi j hj hij p hp
    rcases mem_succ_iff.mp hj with rfl | hj
    · rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingFamilyNext_new] at hp
        rw [forcingFamilyNext_new, forcingMatrixNext_diagonal, identity_value hp,
          identity_value (hr.inclusion _ (function_value_mem hr.maps hp))]
      · simpa only [forcingFamilyNext_new, forcingFamilyNext_old hi, forcingMatrixNext_column hi]
          using hE i hi p (by simpa only [forcingFamilyNext_old hi] using hp)
    · have hiθ : i ∈ θ := by
        rcases mem_succ_iff.mp hi with rfl | hi
        · exact (ne_of_mem (hij j hj) rfl).elim
        · exact hi
      simpa only [forcingFamilyNext_old hiθ, forcingFamilyNext_old hj, forcingMatrixNext_old hi hj]
        using h.sectionCoherent i hiθ j hj hij p (by simpa only [forcingFamilyNext_old hiθ] using hp)

end ZFVP
