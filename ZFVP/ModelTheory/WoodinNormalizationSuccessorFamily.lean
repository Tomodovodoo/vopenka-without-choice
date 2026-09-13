import ZFVP.ModelTheory.ForcingNormalizationExtension
import ZFVP.ModelTheory.WoodinNormalizationSuccessorCoherence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 800000 in
theorem woodinNormalizationSuccessor_family {Ω k s K m : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hs : IsWoodinIteration Ω (succ k) s K)
    (h : IsForcingNormalizationFamily (succ k) s m) :
    IsForcingNormalizationFamily (succ (succ k)) (woodinIterationSuccessor k s K)
      (woodinNormalizationSuccessor k s K m) := by
  let P := (forcingCodeP s) ‘ k
  let R := (forcingCodeR s) ‘ k
  let o := (forcingCodet s) ‘ k
  let κ := K ‘ k
  let c := woodinPrefixCutoff P R o κ
  let N := forcingMapFixedPoints P (m ‘ k)
  let T := forcingOrderRestriction N R
  have hr : IsForcingRetraction N T P R (m ‘ k) := h.retraction k (mem_succ_self k)
  obtain ⟨hR, ht, hc, hP, hκc, hκ⟩ := hs.normalizationSuccessor_inputs hΩ
  have hT : IsForcingPreorder N T := forcingOrderRestriction_preorder hR hr.inclusion
  have ho : o ∈ N := by
    exact mem_sep_iff.mpr ⟨ht.1, h.fixesTop k (mem_succ_self k)⟩
  have he := h.equivalent k (mem_succ_self k)
  have hI := saturatedWoodinPrefix_iterand hR ht hc hP hκc hκ
  have hI' := hr.iterand_nameAction hR hT he hI
  have htop := hr.top_of_mem ht ho
  have hTnew := normalizedNameTwoStep_preorder (δ := c) hT htop hI'.posetName hI'.orderName hI'.preorder
  have hrnew := hs.normalizationSuccessor_retraction hΩ hr hT ho he
  have henew (z : V) := hs.normalizationSuccessor_equivalent hΩ hr hT ho he (z := z)
  have htnew := hs.normalizationSuccessor_top hΩ hr hT ho he
  have hpnew : ∀ i ∈ succ k, ∀ z ∈ (forcingCodeP (woodinIterationSuccessor k s K)) ‘ (succ k),
      ((forcingCodeπ (woodinIterationSuccessor k s K)) ‘ ⟨i, succ k⟩ₖ) ‘
        ((woodinNormalizationSuccessorMap k s K m) ‘ z) =
      (m ‘ i) ‘ (((forcingCodeπ (woodinIterationSuccessor k s K)) ‘ ⟨i, succ k⟩ₖ) ‘ z) := by
    intro i hi z hz
    have hcoh : ∀ p ∈ P, ((forcingCodeπ s) ‘ ⟨i, k⟩ₖ) ‘ ((m ‘ k) ‘ p) =
        (m ‘ i) ‘ (((forcingCodeπ s) ‘ ⟨i, k⟩ₖ) ‘ p) := by
      rcases mem_succ_iff.mp hi with hik | hik
      · subst i
        intro p hp
        have hid : ∀ q ∈ P, ((forcingCodeπ s) ‘ ⟨k, k⟩ₖ) ‘ q = q := by
          intro q hq
          have hh := hs.code.system.split.retraction k (mem_succ_self k) k (mem_succ_self k)
            (subset_refl _) q hq
          rwa [hs.code.system.split.secId k (mem_succ_self k) q hq] at hh
        rw [hid p hp, hid _ (hr.inclusion _ (function_value_mem hr.maps hp))]
      · exact h.projection k (mem_succ_self k) i hik (mem_succ_iff.mpr (Or.inr hik))
    simpa only [woodinNormalizationSuccessor_new, woodinNormalizationSuccessor_old hi] using
      woodinNormalizationSuccessor_projection_coherent hr hR hT ht ho hc hP hκc he hκ hi hcoh hz
  have hEnew : ∀ i ∈ succ k, ∀ p ∈ (forcingCodeP s) ‘ i,
      (woodinNormalizationSuccessorMap k s K m) ‘
        (((forcingCodeE (woodinIterationSuccessor k s K)) ‘ ⟨i, succ k⟩ₖ) ‘ p) =
      ((forcingCodeE (woodinIterationSuccessor k s K)) ‘ ⟨i, succ k⟩ₖ) ‘ ((m ‘ i) ‘ p) := by
    intro i hi p hp
    have hik : i ⊆ k := by
      rcases mem_succ_iff.mp hi with rfl | hik
      · exact subset_refl _
      · exact IsOrdinal.toIsTransitive.transitive _ hik
    have hmp := (h.retraction i hi).inclusion _ (function_value_mem (h.retraction i hi).maps hp)
    simpa only [woodinNormalizationSuccessor_new, woodinNormalizationSuccessor_old hi] using
      woodinNormalizationSuccessor_section_coherent hs.code hr hR hT ht ho hc hP hκc he hκ hi hp hmp
        (h.sectionCoherent i hi k (mem_succ_self k) hik p hp)
  simp only [woodinNormalizationSuccessor_new, woodinIterationSuccessor, forcingSuccessorCode_poset,
    forcingSuccessorCode_order, forcingSuccessorCode_top] at hrnew henew htnew
  unfold woodinNormalizationSuccessor woodinIterationSuccessor forcingSuccessorCode
  apply h.extend hrnew hTnew henew htnew
  · intro i hi z hz
    have hh := hpnew i hi z (by simpa only [woodinIterationSuccessor, forcingSuccessorCode_poset] using hz)
    simpa only [woodinIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
      forcingCodeπ_code, forcingMatrixNext_column hi] using hh
  · intro i hi p hp
    simpa only [woodinIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
      forcingCodeE_code, forcingMatrixNext_column hi] using hEnew i hi p hp

end ZFVP
