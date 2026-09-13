import ZFVP.ModelTheory.ForcingNormalizationLiftClosure
import ZFVP.ModelTheory.WoodinNormalizationSuccessorFamily

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 800000 in
theorem woodinNormalizationSuccessor_liftClosed {Ω k s K m : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hs : IsWoodinIteration Ω (succ k) s K)
    (h : IsForcingNormalizationFamily (succ k) s m)
    (hL : IsForcingNormalizationLiftClosed (succ k) s m) :
    IsForcingNormalizationLiftClosed (succ (succ k)) (woodinIterationSuccessor k s K)
      (woodinNormalizationSuccessor k s K m) := by
  let P := (forcingCodeP s) ‘ k
  let R := (forcingCodeR s) ‘ k
  let o := (forcingCodet s) ‘ k
  let κ := K ‘ k
  let c := woodinPrefixCutoff P R o κ
  let Q := saturatedWoodinPrefixPosetName P R o κ c
  let N := forcingMapFixedPoints P (m ‘ k)
  let T := forcingOrderRestriction N R
  have hr : IsForcingRetraction N T P R (m ‘ k) := h.retraction k (mem_succ_self k)
  have hR := hs.code.system.order.preorder k (mem_succ_self k)
  have hT : IsForcingPreorder N T := forcingOrderRestriction_preorder hR hr.inclusion
  have ho : o ∈ N := mem_sep_iff.mpr
    ⟨(hs.code.system.tops.top k (mem_succ_self k)).1, h.fixesTop k (mem_succ_self k)⟩
  have hrnew := hs.normalizationSuccessor_retraction hΩ hr hT ho (h.equivalent k (mem_succ_self k))
  have hshape : forcingMapFixedPoints (twoStepConditions P R Q ∅)
      (woodinNormalizationSuccessorMap k s K m) = normalizedNameTwoStep N T o c (nameAction (m ‘ k) Q) := by
    simpa only [woodinIterationSuccessor, forcingSuccessorCode_poset] using hrnew.fixedPoints_eq
  unfold woodinNormalizationSuccessor woodinIterationSuccessor forcingSuccessorCode
  apply hL.extend
  intro i hi a ha b hb hle
  rw [hshape] at ha ⊢
  have haP : a ∈ twoStepConditions P R Q ∅ := by
    simpa only [woodinIterationSuccessor, forcingSuccessorCode_poset] using hrnew.inclusion a ha
  have hbP := h.inclusion i hi b hb
  rw [successorProjectionColumn_value hi haP] at hle
  rw [successorLiftColumn_value hi haP hbP]
  obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp ha
  have hik : i ⊆ k := by
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hi
  have hpN : p ∈ (forcingNormalizationCarriers (succ k) s m) ‘ k := by
    rwa [forcingNormalizationCarriers_value (mem_succ_self k)]
  have hl := hL i hi k (mem_succ_self k) hik p hpN b hb
    (by simpa only [kpair.π₁_kpair] using hle)
  rw [forcingNormalizationCarriers_value (mem_succ_self k)] at hl
  simpa only [successorForcingLiftValue, twoStepStronger, kpair.π₁_kpair, kpair.π₂_kpair,
    normalizedNameTwoStep]
    using (kpair_mem_iff.mpr ⟨hl, hτ⟩ :
      ⟨((forcingCodeL s) ‘ ⟨i, k⟩ₖ) ‘ ⟨p, b⟩ₖ, τ⟩ₖ ∈ N ×ˢ normalizedNamePool N T o c (nameAction (m ‘ k) Q))

end ZFVP

