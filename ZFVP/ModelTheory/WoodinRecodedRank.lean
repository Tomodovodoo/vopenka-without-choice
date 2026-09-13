import ZFVP.ModelTheory.WoodinRecodingCardinals
import ZFVP.ModelTheory.WoodinRecodedSuccessorNext
import ZFVP.ModelTheory.NormalizedCarrierRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinRecodedSuccessorCarrier_small {Ω k Q T m ξ : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
    (hm : ∀ i ∈ succ k, IsForcingIsomorphism
      ((forcingCodeP (woodinNormalizedPrefixCode (succ k))) ‘ i)
      ((forcingCodeR (woodinNormalizedPrefixCode (succ k))) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ succ k, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable (succ k) Q) (hTt : IsIterationTable (succ k) T)
    (hQrank : Q ‘ k ∈ hierarchy (woodinNormalizedSuccessorCutoff k))
    (hξ : IsChoicelessInaccessible ξ) (hdξ : woodinNormalizedSuccessorCutoff k ∈ ξ) :
    woodinRecodedSuccessorCarrier k
      (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m) ∈ hierarchy ξ := by
  let := hΩ.inaccessible.1
  let := hξ.1
  let s := woodinNormalizedStageCode k
  let c := forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m
  have hsub : succ k ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hk
    · exact IsOrdinal.toIsTransitive.mem_trans hi hk
  have hs := woodinNormalizedStageCode_valid hΩ hAC hk
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm hT hQt hTt
  have hf := hm k (mem_succ_self k)
  rw [woodinNormalizedPrefix_successor hΩ hAC hk] at hf
  have hf' : IsForcingIsomorphism ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      ((forcingCodeP c) ‘ k) ((forcingCodeR c) ‘ k) (m ‘ k) := by
    simpa only [s, c, forcingRecodedCode, forcingCodeP_code, forcingCodeR_code] using hf
  have hft : (m ‘ k) ‘ ((forcingCodet s) ‘ k) = (forcingCodet c) ‘ k := by
    simp only [s, c, forcingRecodedCode, forcingCodet_code, forcingRecodedTops_value (mem_succ_self k),
      woodinNormalizedPrefix_successor hΩ hAC hk]
  have he := hf'.prefix_cutoff (hs.system.order.preorder k (mem_succ_self k))
    (hc.system.order.preorder k (mem_succ_self k)) (hs.system.tops.top k (mem_succ_self k))
    (hc.system.tops.top k (mem_succ_self k)) hft ((kpair.π₂ (woodinIterationRec k)) ‘ k)
  change woodinNormalizedSuccessorCutoff k = _ at he
  obtain ⟨hd, _⟩ := woodinNormalizedSuccessorCutoff_bounds hΩ hAC hk
  let := hd.1
  change woodinRecodedSuccessorCarrier k c ∈ hierarchy ξ
  unfold woodinRecodedSuccessorCarrier
  dsimp only
  rw [← he]
  apply normalizedNameTwoStep_mem_larger_hierarchy hξ.rankCriterion.2.2.1 hdξ
  simpa only [c, forcingRecodedCode, forcingCodeP_code] using hQrank

theorem woodinRecodedInverseCarrier_small {Ω θ Q T m ξ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
      ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
    (hQrank : ∀ i ∈ θ, Q ‘ i ∈ hierarchy (woodinNormalizedInverseCutoff θ))
    (hξ : IsChoicelessInaccessible ξ) (hdξ : woodinNormalizedInverseCutoff θ ∈ ξ) :
    woodinRecodedInverseCarrier θ (forcingRecodedCode θ (woodinNormalizedPrefixCode θ) Q T m) ∈ hierarchy ξ := by
  let := hΩ.inaccessible.1
  let := hξ.1
  let c := forcingRecodedCode θ (woodinNormalizedPrefixCode θ) Q T m
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm hT hQt hTt
  have col := hc.system.inverseColumn hz hc.subset_universe
  have hb := woodinNormalized_inverse_base_laws hΩ hAC hsub hz
  have hf := woodinRecodedInverseBaseMap_isomorphism hΩ hAC hsub hm hT hQt hTt
  have hft := woodinRecodedInverseBaseMap_top hΩ hAC hsub hm hT hQt hTt hz
  have he := hf.hartogs_prefix_cutoff hb.1 col.order.preorder hb.2 col.tops.top hft
    (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  change woodinNormalizedInverseCutoff θ = forcingInverseSourceCutoff θ c _ at he
  obtain ⟨_, hd, hθd, _⟩ := woodinNormalizedInverseCutoff_bounds hΩ hAC hθ h0 hlim hn
  let := hd.1
  have hA : forcingInverseCodePoset θ c ∈ hierarchy (woodinNormalizedInverseCutoff θ) := by
    have hh := (forcingInverseLimit_small_family (R := T)
      (π := forcingRecodedProjections θ (woodinNormalizedPrefixCode θ) m)
      hd (ordinal_mem_hierarchy_iff.mpr hθd) (hQt.mem_function hQrank)).1
    simpa only [c, forcingInverseCodePoset, forcingCodeUniverse, forcingRecodedCode, forcingCodeP_code,
      forcingCodeπ_code] using hh
  change woodinRecodedInverseCarrier θ c ∈ hierarchy ξ
  unfold woodinRecodedInverseCarrier
  dsimp only
  rw [← he]
  exact normalizedNameTwoStep_mem_larger_hierarchy hξ.rankCriterion.2.2.1 hdξ hA

end ZFVP
