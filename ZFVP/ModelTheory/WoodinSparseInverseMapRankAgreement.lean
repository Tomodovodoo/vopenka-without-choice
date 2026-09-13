import ZFVP.ModelTheory.WoodinSparseActualInverseRankAgreement
import ZFVP.ModelTheory.WoodinNormalizedCodeRankAgreement
import ZFVP.ModelTheory.RankNormalizationMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable {Ω : V} [IsOrdinal Ω] [Nonempty (SetDomain (hierarchy Ω))]
  [(SetDomain (hierarchy Ω))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinNormalizedInverseBase_val_endpoint (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) (θ : SetDomain (hierarchy Ω)) [IsOrdinal θ] :
    (woodinNormalizedInverseBase θ).val = woodinNormalizedInverseBase θ.val := by
  let := hierarchy_transitive Ω
  have hs := (woodinIterationPrefixes_val_of_previous (hierarchy Ω) θ
    (fun i hi ↦ hΩ.rank_woodinIterationRec_val hAC i (IsOrdinal.of_mem hi))).1
  unfold woodinNormalizedInverseBase
  rw [rank_forcingInverseLimit_val hΩ.inaccessible.rankCriterion.2.2.1,
    forcingCodeP_val (hierarchy Ω), forcingCodeπ_val (hierarchy Ω), forcingCodeUniverse_val (hierarchy Ω),
    (hΩ.rank_woodinNormalizedCode_val hAC θ inferInstance).1, hs]

theorem woodinNormalizedInverseOrder_val_endpoint (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) (θ : SetDomain (hierarchy Ω)) [IsOrdinal θ] :
    (woodinNormalizedInverseOrder θ).val = woodinNormalizedInverseOrder θ.val := by
  let := hierarchy_transitive Ω
  unfold woodinNormalizedInverseOrder
  rw [forcingThreadOrder_val (hierarchy Ω), forcingCodeR_val (hierarchy Ω),
    (hΩ.rank_woodinNormalizedCode_val hAC θ inferInstance).1,
    woodinNormalizedInverseBase_val_endpoint hΩ hAC θ]

theorem woodinSparseInverseBaseMap_val_endpoint (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) (θ c m : SetDomain (hierarchy Ω)) [IsOrdinal θ] :
    (woodinSparseInverseBaseMap θ c m).val = woodinSparseInverseBaseMap θ.val c.val m.val := by
  let := hierarchy_transitive Ω
  unfold woodinSparseInverseBaseMap woodinRecodedInverseBaseMap
  rw [compose_val (hierarchy Ω), forcingThreadActionMap_val (hierarchy Ω),
    woodinNormalizedInverseBase_val_endpoint hΩ hAC θ,
    woodinSparseInverseFlatten_val_rank Ω hΩ.inaccessible.rankCriterion.2.2.1]

theorem woodinNormalizedInverseCutoff_val_endpoint (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) (θ : SetDomain (hierarchy Ω)) [IsOrdinal θ]
    (hzero : θ.val ≠ ∅) (hlim : ∀ i ∈ θ.val, succ i ∈ θ.val)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ.val))) :
    (woodinNormalizedInverseCutoff θ).val = woodinNormalizedInverseCutoff θ.val := by
  let := hierarchy_transitive Ω
  let := (ordinal_iff (hierarchy Ω) θ).mp (inferInstance : IsOrdinal θ)
  have hθ : θ.val ∈ Ω := ordinal_mem_hierarchy_iff.mp θ.property
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have h0 : (∅ : V) ∈ θ.val := (IsOrdinal.subset_iff.mp (empty_subset θ.val)).resolve_left (fun he ↦ hzero he.symm)
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hsub i hi)).1)
  let P := woodinNormalizedInverseBase θ
  let R := woodinNormalizedInverseOrder θ
  let one := forcingInverseCodeTop θ (woodinIterationPrefix θ)
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  have hP : P.val = woodinNormalizedInverseBase θ.val := woodinNormalizedInverseBase_val_endpoint hΩ hAC θ
  have hR : R.val = woodinNormalizedInverseOrder θ.val := woodinNormalizedInverseOrder_val_endpoint hΩ hAC θ
  have hγ : γ.val = woodinLimitCardinal (woodinIterationCardinalPrefix θ.val) :=
    woodinIterationLimitCardinal_val_endpoint hΩ hAC θ
  have hpref := (woodinIterationPrefixes_val_of_previous (hierarchy Ω) θ
    (fun i hi ↦ hΩ.rank_woodinIterationRec_val hAC i (IsOrdinal.of_mem hi))).1
  have ho : one.val = forcingInverseCodeTop θ.val (woodinIterationPrefix θ.val) := by
    rw [forcingInverseCodeTop_val (hierarchy Ω), hpref]
  have hl := woodinNormalized_inverse_base_laws hΩ hAC hsub h0
  have hi : IsForcingPreorder P.val R.val := by rw [hP, hR]; exact hl.1
  have ht : IsForcingTop P.val R.val one.val := by rw [hP, hR, ho]; exact hl.2
  have hgord : IsOrdinal γ.val := hγ.symm ▸ hs.limitCardinal_ordinal
  have hgmem : γ.val ∈ Ω := by
    let := hgord
    exact ordinal_mem_hierarchy_iff.mp γ.property
  have hsmall : ∀ κ : V, IsChoicelessInaccessible κ → γ.val ∈ κ → P.val ∈ hierarchy κ := by
    intro κ hκ hgκ
    let := hκ.1
    rw [hP]
    apply subset_mem_hierarchy_limit hκ.rankCriterion.2.2.1
      (hs.inverse_small_above_limit hlim hκ (hγ ▸ hgκ)).1
    rw [← (woodinNormalized_inverse_base_dictionary hΩ hAC hsub).1]
    exact sep_subset
  have hf := woodinSparseRawInverse_isomorphism hΩ hAC hsub h0 hlim
  have hft := woodinSparseRawInverse_top hΩ hAC hsub h0 hlim
  have hraw := woodinSparsePrefix_inverse_rankInputs hΩ hAC hθ hzero hlim hn
  have hforce (φ : SetTheorySemisentence 1)
      (hh : ∀ p ∈ woodinSparseInverseBase θ.val (woodinSparsePrefixCode θ.val),
        p ∈ forcingFormula (woodinSparseInverseBase θ.val (woodinSparsePrefixCode θ.val))
          (woodinSparseInverseOrder θ.val (woodinSparsePrefixCode θ.val)) φ
          (standardTuple ![hartogsNumberName (woodinSparseInverseBase θ.val (woodinSparsePrefixCode θ.val))
            (woodinSparseInverseOrder θ.val (woodinSparsePrefixCode θ.val))
            (checkName ∅ (woodinLimitCardinal (woodinIterationCardinalPrefix θ.val)))])) :
      ∀ p ∈ P.val, p ∈ forcingFormula P.val R.val φ
        (standardTuple ![hartogsNumberName P.val R.val (checkName one.val γ.val)]) := by
    rw [hP, hR, ho, hγ]
    intro p hp
    exact (hf.hartogs_forcing_iff hl.1 hraw.preorder hl.2 hft hp φ).mpr
      (hh _ (function_value_mem hf.1 hp))
  have hc := hartogsPrefixCutoff_val_endpoint hΩ P R one γ hi ht hgmem hsmall
    (hforce regularCardinalFormula hraw.regular) (hforce dependentChoiceBelowFormula hraw.dc)
  change (woodinNormalizedInverseCutoff θ).val = _ at hc
  rw [hP, hR, ho, hγ] at hc
  exact hc

theorem woodinSparseInversePairMap_val_of_actual_prefix (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) (θ c m : SetDomain (hierarchy Ω)) [IsOrdinal θ]
    (hc : c.val = woodinSparsePrefixCode θ.val)
    (hm : m.val = woodinRecodingMaps (woodinSparseRecodingHistory θ.val))
    (hzero : θ.val ≠ ∅) (hlim : ∀ i ∈ θ.val, succ i ∈ θ.val)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ.val))) :
    (woodinSparseInversePairMap θ c m).val = woodinSparseInversePairMap θ.val c.val m.val := by
  let := hierarchy_transitive Ω
  let := (ordinal_iff (hierarchy Ω) θ).mp (inferInstance : IsOrdinal θ)
  have hθ : θ.val ∈ Ω := ordinal_mem_hierarchy_iff.mp θ.property
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have h0 : (∅ : V) ∈ θ.val := (IsOrdinal.subset_iff.mp (empty_subset θ.val)).resolve_left (fun he ↦ hzero he.symm)
  let P := woodinNormalizedInverseBase θ
  let R := woodinNormalizedInverseOrder θ
  let one := forcingInverseCodeTop θ (woodinIterationPrefix θ)
  let δ := woodinNormalizedInverseCutoff θ
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  let A := woodinSparseInverseBase θ c
  let B := woodinSparseInverseOrder θ c
  let f := woodinSparseInverseBaseMap θ c m
  let Q := saturatedHartogsPosetName P R one γ δ
  have hP : P.val = woodinNormalizedInverseBase θ.val := woodinNormalizedInverseBase_val_endpoint hΩ hAC θ
  have hR : R.val = woodinNormalizedInverseOrder θ.val := woodinNormalizedInverseOrder_val_endpoint hΩ hAC θ
  have hγ : γ.val = woodinLimitCardinal (woodinIterationCardinalPrefix θ.val) :=
    woodinIterationLimitCardinal_val_endpoint hΩ hAC θ
  have hpref := (woodinIterationPrefixes_val_of_previous (hierarchy Ω) θ
    (fun i hi ↦ hΩ.rank_woodinIterationRec_val hAC i (IsOrdinal.of_mem hi))).1
  have ho : one.val = forcingInverseCodeTop θ.val (woodinIterationPrefix θ.val) := by
    rw [forcingInverseCodeTop_val (hierarchy Ω), hpref]
  have hδ : δ.val = woodinNormalizedInverseCutoff θ.val :=
    woodinNormalizedInverseCutoff_val_endpoint hΩ hAC θ hzero hlim hn
  have hA : A.val = woodinSparseInverseBase θ.val c.val :=
    woodinSparseInverseBase_val_rank Ω hΩ.inaccessible.rankCriterion.2.2.1 θ c
  have hB : B.val = woodinSparseInverseOrder θ.val c.val :=
    woodinSparseInverseOrder_val_rank Ω hΩ.inaccessible.rankCriterion.2.2.1 θ c
  have hf : f.val = woodinSparseInverseBaseMap θ.val c.val m.val :=
    woodinSparseInverseBaseMap_val_endpoint hΩ hAC θ c m
  have hl := woodinNormalized_inverse_base_laws hΩ hAC hsub h0
  have hp : IsForcingPreorder P.val R.val := by rw [hP, hR]; exact hl.1
  have ht : IsForcingTop P.val R.val one.val := by rw [hP, hR, ho]; exact hl.2
  have hraw := woodinSparseRawInverse_laws hΩ hAC hsub h0 hlim
  have hb : IsForcingPreorder A.val B.val := by rw [hA, hB, hc]; exact hraw.1
  have htop : (∅ : SetDomain (hierarchy Ω)).val ∈ A.val := by
    rw [empty_val (hierarchy Ω), hA, hc]; exact hraw.2.1
  have hfmap : f.val ∈ A.val ^ P.val := by
    rw [hf, hA, hP, hc, hm]
    exact (woodinSparseRawInverse_isomorphism hΩ hAC hsub h0 hlim).1
  have hδord : IsOrdinal δ := by
    dsimp only [δ, woodinNormalizedInverseCutoff]
    infer_instance
  have hQ : Q.val = saturatedHartogsPosetName P.val R.val one.val γ.val δ.val :=
    rank_saturatedHartogsPosetName_val hΩ.inaccessible P R one γ δ
      ((forcingPreorder_iff (hierarchy Ω) P R).mpr hp)
      ((forcingTop_iff (hierarchy Ω) P R one).mpr ht) hδord
  have he := normalizedTwoStepIsoMap_val_rank Ω P R one δ Q A B ∅ f
    hδord hp ht.1 hfmap hb htop
  change (woodinSparseInversePairMap θ c m).val = _ at he
  rw [hQ, hP, hR, ho, hγ, hδ, hA, hB, empty_val (hierarchy Ω), hf] at he
  exact he

theorem woodinSparseCompletedInverseMap_val_of_actual_prefix (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) (θ c m : SetDomain (hierarchy Ω)) [IsOrdinal θ]
    (hc : c.val = woodinSparsePrefixCode θ.val)
    (hm : m.val = woodinRecodingMaps (woodinSparseRecodingHistory θ.val))
    (hzero : θ.val ≠ ∅) (hlim : ∀ i ∈ θ.val, succ i ∈ θ.val)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ.val))) :
    (woodinSparseCompletedInverseMap θ c m).val = woodinSparseCompletedInverseMap θ.val c.val m.val := by
  let := hierarchy_transitive Ω
  have hp := (woodinSparseCompletedInverse_val_of_actual_prefix hΩ hAC θ c hc hzero hlim hn).2.1
  unfold woodinSparseCompletedInverseMap
  rw [compose_val (hierarchy Ω), woodinSparseInversePairMap_val_of_actual_prefix hΩ hAC θ c m hc hm hzero hlim hn,
    sparsePairEncode_val (hierarchy Ω), woodinSparseInverseBase_val_rank Ω hΩ.inaccessible.rankCriterion.2.2.1, hp]

end TransitiveZF
end ZFVP


