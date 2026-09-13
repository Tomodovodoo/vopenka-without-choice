import ZFVP.ModelTheory.RankSparseLimits
import ZFVP.ModelTheory.RankSparseNormalizedTwoStep
import ZFVP.ModelTheory.RankSaturatedHartogsNameAgreement
import ZFVP.ModelTheory.WoodinSourceEndpointAgreement
import ZFVP.ModelTheory.HartogsLeastPrefixCutoffRankAgreement
import ZFVP.ModelTheory.WoodinSparseInverseStage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem saturatedHartogsNormalizedPool_val_rank (hξ : IsChoicelessInaccessible ξ)
    (P R one γ δ : SetDomain (hierarchy ξ))
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hδ : IsOrdinal δ) :
    (normalizedNamePool P R one δ (saturatedHartogsPosetName P R one γ δ)).val =
      normalizedNamePool P.val R.val one.val δ.val
        (saturatedHartogsPosetName P.val R.val one.val γ.val δ.val) := by
  let := hierarchy_transitive ξ
  rw [normalizedNamePool_val_rank ξ _ _ _ _ _ hδ
    ((forcingPreorder_iff (hierarchy ξ) P R).mp hR)
    ((forcingTop_iff (hierarchy ξ) P R one).mp ht).1,
    rank_saturatedHartogsPosetName_val hξ P R one γ δ hR ht hδ]

theorem saturatedHartogsSparseCarrier_val_rank (hξ : IsChoicelessInaccessible ξ)
    (a P R one γ δ : SetDomain (hierarchy ξ))
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hδ : IsOrdinal δ) :
    (sparseNormalizedTwoStep a P R one δ (saturatedHartogsPosetName P R one γ δ)).val =
      sparseNormalizedTwoStep a.val P.val R.val one.val δ.val
        (saturatedHartogsPosetName P.val R.val one.val γ.val δ.val) := by
  let := hierarchy_transitive ξ
  unfold sparseNormalizedTwoStep
  rw [sparsePairCarrier_val (hierarchy ξ), saturatedHartogsNormalizedPool_val_rank hξ P R one γ δ hR ht hδ]

theorem saturatedHartogsSparseOrder_val_rank (hξ : IsChoicelessInaccessible ξ)
    (a P R one γ δ : SetDomain (hierarchy ξ))
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hδ : IsOrdinal δ) :
    (sparseNormalizedTwoStepOrder a P R one δ (saturatedHartogsPosetName P R one γ δ)
      (saturatedHartogsOrderName P R one γ δ)).val =
      sparseNormalizedTwoStepOrder a.val P.val R.val one.val δ.val
        (saturatedHartogsPosetName P.val R.val one.val γ.val δ.val)
        (saturatedHartogsOrderName P.val R.val one.val γ.val δ.val) := by
  let := hierarchy_transitive ξ
  unfold saturatedHartogsOrderName
  rw [sparseNormalizedReverseOrder_val_rank ξ a P R one δ _ hδ hR ht
    (saturatedHartogsPosetName_isName _ _ _ _ _),
    rank_saturatedHartogsPosetName_val hξ P R one γ δ hR ht hδ]

theorem woodinIterationLimitCardinal_val_endpoint (hξ : IsWoodinSupercompact ξ)
    (hAC : ¬InternalChoice V) (θ : SetDomain (hierarchy ξ)) [IsOrdinal θ] :
    (woodinLimitCardinal (woodinIterationCardinalPrefix θ)).val =
      woodinLimitCardinal (woodinIterationCardinalPrefix θ.val) := by
  let := hierarchy_transitive ξ
  rw [woodinLimitCardinal_val (hierarchy ξ)]
  rw [(woodinIterationPrefixes_val_of_previous (hierarchy ξ) θ
    (fun i hi ↦ hξ.rank_woodinIterationRec_val hAC i (IsOrdinal.of_mem hi))).2]

omit [IsOrdinal ξ] in
theorem hartogsPrefixCutoff_val_endpoint (hξ : IsWoodinSupercompact ξ)
    (P R one γ : SetDomain (hierarchy ξ))
    (hR : IsForcingPreorder P.val R.val) (ht : IsForcingTop P.val R.val one.val)
    (hγ : γ.val ∈ ξ)
    (hsmall : ∀ κ : V, IsChoicelessInaccessible κ → γ.val ∈ κ → P.val ∈ hierarchy κ)
    (hreg : ∀ p ∈ P.val, p ∈ forcingFormula P.val R.val regularCardinalFormula
      (standardTuple ![hartogsNumberName P.val R.val (checkName one.val γ.val)]))
    (hDC : ∀ p ∈ P.val, p ∈ forcingFormula P.val R.val dependentChoiceBelowFormula
      (standardTuple ![hartogsNumberName P.val R.val (checkName one.val γ.val)])) :
    (woodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ))).val =
      woodinNamedPrefixCutoff P.val R.val one.val γ.val
        (hartogsNumberName P.val R.val (checkName one.val γ.val)) := by
  obtain ⟨η, hη, _, he⟩ := hξ.eventually_rank_hartogsPrefixCutoff_eq hR ht P.property R.property hγ hsmall hreg hDC
  exact he ξ hη hξ.inaccessible P R one γ rfl rfl rfl rfl

end TransitiveZF

/-- Forcing invariants needed for the Hartogs restoration selector at a raw
sparse inverse stage. The fields contain no rank-computation agreement. -/
structure SparseInverseRankForcingInputs (θ c : V) : Prop where
  preorder : IsForcingPreorder (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c)
  top : IsForcingTop (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) ∅
  cardinalOrdinal : IsOrdinal (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  small : ∀ κ : V, IsChoicelessInaccessible κ →
    woodinLimitCardinal (woodinIterationCardinalPrefix θ) ∈ κ → woodinSparseInverseBase θ c ∈ hierarchy κ
  regular : ∀ p ∈ woodinSparseInverseBase θ c,
    p ∈ forcingFormula (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) regularCardinalFormula
      (standardTuple ![hartogsNumberName (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c)
        (checkName ∅ (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))])
  dc : ∀ p ∈ woodinSparseInverseBase θ c,
    p ∈ forcingFormula (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) dependentChoiceBelowFormula
      (standardTuple ![hartogsNumberName (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c)
        (checkName ∅ (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))])

namespace TransitiveZF
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseCompletedInverse_val_endpoint (hξ : IsWoodinSupercompact ξ)
    (hAC : ¬InternalChoice V) (θ c : SetDomain (hierarchy ξ)) [IsOrdinal θ]
    (h : SparseInverseRankForcingInputs θ.val c.val) :
    (woodinSparseInverseCutoff θ c).val = woodinSparseInverseCutoff θ.val c.val ∧
    (woodinSparseInversePool θ c).val = woodinSparseInversePool θ.val c.val ∧
    (woodinSparseCompletedInverseCarrier θ c).val = woodinSparseCompletedInverseCarrier θ.val c.val ∧
    (woodinSparseCompletedInverseOrder θ c).val = woodinSparseCompletedInverseOrder θ.val c.val := by
  let := hierarchy_transitive ξ
  let A := woodinSparseInverseBase θ c
  let B := woodinSparseInverseOrder θ c
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  let δ := woodinSparseInverseCutoff θ c
  have hA : A.val = woodinSparseInverseBase θ.val c.val :=
    woodinSparseInverseBase_val_rank ξ hξ.inaccessible.rankCriterion.2.2.1 θ c
  have hB : B.val = woodinSparseInverseOrder θ.val c.val :=
    woodinSparseInverseOrder_val_rank ξ hξ.inaccessible.rankCriterion.2.2.1 θ c
  have hγ : γ.val = woodinLimitCardinal (woodinIterationCardinalPrefix θ.val) :=
    woodinIterationLimitCardinal_val_endpoint hξ hAC θ
  have hR : IsForcingPreorder A.val B.val := by rw [hA, hB]; exact h.preorder
  have ht : IsForcingTop A.val B.val (∅ : SetDomain (hierarchy ξ)).val := by
    rw [hA, hB, empty_val (hierarchy ξ)]; exact h.top
  have hγord : IsOrdinal γ.val := hγ.symm ▸ h.cardinalOrdinal
  have hγmem : γ.val ∈ ξ := by
    let := hγord
    exact ordinal_mem_hierarchy_iff.mp γ.property
  have hc := hartogsPrefixCutoff_val_endpoint hξ A B ∅ γ hR ht hγmem
    (by rw [hγ, hA]; exact h.small)
    (by rw [hA, hB, empty_val (hierarchy ξ), hγ]; exact h.regular)
    (by rw [hA, hB, empty_val (hierarchy ξ), hγ]; exact h.dc)
  have hδ : δ.val = woodinSparseInverseCutoff θ.val c.val := by
    change δ.val = _ at hc
    rw [hA, hB, empty_val (hierarchy ξ), hγ] at hc
    exact hc
  have hδord : IsOrdinal δ := by
    dsimp only [δ, woodinSparseInverseCutoff]
    infer_instance
  have hRi := (forcingPreorder_iff (hierarchy ξ) A B).mpr hR
  have hti := (forcingTop_iff (hierarchy ξ) A B ∅).mpr ht
  have hp := saturatedHartogsNormalizedPool_val_rank hξ.inaccessible A B ∅ γ δ hRi hti hδord
  have hpool : (woodinSparseInversePool θ c).val = woodinSparseInversePool θ.val c.val := by
    change (woodinSparseInversePool θ c).val = _ at hp
    rw [hA, hB, empty_val (hierarchy ξ), hγ, hδ] at hp
    exact hp
  have hcar : (woodinSparseCompletedInverseCarrier θ c).val = woodinSparseCompletedInverseCarrier θ.val c.val := by
    unfold woodinSparseCompletedInverseCarrier
    rw [sparsePairCarrier_val (hierarchy ξ), hpool, woodinSparseInverseBase_val_rank ξ hξ.inaccessible.rankCriterion.2.2.1]
  have ho := saturatedHartogsSparseOrder_val_rank hξ.inaccessible θ A B ∅ γ δ hRi hti hδord
  have hord : (woodinSparseCompletedInverseOrder θ c).val = woodinSparseCompletedInverseOrder θ.val c.val := by
    change (woodinSparseCompletedInverseOrder θ c).val = _ at ho
    rw [hA, hB, empty_val (hierarchy ξ), hγ, hδ] at ho
    exact ho
  exact ⟨hδ, hpool, hcar, hord⟩

end TransitiveZF
end ZFVP


