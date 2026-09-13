import ZFVP.ModelTheory.WoodinSparseCodedForcingEquality
set_option maxHeartbeats 800000
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal Ω] [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hθ : IsWoodinSupercompact θ) (hAC : ¬InternalChoice V)
  {G : Set V} (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G) (hθΩ : θ ∈ Ω)
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG
include hθ hθΩ

/-- W06 at the source's fixed r_(k+1), for the explicitly fixed W05 formula.
This uses the source quantifier bound directly, not the earlier implementation
dictionary estimate. -/
theorem woodinSparse_cn_coded_source_window (k : ℕ)
    (hΩC : Cn (woodinCodedForcingLevel k) Ω) (hθC : Cn (woodinCodedForcingLevel k) θ) :
    Cn (k + 1) (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hθΩ) := by
  let := hierarchy_transitive ((E).check Ω)
  let := hierarchy_transitive ((E).check θ)
  let := woodinSparseLowerRank_nonempty hΩ hθ hAC hG hθΩ
  let := woodinSparseLowerRank_models_zf hΩ hθ hAC hG hθΩ
  have hsub : hierarchy ((E).check θ) ⊆ hierarchy ((E).check Ω) :=
    hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ (((E).check_mem_iff _ _).mpr hθΩ))
  have hrel := relativeSigmaCorrect_of_domainTruthFormula
    (hierarchy ((E).check θ)) (hierarchy ((E).check Ω)) hsub k
    (woodinSparseLowerRank_formula_reflection hΩ hθ hAC hG hθΩ
      (woodinIteration_supercompact_fixedPoint hΩ hθ hAC hθΩ) hΩC hθC
      (domainTruthFormula .sigma k) (woodinCodedForcingTranslation_complexity k).1
      (woodinCodedForcingTranslation_complexity k).2)
  exact (TransitiveZF.cn_iff_relative (hierarchy ((E).check Ω)) k
    (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hθΩ)
    (show IsOrdinal ((E).check θ) from inferInstance) hsub).mpr hrel

theorem woodinSparse_cn_coded_source_positive_window (k : ℕ) (hk : 0 < k)
    (hΩC : Cn (woodinCodedForcingLevel (k - 1)) Ω) (hθC : Cn (woodinCodedForcingLevel (k - 1)) θ) :
    Cn k (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hθΩ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact woodinSparse_cn_coded_source_window hΩ hθ hAC hG hθΩ j hΩC hθC

end ZFVP


