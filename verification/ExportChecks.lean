import ZFVP.ModelTheory.BlockCohenRigidConsistency
import ZFVP.ModelTheory.ClassForcingDensitySemantics
import ZFVP.ModelTheory.ClassForcingVopenkaDensityComplete
import ZFVP.ModelTheory.CohenRigidRestoration
import ZFVP.ModelTheory.CohenVopenkaConsistency
import ZFVP.ModelTheory.CountabilityEssentialTheorem
import ZFVP.ModelTheory.CountableCohenVopenkaConsistency
import ZFVP.ModelTheory.CountablePrunedGroundModel
import ZFVP.ModelTheory.DerivedUltrafilterComplete
import ZFVP.ModelTheory.FefermanLevyConsistency
import ZFVP.ModelTheory.ForcedWellOrdering
import ZFVP.ModelTheory.ForcingWellOrdering
import ZFVP.ModelTheory.PiSymmetricVopenkaPreservation
import ZFVP.ModelTheory.RankBerkeleyDescent
import ZFVP.ModelTheory.RealSolovayConsistency
import ZFVP.ModelTheory.RealSolovayRegularity
import ZFVP.ModelTheory.RealSolovayTheory
import ZFVP.ModelTheory.SVCVopenkaRestoration
import ZFVP.ModelTheory.SolovayCorollaryUnconditional
import ZFVP.ModelTheory.SolovayHODUltrafilter
import ZFVP.ModelTheory.SolovayLocalization
import ZFVP.ModelTheory.SolovayLocalizationSequences
import ZFVP.ModelTheory.SymmetricExtensionZF
import ZFVP.ModelTheory.SymmetricLiftFixedClosure
import ZFVP.ModelTheory.SymmetricLiftOrdinary
import ZFVP.ModelTheory.SymmetricModelZF
import ZFVP.ModelTheory.SymmetricVopenkaPreservation
import ZFVP.ModelTheory.TransitiveZFSymmetry
import ZFVP.ModelTheory.UsubaForcingDerivability
import ZFVP.ModelTheory.WoodinDirectedSourceTransfer
import ZFVP.ModelTheory.WoodinEndpointInternalPresentation
import ZFVP.ModelTheory.WoodinFixedPointDirect
import ZFVP.ModelTheory.WoodinFixedPointModel
import ZFVP.ModelTheory.WoodinMarkedStageTheorem
import ZFVP.ModelTheory.WoodinSparseActualCriticalLift
import ZFVP.ModelTheory.WoodinSparseActualGenericMovement
import ZFVP.ModelTheory.WoodinSparseCodedForcingEquality
import ZFVP.ModelTheory.WoodinSparseEndpointTruth
import ZFVP.ModelTheory.WoodinSparseEndpointZFC
import ZFVP.ModelTheory.WoodinSparseLiteralRankReflection
import ZFVP.ModelTheory.WoodinSparseRestorationTheorem
import ZFVP.ModelTheory.WoodinSparseSourceTruthWindow
import ZFVP.ModelTheory.WoodinSparseStandardFormulaTruth
import ZFVP.ModelTheory.WoodinSupercompactRankZF
import ZFVP.SetTheory.CnExtendibleDownward
import ZFVP.SetTheory.EffectiveFiniteLanguageReduction
import ZFVP.SetTheory.FiniteDictionaryReflection
import ZFVP.SetTheory.FiniteDictionarySourceBounds
import ZFVP.SetTheory.LowenheimSkolemCardinals
import ZFVP.SetTheory.OrdinaryCorrectSupercompact
import ZFVP.SetTheory.PiOneRankCriterion
import ZFVP.SetTheory.PiVopenkaZFRanks
import ZFVP.SetTheory.TransitiveRestriction
import ZFVP.SetTheory.UEImpliesVopenka
import ZFVP.SetTheory.VopenkaLowenheimSkolem

#check ZFVP.SymmetricContext.vopenkaInstance
#print axioms ZFVP.SymmetricContext.vopenkaInstance
#check ZFVP.SymmetricContext.pi_vopenka_preservation
#print axioms ZFVP.SymmetricContext.pi_vopenka_preservation
#check ZFVP.SymmetricContext.modelZF
#print axioms ZFVP.SymmetricContext.modelZF
#check ZFVP.consistent_zfcVP_iff_consistent_zfVP_woodin
#print axioms ZFVP.consistent_zfcVP_iff_consistent_zfVP_woodin
#check ZFVP.transitiveRestriction
#print axioms ZFVP.transitiveRestriction
#check ZFVP.TransitiveZF.symmetricExtensionDomain_models_zf
#print axioms ZFVP.TransitiveZF.symmetricExtensionDomain_models_zf
#check ZFVP.TransitiveZF.symmetricQuotientValue_check
#print axioms ZFVP.TransitiveZF.symmetricQuotientValue_check
#check ZFVP.TransitiveZF.hereditarilySymmetricName_iff
#print axioms ZFVP.TransitiveZF.hereditarilySymmetricName_iff
#check ZFVP.exists_symmetric_lift_of_fixedClosure
#print axioms ZFVP.exists_symmetric_lift_of_fixedClosure
#check ZFVP.SymmetricLiftData.graph_agrees_ordinaryLift
#print axioms ZFVP.SymmetricLiftData.graph_agrees_ordinaryLift
#check ZFVP.IsRankCriterionHeight.models_zf
#print axioms ZFVP.IsRankCriterionHeight.models_zf
#check ZFVP.rankCriterionFormula_piOne
#print axioms ZFVP.rankCriterionFormula_piOne
#check ZFVP.pi_vopenka_rankCriterion_unbounded
#print axioms ZFVP.pi_vopenka_rankCriterion_unbounded
#check ZFVP.pi_vopenka_rankMarker_criticalPoint_above
#print axioms ZFVP.pi_vopenka_rankMarker_criticalPoint_above
#check ZFVP.limitRankEmbedding_criticalPoint_measurable
#print axioms ZFVP.limitRankEmbedding_criticalPoint_measurable
#check ZFVP.lsCardinal_of_cofinally_ls
#print axioms ZFVP.lsCardinal_of_cofinally_ls
#check ZFVP.weaklyLSCardinal_of_cofinally_weaklyLS
#print axioms ZFVP.weaklyLSCardinal_of_cofinally_weaklyLS
#check ZFVP.vopenka_lsCardinal_unbounded
#print axioms ZFVP.vopenka_lsCardinal_unbounded
#check ZFVP.vopenka_singular_lsCardinal
#print axioms ZFVP.vopenka_singular_lsCardinal
#check ZFVP.usubaForcesZFC_unrestricted
#print axioms ZFVP.usubaForcesZFC_unrestricted
#check ZFVP.zf_proves_usubaForcesZFC_of_ls
#print axioms ZFVP.zf_proves_usubaForcesZFC_of_ls
#check ZFVP.unboundedExtendibility_implies_vopenka
#print axioms ZFVP.unboundedExtendibility_implies_vopenka
#check ZFVP.IsNonzeroRankBerkeley.externalZFUEVP_model_above
#print axioms ZFVP.IsNonzeroRankBerkeley.externalZFUEVP_model_above
#check ZFVP.IsCnExtendible.of_le
#print axioms ZFVP.IsCnExtendible.of_le
#check ZFVP.exists_countable_prunedUEVP_model
#print axioms ZFVP.exists_countable_prunedUEVP_model
#check ZFVP.woodinMarkedStageConclusion
#print axioms ZFVP.woodinMarkedStageConclusion
#check ZFVP.woodinEndpointStagePresentation_sigmaThree_uniform
#print axioms ZFVP.woodinEndpointStagePresentation_sigmaThree_uniform
#check ZFVP.woodinIteration_fixedPoint_direct
#print axioms ZFVP.woodinIteration_fixedPoint_direct
#check ZFVP.WoodinEndpointModel.fixedPointRank_models_zfc
#print axioms ZFVP.WoodinEndpointModel.fixedPointRank_models_zfc
#check ZFVP.ForcingContext.woodinSparseSource_all_quotient_directedClosedBelow_zf
#print axioms ZFVP.ForcingContext.woodinSparseSource_all_quotient_directedClosedBelow_zf
#check ZFVP.woodinSparseSource_move_generic
#print axioms ZFVP.woodinSparseSource_move_generic
#check ZFVP.ForcingContext.woodinSparseSource_exists_criticalLift_actual
#print axioms ZFVP.ForcingContext.woodinSparseSource_exists_criticalLift_actual
#check ZFVP.IsWoodinSupercompact.models_zf
#print axioms ZFVP.IsWoodinSupercompact.models_zf
#check ZFVP.woodinCodedForcingFormula_rank_internal
#print axioms ZFVP.woodinCodedForcingFormula_rank_internal
#check ZFVP.woodinSparseFixedPointContext_internalGenericTruth
#print axioms ZFVP.woodinSparseFixedPointContext_internalGenericTruth
#check ZFVP.woodinSparse_fixedPoint_standardFormula_truth
#print axioms ZFVP.woodinSparse_fixedPoint_standardFormula_truth
#check ZFVP.woodinSparse_cn_source_positive_window
#print axioms ZFVP.woodinSparse_cn_source_positive_window
#check ZFVP.woodinSparseLowerRank_formula_reflection
#print axioms ZFVP.woodinSparseLowerRank_formula_reflection
#check ZFVP.finite_reflection_source
#print axioms ZFVP.finite_reflection_source
#check ZFVP.reflectionFormula_sigma
#print axioms ZFVP.reflectionFormula_sigma
#check ZFVP.IsCnExtendible.correct_add_two
#print axioms ZFVP.IsCnExtendible.correct_add_two
#check ZFVP.IsCnExtendible.woodinSupercompact_of_bound
#print axioms ZFVP.IsCnExtendible.woodinSupercompact_of_bound
#check ZFVP.prunedUE_sparseEndpoint_cnExtendible_unbounded
#print axioms ZFVP.prunedUE_sparseEndpoint_cnExtendible_unbounded
#check ZFVP.WoodinSparseEndpointModel.rankModel_models_zfc
#print axioms ZFVP.WoodinSparseEndpointModel.rankModel_models_zfc
#check ZFVP.provable_vopenkaSentence_of_effective_pi_scheme
#print axioms ZFVP.provable_vopenkaSentence_of_effective_pi_scheme
#check ZFVP.one_le_effectiveLanguageReductionLevel
#print axioms ZFVP.one_le_effectiveLanguageReductionLevel
#check ZFVP.consistent_zfVP_notChoice_notDC
#print axioms ZFVP.consistent_zfVP_notChoice_notDC
#check ZFVP.consistent_zfcVP_of_consistent_zfVP_woodin
#print axioms ZFVP.consistent_zfcVP_of_consistent_zfVP_woodin
#check ZFVP.omegaOneCohen_model_zfVP_DC_notChoice
#print axioms ZFVP.omegaOneCohen_model_zfVP_DC_notChoice
#check ZFVP.consistent_zfVP_DC_notChoice
#print axioms ZFVP.consistent_zfVP_DC_notChoice
#check ZFVP.consistent_zfVP_notRigid
#print axioms ZFVP.consistent_zfVP_notRigid
#check ZFVP.consistent_zfVP_rigid_notChoice_notDC_of_zfVP
#print axioms ZFVP.consistent_zfVP_rigid_notChoice_notDC_of_zfVP
#check ZFVP.consistent_zfVP_fefermanLevy
#print axioms ZFVP.consistent_zfVP_fefermanLevy
#check ZFVP.solovay_realRegularity
#print axioms ZFVP.solovay_realRegularity
#check ZFVP.groundRealDefinable_localized
#print axioms ZFVP.groundRealDefinable_localized
#check ZFVP.sequence_localized
#print axioms ZFVP.sequence_localized
#check ZFVP.Unconditional.solovay_corollary
#print axioms ZFVP.Unconditional.solovay_corollary
#check ZFVP.hod_solovayTrace_nonprincipalSetUltrafilter
#print axioms ZFVP.hod_solovayTrace_nonprincipalSetUltrafilter
#check ZFVP.Unconditional.solovay_symmetric_range
#print axioms ZFVP.Unconditional.solovay_symmetric_range
#check ZFVP.consistent_realSolovay_of_consistent_zfVP
#print axioms ZFVP.consistent_realSolovay_of_consistent_zfVP
#check ZFVP.models_realSolovayTheory
#print axioms ZFVP.models_realSolovayTheory
#check ZFVP.ClassForcingDensitySemantics.forcesPiVopenka_iff_denselyUnbounded_all_positive
#print axioms ZFVP.ClassForcingDensitySemantics.forcesPiVopenka_iff_denselyUnbounded_all_positive
#check ZFVP.ClassForcingDensitySemantics.denselyUnbounded_iff
#print axioms ZFVP.ClassForcingDensitySemantics.denselyUnbounded_iff
#check ZFVP.svc_collapse_restores_zfcVP
#print axioms ZFVP.svc_collapse_restores_zfcVP
#check ZFVP.exists_svc_zfcVP_generic_extension
#print axioms ZFVP.exists_svc_zfcVP_generic_extension
#check ZFVP.wellOrderable_of_forced_ordinal_surjection
#print axioms ZFVP.wellOrderable_of_forced_ordinal_surjection
#check ZFVP.ForcingContext.not_internalChoice_model
#print axioms ZFVP.ForcingContext.not_internalChoice_model
#check ZFVP.countability_essential_of_consistent
#print axioms ZFVP.countability_essential_of_consistent
#check ZFVP.countability_essential_forcing_obstruction
#print axioms ZFVP.countability_essential_forcing_obstruction

namespace ZFVP.PaperCoverageAudit
open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem pi_one_measurable_rank
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ)
    (γ : V) [IsOrdinal γ] :
    ∃ κ : V, γ ∈ κ ∧ IsRankCriterionHeight κ ∧ IsMeasurableOrdinal κ := by
  obtain ⟨δ, μ, f, κ, hδ, hμ, hf, hκ, hγκ, hωκ⟩ :=
    pi_vopenka_rankMarker_criticalPoint_above (by omega) hVP γ
  let := hδ
  let := hμ
  let := hierarchy_transitive (ordinalAdd μ ω)
  have hc : ∀ β ∈ ordinalAdd δ ω, succ β ∈ ordinalAdd δ ω :=
    fun _ ↦ ordinalAdd_omega_succ_closed δ
  exact ⟨κ, hγκ, limitRankEmbedding_criticalPoint_rankCriterion hc hf hκ hωκ,
    limitRankEmbedding_criticalPoint_measurable hc hf hκ hωκ⟩

theorem dc_notAC_from_zfVP (h : Consistent zfVPTheory) :
    Consistent zfVPDCNotChoiceTheory :=
  consistent_zfVP_DC_notChoice (consistent_zfcVP_of_consistent_zfVP_woodin h)

theorem dc_both_branches (h : Consistent zfVPTheory) :
    Consistent zfVPDCNotChoiceTheory ∧ Consistent zfVPNotChoiceNotDCTheory :=
  ⟨dc_notAC_from_zfVP h, consistent_zfVP_notChoice_notDC h⟩

theorem fefermanLevy_from_zfVP (h : Consistent zfVPTheory) :
    Consistent zfVPFefermanLevyTheory :=
  consistent_zfVP_fefermanLevy (consistent_zfcVP_of_consistent_zfVP_woodin h)

#print axioms pi_one_measurable_rank
#print axioms dc_notAC_from_zfVP
#print axioms dc_both_branches
#print axioms fefermanLevy_from_zfVP
end ZFVP.PaperCoverageAudit
