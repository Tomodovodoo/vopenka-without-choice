import ZFVP.ModelTheory.WoodinSparseLiteralRankReflection
import ZFVP.ModelTheory.WoodinSparseUniformRestoration
import ZFVP.ModelTheory.DomainTruthCorrectnessCriterion
import ZFVP.ModelTheory.WoodinSparseRestrictedLiftRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- One fixed finite dictionary handles all internally coded Σ_(k+1) formulas. -/
def woodinSparseSatDictionary (k : ℕ) : SetFormulaDictionary :=
  [⟨4, woodinSparseForcingTranslation (domainTruthFormula .sigma k)⟩,
   ⟨4, woodinSparseForcingTranslation (∼domainTruthFormula .sigma k)⟩]

def woodinSparseSatLevel (k : ℕ) : ℕ := levyDictionaryBound (woodinSparseSatDictionary k) + 1

theorem woodinSparseSatLevel_positive (k : ℕ) : 0 < woodinSparseSatLevel k := Nat.zero_lt_succ _

theorem woodinSparseSatTranslation_complexity (k : ℕ) :
    IsSigmaFormula (woodinSparseSatLevel k) (woodinSparseForcingTranslation (domainTruthFormula .sigma k)) ∧
    IsSigmaFormula (woodinSparseSatLevel k) (woodinSparseForcingTranslation (∼domainTruthFormula .sigma k)) := by
  constructor
  · exact (isLevyFormula_dictionaryBound (woodinSparseSatDictionary k)
      (by simp [woodinSparseSatDictionary]) .sigma).mono (Nat.le_succ _)
  · exact (isLevyFormula_dictionaryBound (woodinSparseSatDictionary k)
      (by simp [woodinSparseSatDictionary]) .sigma).mono (Nat.le_succ _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal Ω] [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hθ : IsWoodinSupercompact θ) (hAC : ¬InternalChoice V)
  {G : Set V} (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G) (hθΩ : θ ∈ Ω)
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG
include hθ hθΩ

/-- Actual finite restoration of C(n) in the endpoint rank. The forcing window
is computed from the explicit sparse class-forcing translation of Sat_k. -/
theorem woodinSparse_cn_window (k : ℕ)
    (hΩC : Cn (woodinSparseSatLevel k) Ω) (hθC : Cn (woodinSparseSatLevel k) θ) :
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
      (domainTruthFormula .sigma k) (woodinSparseSatTranslation_complexity k).1
      (woodinSparseSatTranslation_complexity k).2)
  exact (TransitiveZF.cn_iff_relative (hierarchy ((E).check Ω)) k
    (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hθΩ) (show IsOrdinal ((E).check θ) from inferInstance) hsub).mpr hrel

end ZFVP
