import ZFVP.ModelTheory.WoodinSparseFiniteTruthWindow
import ZFVP.ModelTheory.UniformWoodinSparseCompleteCode
import ZFVP.SetTheory.SourceQuantifierBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
set_option maxHeartbeats 800000

/-- The fixed presentation dictionary D_W. These are membership-language graph
formulas, not new predicate symbols: notation substitutes their full ASTs. -/
def woodinSourcePresentationDictionary : SetFormulaDictionary :=
  woodinNormalizationDictionary ++ woodinSparseSuccessorDictionary ++
  woodinSparseLimitsDictionary ++ woodinSparseMapsDictionary ++
  woodinSparseRecursionDictionary ++ totalWoodinSourceDictionary ++
  woodinSparseCompleteCodeDictionary ++
  [⟨1, woodinSparseClassCarrierFormula⟩, ⟨2, woodinSparseClassOrderFormula⟩,
   ⟨1, woodinSparseClassNameFormula⟩, ⟨4, woodinSparseLocalForcingFormula⟩]

/-- The fixed W05 formula with both polarities. Its code parameter includes a
polarity tag: equality with p selects Sat, inequality selects its negation.
All D_W graph predicates have already been eliminated by formula substitution.
Here k indexes Sigma_(k+1), so this is the source's vartheta_(k+1). -/
def woodinSourceSatFormula (k : ℕ) : SetTheorySemisentence 5 :=
  ((“#0 = #1” : SetTheorySemisentence 5).and
    ((woodinSparseForcingTranslation (domainTruthFormula .sigma k)).subst
      ![.bvar 1, .bvar 2, .bvar 3, .bvar 4])).or
  ((“#0 ≠ #1” : SetTheorySemisentence 5).and
    ((woodinSparseForcingTranslation (∼domainTruthFormula .sigma k)).subst
      ![.bvar 1, .bvar 2, .bvar 3, .bvar 4]))

/-- Exactly 2+max ell over the expanded singleton's subformulas and negations,
with ell=q+1 and q the total quantifier-occurrence count. -/
def woodinSourceSatLevel (k : ℕ) : ℕ := sourceQuantifierCount (woodinSourceSatFormula k) + 3

/-- The paper's positive indexing: r_k, used only when 0<k. -/
def woodinSourceWindowLevel (k : ℕ) : ℕ := woodinSourceSatLevel (k - 1)

theorem woodinSourceSatLevel_literal (k : ℕ) :
    woodinSourceSatLevel k = sourceSingletonBound (woodinSourceSatFormula k) :=
  (sourceSingletonBound_eq _).symm

theorem woodinSourceSatLevel_eq (k : ℕ) : woodinSourceSatLevel k =
    sourceQuantifierCount (woodinSparseForcingTranslation (domainTruthFormula .sigma k)) +
    sourceQuantifierCount (woodinSparseForcingTranslation (∼domainTruthFormula .sigma k)) + 3 := by
  change sourceQuantifierCount ((“#0 = #1” : SetTheorySemisentence 5).and _) +
    sourceQuantifierCount ((“#0 ≠ #1” : SetTheorySemisentence 5).and _) + 3 = _
  have ha : sourceQuantifierCount (“#0 = #1” : SetTheorySemisentence 5) = 0 := rfl
  simp only [sourceQuantifierCount, sourceQuantifierCount_rew, sourceQuantifierCount_neg, ha, Nat.zero_add]

theorem woodinSourceSatTranslation_complexity (k : ℕ) :
    IsSigmaFormula (woodinSourceSatLevel k)
      (woodinSparseForcingTranslation (domainTruthFormula .sigma k)) ∧
    IsSigmaFormula (woodinSourceSatLevel k)
      (woodinSparseForcingTranslation (∼domainTruthFormula .sigma k)) := by
  constructor
  · exact (isLevyFormula_sourceQuantifierCount _ .sigma).mono (by rw [woodinSourceSatLevel_eq]; omega)
  · exact (isLevyFormula_sourceQuantifierCount _ .sigma).mono (by rw [woodinSourceSatLevel_eq]; omega)

theorem eval_woodinSourceSatFormula {M : Type*} [SetStructure M] (k : ℕ) (tag p n e b : M) :
    (woodinSourceSatFormula k).Evalb ![tag, p, n, e, b] ↔
      (tag = p ∧ (woodinSparseForcingTranslation (domainTruthFormula .sigma k)).Evalb ![p,n,e,b]) ∨
      (tag ≠ p ∧ (woodinSparseForcingTranslation (∼domainTruthFormula .sigma k)).Evalb ![p,n,e,b]) := by
  have hand {n} (φ ψ : SetTheorySemisentence n) (v : Fin n → M) :
      (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl
  have hor {n} (φ ψ : SetTheorySemisentence n) (v : Fin n → M) :
      (φ.or ψ).Evalb v ↔ φ.Evalb v ∨ ψ.Evalb v := Iff.rfl
  have hv : (fun i : Fin 4 ↦ Semiterm.val ![tag,p,n,e,b] Empty.elim
      ((![.bvar 1, .bvar 2, .bvar 3, .bvar 4] : Fin 4 → SetTheorySemiterm Empty 5) i)) =
      ![p,n,e,b] := by funext i; fin_cases i <;> rfl
  simp [woodinSourceSatFormula, hand, hor, Semiformula.eval_substs, Function.comp_def, hv]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The fixed source formula actually reads the two endpoint forcing relations;
its dictionary and its bound are attached to this formula, not to an arbitrary
larger estimate. -/
theorem woodinSourceSatFormula_rank {Ω : V} (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) (k : ℕ) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ (tag p : SetDomain (hierarchy Ω)) (v : Fin 3 → SetDomain (hierarchy Ω)),
      ∀ _ : (∀ i, IsForcingName ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) (v i).val),
      (woodinSourceSatFormula k).Evalb (tag :> p :> v) ↔
        (tag = p ∧ p.val ∈ classForcingFormula
          ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
          ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω)
          (fun x ↦ x ∈ hierarchy Ω ∧ IsForcingName ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) x)
          (by definability) (domainTruthFormula .sigma k) (standardTuple (fun i ↦ (v i).val))) ∨
        (tag ≠ p ∧ p.val ∈ classForcingFormula
          ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
          ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω)
          (fun x ↦ x ∈ hierarchy Ω ∧ IsForcingName ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) x)
          (by definability) (∼domainTruthFormula .sigma k) (standardTuple (fun i ↦ (v i).val))) := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  intro tag p v hv
  have he := eval_woodinSourceSatFormula k tag p (v 0) (v 1) (v 2)
  have hvec : ![v 0, v 1, v 2] = v := by funext i; fin_cases i <;> rfl
  change (woodinSourceSatFormula k).Evalb (tag :> p :> ![v 0,v 1,v 2]) ↔
    (tag = p ∧ (woodinSparseForcingTranslation (domainTruthFormula .sigma k)).Evalb
      (p :> ![v 0,v 1,v 2])) ∨
    (tag ≠ p ∧ (woodinSparseForcingTranslation (∼domainTruthFormula .sigma k)).Evalb
      (p :> ![v 0,v 1,v 2])) at he
  rw [hvec] at he
  exact he.trans (or_congr
    (and_congr_right fun _ ↦ woodinSparseForcingTranslation_rank hΩ hAC _ v hv p)
    (and_congr_right fun _ ↦ woodinSparseForcingTranslation_rank hΩ hAC _ v hv p))

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
theorem woodinSparse_cn_source_window (k : ℕ)
    (hΩC : Cn (woodinSourceSatLevel k) Ω) (hθC : Cn (woodinSourceSatLevel k) θ) :
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
      (domainTruthFormula .sigma k) (woodinSourceSatTranslation_complexity k).1
      (woodinSourceSatTranslation_complexity k).2)
  exact (TransitiveZF.cn_iff_relative (hierarchy ((E).check Ω)) k
    (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hθΩ)
    (show IsOrdinal ((E).check θ) from inferInstance) hsub).mpr hrel

theorem woodinSparse_cn_source_positive_window (k : ℕ) (hk : 0 < k)
    (hΩC : Cn (woodinSourceWindowLevel k) Ω) (hθC : Cn (woodinSourceWindowLevel k) θ) :
    Cn k (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hθΩ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact woodinSparse_cn_source_window hΩ hθ hAC hG hθΩ j hΩC hθC

end ZFVP
