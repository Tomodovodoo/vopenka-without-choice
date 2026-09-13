import ZFVP.ModelTheory.WoodinSparseCodedForcingFormula

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedForcingArguments (one n φ s : V) : V :=
  standardTuple ![checkName one n, checkName one φ, sequenceName one s]

instance codedForcingArguments_definable : ℒₛₑₜ-function₄[V] codedForcingArguments := by
  unfold codedForcingArguments
  definability

/-- The actual rank forcing relation for a fixed signed formula code. -/
noncomputable def sparseCodedForcingSet (P R δ : V) (k : ℕ) (pol : LevyPolarity) (n φ s : V) : V :=
  classForcingFormula P R (IsLowRankForcingName P δ) (by definability)
    (domainTruthFormula pol k) (codedForcingArguments ∅ n φ s)

theorem TransitiveZF.woodinForcingCode_val (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (pol : LevyPolarity) (n φ : SetDomain U) :
    (woodinForcingCode pol n φ).val = woodinForcingCode pol n.val φ.val := by
  cases pol <;> simp only [woodinForcingCode, TransitiveZF.kpair_val,
    TransitiveZF.empty_val, TransitiveZF.succ_val]

theorem woodinCodedForcingFormula_rank {Ω : V} (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) (k : ℕ) (pol : LevyPolarity) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ p n φ s : SetDomain (hierarchy Ω),
      ∀ _ : IsNameSequence ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) s.val,
      (woodinCodedForcingFormula k).Evalb ![p, woodinForcingCode pol n φ, s] ↔
        p.val ∈ sparseCodedForcingSet
          ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
          ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω) Ω k pol n.val φ.val s.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro p n φ s hs
  rw [eval_woodinCodedForcingFormula]
  let v : Fin 3 → SetDomain (hierarchy Ω) := ![checkName ∅ n, checkName ∅ φ, sequenceName ∅ s]
  have hzero : (∅ : V) ∈ (forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω := by
    have ht := (woodinSparseStageCode_valid hΩ hAC (subset_refl Ω)).system.tops.top Ω (mem_succ_self Ω)
    rw [woodinSparseStageCode_top hΩ hAC (subset_refl Ω)] at ht
    exact ht.1
  have hvs : (fun i ↦ (v i).val) = ![checkName ∅ n.val, checkName ∅ φ.val, sequenceName ∅ s.val] := by
    funext i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) i) i) i
    · change (checkName (∅ : SetDomain (hierarchy Ω)) n).val = _
      rw [TransitiveZF.checkName_val, TransitiveZF.empty_val]
      rfl
    · change (checkName (∅ : SetDomain (hierarchy Ω)) φ).val = _
      rw [TransitiveZF.checkName_val, TransitiveZF.empty_val]
      rfl
    · change (sequenceName (∅ : SetDomain (hierarchy Ω)) s).val = _
      rw [TransitiveZF.sequenceName_val, TransitiveZF.empty_val]
      rfl
  have hv : ∀ i, IsForcingName ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) (v i).val := by
    intro i
    rw [show (v i).val = ![checkName ∅ n.val, checkName ∅ φ.val, sequenceName ∅ s.val] i from congrFun hvs i]
    exact Fin.cases (checkName_isName hzero n.val)
      (fun i ↦ Fin.cases (checkName_isName hzero φ.val)
        (fun i ↦ Fin.cases (sequenceName_isName hzero hs) (fun j ↦ Fin.elim0 j) i) i) i
  have hh := woodinSparseForcingTranslation_rank hΩ hAC (domainTruthFormula pol k) v hv p
  rw [hvs] at hh
  exact hh

end ZFVP
