import ZFVP.ModelTheory.WoodinSparseForcingReflection
import ZFVP.ModelTheory.WoodinSparseFixedPointInclusion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem genericMeets_classFormula_neg (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (hnames : ∀ x, N x → IsForcingName P x) {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → V) (hv : ∀ i, N (v i)) :
    GenericMeets G (classForcingFormula P R N hN (∼φ) (standardTuple v)) ↔
      ¬GenericMeets G (classForcingFormula P R N hN φ (standardTuple v)) := by
  let w : Fin n → {x : V // N x} := fun i ↦ ⟨v i, hv i⟩
  have ha := ClassForcingQuotient.formula_truth P R G hR hG N hN hnames φ w
  have hb := ClassForcingQuotient.formula_truth P R G hR hG N hN hnames (∼φ) w
  exact hb.symm.trans ((by simp : (∼φ).Evalb _ ↔ ¬φ.Evalb _).trans (not_congr ha))

variable {Ω θ : V} [IsOrdinal Ω] [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hθ : IsWoodinSupercompact θ) (hAC : ¬InternalChoice V)
  {G : Set V} (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G) (hθΩ : θ ∈ Ω)
local notation "A" => woodinSparseFixedPointContext hΩ hAC hG hθΩ
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG

include hθ
/-- Reflected positive and negative translations suffice for two-way transfer
of generic truth; no endpoint witness is assumed to be an earlier condition. -/
theorem woodinSparse_genericMeets_reflection {k n : ℕ}
    (hΩC : Cn (k + 1) Ω) (hθC : Cn (k + 1) θ) (φ : SetTheorySemisentence n)
    (hφ : IsSigmaFormula (k + 1) (woodinSparseForcingTranslation φ))
    (hneg : IsSigmaFormula (k + 1) (woodinSparseForcingTranslation (∼φ)))
    (v : Fin n → SetDomain (hierarchy θ)) (hv : ∀ i, IsForcingName (A).P (v i).val) :
    GenericMeets (A).G (classForcingFormula (A).P (A).R
      (IsLowRankForcingName (A).P θ) (lowRankForcingName_definable _ _) φ (standardTuple (fun i ↦ (v i).val))) ↔
    GenericMeets (E).G (classForcingFormula (E).P (E).R
      (IsLowRankForcingName (E).P Ω) (lowRankForcingName_definable _ _) φ (standardTuple (fun i ↦ (v i).val))) := by
  have hsub := woodinSparse_prefix_carrier_subset hΩ hAC hθΩ
  have hvA : ∀ i, IsLowRankForcingName (A).P θ (v i).val := fun i ↦ ⟨(v i).property, hv i⟩
  have hvE : ∀ i, IsLowRankForcingName (E).P Ω (v i).val := fun i ↦
    ⟨hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hθΩ) _ (v i).property, (hv i).mono hsub⟩
  have forward (ψ : SetTheorySemisentence n)
      (hψ : IsSigmaFormula (k + 1) (woodinSparseForcingTranslation ψ)) :
      GenericMeets (A).G (classForcingFormula (A).P (A).R
        (IsLowRankForcingName (A).P θ) (lowRankForcingName_definable _ _) ψ (standardTuple (fun i ↦ (v i).val))) →
      GenericMeets (E).G (classForcingFormula (E).P (E).R
        (IsLowRankForcingName (E).P Ω) (lowRankForcingName_definable _ _) ψ (standardTuple (fun i ↦ (v i).val))) := by
    rintro ⟨p, hpG, hpF⟩
    have hpP := (A).generic.1.1 p hpG
    have hpθ := woodinSparseStageCode_rows_subset_at_endpoint hθ hAC θ (mem_succ_self θ) p hpP
    refine ⟨p, ((woodinSparseFixedPointContext_generic_iff hΩ hAC hG hθΩ p).mp hpG).1, ?_⟩
    exact (woodinSparseForcing_rank_compare hΩ hθ hAC hθΩ hΩC hθC ψ hψ v hv ⟨p, hpθ⟩).mp hpF
  constructor
  · exact forward φ hφ
  · intro he
    by_contra ha
    have hna := (genericMeets_classFormula_neg (A).P (A).R (A).G (A).order (A).generic
      (IsLowRankForcingName (A).P θ) (lowRankForcingName_definable _ _) (fun _ h ↦ h.2) φ _ hvA).mpr ha
    have hne := forward (∼φ) hneg hna
    exact (genericMeets_classFormula_neg (E).P (E).R (E).G (E).order (E).generic
      (IsLowRankForcingName (E).P Ω) (lowRankForcingName_definable _ _) (fun _ h ↦ h.2) φ _ hvE).mp hne he

end ZFVP


