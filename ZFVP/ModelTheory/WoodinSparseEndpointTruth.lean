import ZFVP.ModelTheory.WoodinSparseLowNames
import ZFVP.ModelTheory.InternalGenericTruth
import ZFVP.ModelTheory.DefinableClassGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- Low-name coverage suffices to identify the evaluation range even when the
whole forcing does not belong to the ground rank. -/
theorem lowRankEvaluation_range_of_coverage (A : ForcingContext V) {δ : V}
    [IsOrdinal δ]
    (hcov : ∀ x ∈ hierarchy (A.check δ), ∃ τ : ForcingName A.P,
      τ.val ∈ hierarchy δ ∧ x = A.ofName τ) :
    range (A.evaluationGraph (lowRankNameSet A.P δ) (A.lowRankNameSet_names δ)) =
      hierarchy (A.check δ) := by
  apply mem_ext
  intro x
  rw [A.mem_range_evaluationGraph_iff]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact A.ofName_mem_checked_hierarchy _ ((mem_lowRankNameSet A.P δ τ).mp hτ).1
  · intro hx
    obtain ⟨τ, hτ, rfl⟩ := hcov x hx
    exact ⟨τ.val, (mem_lowRankNameSet A.P δ τ.val).mpr ⟨hτ, τ.property⟩, rfl⟩

theorem lowRank_internalGenericTruth_of_coverage (A : ForcingContext V) {δ : V}
    [IsOrdinal δ]
    (hcov : ∀ x ∈ hierarchy (A.check δ), ∃ τ : ForcingName A.P,
      τ.val ∈ hierarchy δ ∧ x = A.ofName τ)
    {n φ b : V} (hφ : IsMembershipFormulaCode n φ)
    (hb : b ∈ lowRankNameSet A.P δ ^ n) :
    MembershipSatisfies (hierarchy (A.check δ)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb)) ↔
        GenericMeets A.G (internalForcingSet A.P A.R (lowRankNameSet A.P δ) n φ b) := by
  have h := A.groundGenericTruth (lowRankNameSet A.P δ) (A.lowRankNameSet_names δ) hφ b hb
  rwa [A.lowRankEvaluation_range_of_coverage hcov] at h

theorem lowRankFiniteAssignment_representative_of_coverage (A : ForcingContext V)
    {δ n : V} [IsOrdinal δ]
    (hcov : ∀ x ∈ hierarchy (A.check δ), ∃ τ : ForcingName A.P,
      τ.val ∈ hierarchy δ ∧ x = A.ofName τ)
    (hn : n ∈ (ω : V)) {b : A.Model}
    (hb : b ∈ hierarchy (A.check δ) ^ A.check n) :
    ∃ s : V, ∃ hsN : IsNameSequence A.P s,
      s ∈ lowRankNameSet A.P δ ^ n ∧ A.sequenceValue s hsN = b := by
  rw [← A.lowRankEvaluation_range_of_coverage hcov] at hb
  exact A.finite_sequenceValue_surjective _ (A.lowRankNameSet_names δ) hn hb

end ForcingContext

variable {Ω : V} [IsOrdinal Ω]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)

local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG

theorem woodinSparseGenericContext_endpoint_evaluation_range :
    range ((E).evaluationGraph (lowRankNameSet (E).P Ω) ((E).lowRankNameSet_names Ω)) =
      hierarchy ((E).check Ω) :=
  (E).lowRankEvaluation_range_of_coverage
    (woodinSparseGenericContext_endpoint_low_name_coverage hΩ hAC hG)

theorem woodinSparseGenericContext_endpoint_definableClasses :
    IsGenericForDefinableDenseClasses
      (fun p : SetDomain (hierarchy Ω) ↦ p.val ∈ (E).P)
      (fun p q ↦ ⟨p.val, q.val⟩ₖ ∈ (E).R)
      {p : SetDomain (hierarchy Ω) | p.val ∈ (E).G} :=
  externalForcingGeneric_definableClasses
    (show (E).P ⊆ hierarchy Ω from
      woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC Ω (mem_succ_self Ω))
    (E).generic

/-- Internal-code truth at the actual sparse endpoint. The only generic is the
given generic of the constructed iteration; low-name coverage is derived. -/
theorem woodinSparseGenericContext_endpoint_internalGenericTruth
    {n φ b : V} (hφ : IsMembershipFormulaCode n φ)
    (hb : b ∈ lowRankNameSet (E).P Ω ^ n) :
    MembershipSatisfies (hierarchy ((E).check Ω)) ((E).check n) ((E).check φ)
      ((E).sequenceValue b ((E).nameSequence_of_mem_function ((E).lowRankNameSet_names Ω) hb)) ↔
        GenericMeets (E).G (internalForcingSet (E).P (E).R (lowRankNameSet (E).P Ω) n φ b) :=
  (E).lowRank_internalGenericTruth_of_coverage
    (woodinSparseGenericContext_endpoint_low_name_coverage hΩ hAC hG) hφ hb

variable {γ : V} [IsOrdinal γ] (hγ : γ ∈ Ω)
local notation "B" => woodinSparseFixedPointContext hΩ hAC hG hγ

theorem woodinSparseFixedPointContext_evaluation_range
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    range ((B).evaluationGraph (lowRankNameSet (B).P γ) ((B).lowRankNameSet_names γ)) =
      hierarchy ((B).check γ) :=
  (B).lowRankEvaluation_range_of_coverage
    (woodinSparseFixedPointContext_low_name_coverage hΩ hAC hG hγ hfix)

theorem woodinSparseFixedPointContext_definableClasses
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    IsGenericForDefinableDenseClasses
      (fun p : SetDomain (hierarchy γ) ↦ p.val ∈ (B).P)
      (fun p q ↦ ⟨p.val, q.val⟩ₖ ∈ (B).R)
      {p : SetDomain (hierarchy γ) | p.val ∈ (B).G} :=
  externalForcingGeneric_definableClasses
    (show (B).P ⊆ hierarchy γ from
      woodinSparseStageCode_rows_subset_at_fixedPoint hΩ hAC hγ hfix γ (mem_succ_self γ))
    (B).generic

/-- The same internal-code truth theorem at a marked stage below the endpoint. -/
theorem woodinSparseFixedPointContext_internalGenericTruth
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ)
    {n φ b : V} (hφ : IsMembershipFormulaCode n φ)
    (hb : b ∈ lowRankNameSet (B).P γ ^ n) :
    MembershipSatisfies (hierarchy ((B).check γ)) ((B).check n) ((B).check φ)
      ((B).sequenceValue b ((B).nameSequence_of_mem_function ((B).lowRankNameSet_names γ) hb)) ↔
        GenericMeets (B).G (internalForcingSet (B).P (B).R (lowRankNameSet (B).P γ) n φ b) :=
  (B).lowRank_internalGenericTruth_of_coverage
    (woodinSparseFixedPointContext_low_name_coverage hΩ hAC hG hγ hfix) hφ hb

end ZFVP
