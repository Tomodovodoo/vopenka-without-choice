import ZFVP.ModelTheory.WoodinSparseLowNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω : V} [IsOrdinal Ω]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)

local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG

theorem woodinSparseGenericContext_endpoint_rank : rank (E).P = Ω := by
  change rank ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) = Ω
  rw [woodinSparseStageCode_rank_eq hΩ hAC (subset_refl Ω), woodinIteration_endpoint_cardinal hΩ hAC]

theorem woodinSparseGenericContext_endpoint_rank_low_name_coverage :
    ∀ x ∈ hierarchy ((E).check (rank (E).P)), ∃ τ : ForcingName (E).P,
      τ.val ∈ hierarchy (rank (E).P) ∧ x = (E).ofName τ := by
  rw [woodinSparseGenericContext_endpoint_rank hΩ hAC hG]
  exact woodinSparseGenericContext_endpoint_low_name_coverage hΩ hAC hG

theorem woodinSparseGenericContext_endpoint_successor_name_coverage (x : (E).Model) :
    x ∈ hierarchy (succ ((E).check (rank (E).P))) ↔ ∃ τ : ForcingName (E).P,
      τ.val ∈ successorLowNameSet (E).P (rank (E).P) ∧ x = (E).ofName τ :=
  (E).successor_low_name_coverage (woodinSparseGenericContext_endpoint_rank_low_name_coverage hΩ hAC hG) x

variable {γ : V} [IsOrdinal γ] (hγ : γ ∈ Ω)
local notation "B" => woodinSparseFixedPointContext hΩ hAC hG hγ

theorem woodinSparseFixedPointContext_rank
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) : rank (B).P = γ := by
  change rank ((forcingCodeP (woodinSparseStageCode γ)) ‘ γ) = γ
  rw [woodinSparseStageCode_rank_eq hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ),
    woodinIteration_fixedPoint_cardinal hΩ hAC hγ hfix]

theorem woodinSparseFixedPointContext_rank_low_name_coverage
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    ∀ x ∈ hierarchy ((B).check (rank (B).P)), ∃ τ : ForcingName (B).P,
      τ.val ∈ hierarchy (rank (B).P) ∧ x = (B).ofName τ := by
  rw [woodinSparseFixedPointContext_rank hΩ hAC hG hγ hfix]
  exact woodinSparseFixedPointContext_low_name_coverage hΩ hAC hG hγ hfix

theorem woodinSparseFixedPointContext_successor_name_coverage
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) (x : (B).Model) :
    x ∈ hierarchy (succ ((B).check (rank (B).P))) ↔ ∃ τ : ForcingName (B).P,
      τ.val ∈ successorLowNameSet (B).P (rank (B).P) ∧ x = (B).ofName τ :=
  (B).successor_low_name_coverage (woodinSparseFixedPointContext_rank_low_name_coverage hΩ hAC hG hγ hfix) x

end ZFVP
