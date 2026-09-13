import ZFVP.ModelTheory.WoodinSparseCarrierRecovery
import ZFVP.ModelTheory.ForcingLowRankNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem subset_woodinSourceIndex (i : V) [IsOrdinal i] : i ⊆ woodinSourceIndex i := by
  classical
  by_cases hi : i ∈ (ω : V)
  · rw [woodinSourceIndex_natural hi]
    exact fun x hx ↦ mem_succ_iff.mpr (Or.inr hx)
  · rw [woodinSourceIndex_infinite hi]

variable {Ω θ i : V} [IsOrdinal θ] [IsOrdinal i]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "Pi" => (forcingCodeP (woodinSparseStageCode i)) ‘ i
include hΩ hAC hθ

/-- A sparse condition's ground rank bounds every coordinate recorded in it.
Actual carrier recovery therefore puts it in the corresponding prefix. -/
theorem woodinSparse_condition_mem_prefix_of_rank {p : V} (hi : i ∈ succ θ)
    (hp : p ∈ P) (hpi : p ∈ hierarchy i) : p ∈ Pi := by
  let := hierarchy_transitive i
  have hs := woodinSparseStageCode_sparse hΩ hAC hθ hp
  rw [woodinSparseStageCode_carrier_recovery hΩ hAC hθ hi, mem_sparseCarrierCut_iff]
  refine ⟨hp, ?_⟩
  intro a ha
  let := IsOrdinal.of_mem (hs.2.1 a ha)
  obtain ⟨v, hav⟩ := mem_domain_iff.mp ha
  have havV := (hierarchy_transitive i).mem_trans hav hpi
  have hai : a ∈ i := ordinal_mem_hierarchy_iff.mp (kpair_components_mem_transitive havV).1
  exact mem_succ_iff.mpr (Or.inr (subset_woodinSourceIndex i a hai))

/-- Every low sparse name is literally a name for a bounded actual prefix.
No replacement of the name or choice of name representatives is used. -/
theorem woodinSparse_name_mem_prefix_of_rank {τ : V} (hi : i ∈ succ θ)
    (hτ : IsForcingName P τ) (hτi : τ ∈ hierarchy i) : IsForcingName Pi τ := by
  let := hierarchy_transitive i
  have hc := nameClosure_minimal (transitive_subnameClosed (hierarchy_transitive i)) hτi
  intro σ hσ z hz
  obtain ⟨u, p, hp, he⟩ := hτ σ hσ z hz
  have hzi : z ∈ hierarchy i := (hierarchy_transitive i).mem_trans hz (hc σ hσ)
  have hpi : p ∈ hierarchy i := (kpair_components_mem_transitive (he ▸ hzi)).2
  exact ⟨u, p, woodinSparse_condition_mem_prefix_of_rank hΩ hAC hθ hi hp hpi, he⟩

omit [IsOrdinal i] in
theorem woodinSparse_lowName_bounded_prefix {τ : V}
    (hlim : ∀ α ∈ θ, succ α ∈ θ)
    (hτ : IsForcingName P τ) (hτθ : τ ∈ hierarchy θ) :
    ∃ i ∈ θ, IsForcingName ((forcingCodeP (woodinSparseStageCode i)) ‘ i) τ := by
  have hi := hlim (rank τ) ((mem_hierarchy_iff_rank_mem τ θ).mp hτθ)
  exact ⟨succ (rank τ), hi,
    woodinSparse_name_mem_prefix_of_rank hΩ hAC hθ (mem_succ_iff.mpr (Or.inr hi)) hτ
      ((mem_hierarchy_iff_rank_mem τ (succ (rank τ))).mpr (mem_succ_self (rank τ)))⟩

end ZFVP
