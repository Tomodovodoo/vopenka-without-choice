import ZFVP.ModelTheory.WoodinSparseBoundedForcing
import ZFVP.ModelTheory.WoodinSparseBoundedNamePrefix
import ZFVP.ModelTheory.WoodinSparseMarkedRank
import ZFVP.SetTheory.InaccessibleFunctionClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Bounded forcing expressed using only strictly earlier sparse prefixes and
strictly lower name-rank bounds. The endpoint poset is not supplied as a set. -/
def WoodinSparseBoundedPrefixForces (Ω n φ b p : V) : Prop :=
  ∃ i ∈ Ω, ∃ η ∈ Ω, (∅ : V) ∈ η ∧
    let P := (forcingCodeP (woodinSparseStageCode i)) ‘ i;
    let R := (forcingCodeR (woodinSparseStageCode i)) ‘ i;
    b ∈ lowRankNameSet P η ^ n ∧ p ∈ P ∧
      p ∈ internalForcingSet P R (lowRankNameSet P η) n φ b

variable {Ω : V} [IsOrdinal Ω]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
local notation "C" => woodinSparseStageCode Ω
local notation "P" => (forcingCodeP C) ‘ Ω
local notation "R" => (forcingCodeR C) ‘ Ω
include hΩ hAC

omit hAC in
theorem woodinSparse_endpoint_assignment_mem_rank {n b : V} (hn : n ∈ (ω : V))
    (hb : b ∈ lowRankNameSet P Ω ^ n) : b ∈ hierarchy Ω := by
  let := IsOrdinal.of_mem hn
  have hnΩ := IsOrdinal.toIsTransitive.mem_trans hn hΩ.inaccessible.2.1
  exact hΩ.inaccessible.function_mem (ordinal_mem_hierarchy_iff.mpr hnΩ)
    (mem_function_of_mem_function_of_subset hb (lowRankNameSet_subset P Ω))

/-- One actual earlier stage simultaneously contains a condition and the names
of any internally finite endpoint assignment. -/
theorem woodinSparse_endpoint_assignment_bounded_prefix {n b p : V}
    (hn : n ∈ (ω : V)) (hb : b ∈ lowRankNameSet P Ω ^ n) (hp : p ∈ P) :
    ∃ i ∈ Ω, (∅ : V) ∈ i ∧
      b ∈ lowRankNameSet ((forcingCodeP (woodinSparseStageCode i)) ‘ i) i ^ n ∧
      p ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i := by
  have hs := hΩ.inaccessible.rankCriterion.2.2.1
  have hbΩ := woodinSparse_endpoint_assignment_mem_rank hΩ hn hb
  have hpΩ := woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC Ω (mem_succ_self Ω) p hp
  obtain ⟨α, hα, hpα, hbα⟩ := common_hierarchy_stage hs hpΩ hbΩ
  let := IsOrdinal.of_mem hα
  let i := succ α
  have hi : i ∈ Ω := hs α hα
  let := hierarchy_transitive i
  have hαi : α ⊆ i := fun x hx ↦ mem_succ_iff.mpr (Or.inr hx)
  have hpi : p ∈ hierarchy i := hierarchy_mono hαi p hpα
  have hbi : b ∈ hierarchy i := hierarchy_mono hαi b hbα
  have h0 : (∅ : V) ∈ i := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset α))
  have hi' : i ∈ succ Ω := mem_succ_iff.mpr (Or.inr hi)
  let := IsFunction.of_mem hb
  have hbr : range b ⊆ lowRankNameSet ((forcingCodeP (woodinSparseStageCode i)) ‘ i) i := by
    intro τ hτ
    obtain ⟨a, haτ⟩ := mem_range_iff.mp hτ
    have hτi := (kpair_components_mem_transitive
      ((hierarchy_transitive i).mem_trans haτ hbi)).2
    have hτP := ((mem_lowRankNameSet P Ω τ).mp (range_subset_of_mem_function hb τ hτ)).2
    exact (mem_lowRankNameSet _ i τ).mpr ⟨hτi,
      woodinSparse_name_mem_prefix_of_rank hΩ hAC (subset_refl Ω) hi' hτP hτi⟩
  refine ⟨i, hi, h0, ?_,
    woodinSparse_condition_mem_prefix_of_rank hΩ hAC (subset_refl Ω) hi' hp hpi⟩
  have hf := mem_function_of_mem_function_of_subset (IsFunction.mem_function b) hbr
  rwa [domain_eq_of_mem_function hb] at hf

/-- The bounded-prefix definition computes the actual endpoint forcing set.
All earlier stages, name pools, and their forcing agreement are constructed. -/
theorem woodinSparse_boundedPrefixForces_iff {n φ b p : V}
    (hφ : IsBoundedFormulaCode n φ) (hb : b ∈ lowRankNameSet P Ω ^ n) (hp : p ∈ P) :
    WoodinSparseBoundedPrefixForces Ω n φ b p ↔
      p ∈ internalForcingSet P R (lowRankNameSet P Ω) n φ b := by
  have h0 : (∅ : V) ∈ Ω := IsOrdinal.toIsTransitive.mem_trans
    (show (∅ : V) ∈ (ω : V) from by simp) hΩ.inaccessible.2.1
  constructor
  · rintro ⟨i, hi, η, hη, hη0, hbi, hpi, hf⟩
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hη
    have hi' : i ∈ succ Ω := mem_succ_iff.mpr (Or.inr hi)
    have he := woodinSparse_boundedForcing_prefix_iff hΩ hAC (subset_refl Ω) hi
      (n := n) (φ := φ) (b := b) (p := p)
      (D0 := lowRankNameSet ((forcingCodeP (woodinSparseStageCode i)) ‘ i) η)
      (D1 := lowRankNameSet P Ω)
    rw [(woodinSparseStage_old_row hi').1, (woodinSparseStage_old_row hi').2] at he
    exact (he (lowRankNameSet_subnameClosedForcingPool _ hη0)
      (lowRankNameSet_subnameClosedForcingPool _ h0) hφ hbi hb hpi).mp hf
  · intro hf
    have hc : IsMembershipFormulaCode n φ := boundedFormulaFamily_subset _ hφ
    obtain ⟨i, hi, hi0, hbi, hpi⟩ := woodinSparse_endpoint_assignment_bounded_prefix
      hΩ hAC hc.context hb hp
    let := IsOrdinal.of_mem hi
    have hi' : i ∈ succ Ω := mem_succ_iff.mpr (Or.inr hi)
    have he := woodinSparse_boundedForcing_prefix_iff hΩ hAC (subset_refl Ω) hi
      (n := n) (φ := φ) (b := b) (p := p)
      (D0 := lowRankNameSet ((forcingCodeP (woodinSparseStageCode i)) ‘ i) i)
      (D1 := lowRankNameSet P Ω)
    rw [(woodinSparseStage_old_row hi').1, (woodinSparseStage_old_row hi').2] at he
    exact ⟨i, hi, i, hi, hi0, hbi, hpi,
      (he (lowRankNameSet_subnameClosedForcingPool _ hi0)
        (lowRankNameSet_subnameClosedForcingPool _ h0) hφ hbi hb hpi).mpr hf⟩

end ZFVP
