import ZFVP.ModelTheory.BoundedForcingPrefixTransfer
import ZFVP.ModelTheory.WoodinSparseCodeCompatibility
import ZFVP.ModelTheory.SuccessorLowNameFamily

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem lowRankNameSet_subnameClosedForcingPool (P : V) {η : V} [IsOrdinal η]
    (hη : (∅ : V) ∈ η) : IsSubnameClosedForcingPool P (lowRankNameSet P η) := by
  refine ⟨fun τ hτ ↦ ((mem_lowRankNameSet P η τ).mp hτ).2, ?_, ?_⟩
  · exact ⟨∅, (mem_lowRankNameSet P η ∅).mpr
      ⟨ordinal_mem_hierarchy_iff.mpr hη, empty_forcingName P⟩⟩
  · intro τ hτ u p hup
    exact lowRankNameSet_subnameClosed P η τ hτ u (mem_domain_of_kpair_mem hup)

theorem lowRankNameSet_mono_poset {P Q η : V} (hPQ : P ⊆ Q) :
    lowRankNameSet P η ⊆ lowRankNameSet Q η := by
  intro τ hτ
  obtain ⟨hτη, hτP⟩ := (mem_lowRankNameSet P η τ).mp hτ
  exact (mem_lowRankNameSet Q η τ).mpr ⟨hτη, hτP.mono hPQ⟩

variable {Ω θ : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
local notation "C" => woodinSparseStageCode θ
local notation "P" => forcingCodeP C
local notation "R" => forcingCodeR C
include hΩ hAC hθ

/-- The actual sparse iteration's identity sections discharge every projection
and order hypothesis of bounded forcing agreement, including at its endpoint. -/
theorem woodinSparse_boundedForcing_prefix_iff {i D0 D1 n φ b p : V} (hi : i ∈ θ)
    (hD0 : IsSubnameClosedForcingPool (P ‘ i) D0)
    (hD1 : IsSubnameClosedForcingPool (P ‘ θ) D1)
    (hφ : IsBoundedFormulaCode n φ) (hb0 : b ∈ D0 ^ n) (hb1 : b ∈ D1 ^ n)
    (hp : p ∈ P ‘ i) :
    p ∈ internalForcingSet (P ‘ i) (R ‘ i) D0 n φ b ↔
      p ∈ internalForcingSet (P ‘ θ) (R ‘ θ) D1 n φ b := by
  have hv := woodinSparseStageCode_valid hΩ hAC hθ
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have ht : θ ∈ succ θ := mem_succ_self θ
  exact boundedForcing_prefix_iff (hv.system.order.preorder i hi') (hv.system.tops.top i hi')
    (hv.system.order.preorder θ ht) (hv.system.tops.top θ ht)
    (hv.system.splitProjection hi' ht (IsOrdinal.toIsTransitive.transitive _ hi))
    (fun p hp ↦ woodinSparseStageCode_section hΩ hAC hθ hi hp)
    hD0 hD1 hφ hb0 hb1 hp

/-- Bounded-prefix independence on the actual low-name pools. Neither forcing
agreement nor a name-pool closure assertion is assumed. -/
theorem woodinSparse_boundedForcing_lowNames_iff {i η n φ b p : V} [IsOrdinal η]
    (hi : i ∈ θ) (hη : (∅ : V) ∈ η)
    (hφ : IsBoundedFormulaCode n φ) (hb : b ∈ lowRankNameSet (P ‘ i) η ^ n)
    (hp : p ∈ P ‘ i) :
    p ∈ internalForcingSet (P ‘ i) (R ‘ i) (lowRankNameSet (P ‘ i) η) n φ b ↔
      p ∈ internalForcingSet (P ‘ θ) (R ‘ θ) (lowRankNameSet (P ‘ θ) η) n φ b := by
  have hv := woodinSparseStageCode_valid hΩ hAC hθ
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have hπ := hv.system.splitProjection hi' (mem_succ_self θ)
    (IsOrdinal.toIsTransitive.transitive _ hi)
  have hP := hπ.subset_of_section_identity
    (fun p hp ↦ woodinSparseStageCode_section hΩ hAC hθ hi hp)
  exact woodinSparse_boundedForcing_prefix_iff hΩ hAC hθ hi
    (lowRankNameSet_subnameClosedForcingPool _ hη) (lowRankNameSet_subnameClosedForcingPool _ hη)
    hφ hb (mem_function_of_mem_function_of_subset hb (lowRankNameSet_mono_poset hP)) hp

end ZFVP
