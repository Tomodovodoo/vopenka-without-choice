import ZFVP.ModelTheory.WoodinSparseDirectRank
import ZFVP.ModelTheory.WoodinNormalizedEndpoint
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ Q T m : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
variable (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
variable (hsp : ∀ i ∈ θ, ∀ p ∈ Q ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
variable (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ Q ‘ j,
  ((forcingRecodedProjections θ (woodinNormalizedPrefixCode θ) m) ‘ ⟨i, j⟩ₖ) ‘ p =
    p ↾ (succ (woodinSourceIndex i)))
variable (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ Q ‘ i,
  ((forcingRecodedSections θ (woodinNormalizedPrefixCode θ) m) ‘ ⟨i, j⟩ₖ) ‘ p = p)

local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "c" => forcingRecodedCode θ N Q T m
variable (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
include hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE hinac in
theorem woodinSparseDirectMap_top (ht : ∀ i ∈ θ, (forcingCodet c) ‘ i = ∅) :
    (woodinSparseDirectMap θ c m) ‘ ((forcingCodet C) ‘ θ) = ∅ := by
  let := hΩ.inaccessible.1
  have hz : IsForcingIterationCode (succ θ) C := by
    rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
    · exact woodinNormalizedStageCode_endpoint_valid hΩ hAC
    · exact woodinNormalizedStageCode_valid hΩ hAC hθ
  have htop := (hz.system.tops.top θ (mem_succ_self θ)).1
  rw [woodinSparseDirectMap_value hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE hinac htop]
  have hzero : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hθ i hi)).1)
  have htv : ∀ i ∈ θ, ((forcingCodet C) ‘ θ) ‘ i = (forcingCodet N) ‘ i := by
    intro i hi
    simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodet_code,
      woodinIterationRec_direct h0 hlim hinac, kpair.π₁_kpair, forcingDirectCode, forcingThreadCode_top,
      woodinNormalizedPrefixCode]
    exact forcingSectionThread_top_value hs.code.system.tops hzero hi
  apply subset_empty_iff_eq_empty.mp
  intro z hz
  obtain ⟨p, hp, hz⟩ := mem_sUnion_iff.mp hz
  have hf : forcingThreadAction θ m ((forcingCodet C) ‘ θ) ∈
      (forcingCodeUniverse c) ^ θ :=
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp
      (forcingDirectLimit_subset _ _ _ _ _ _
        (woodinSparseDirect_mapped_thread_mem hΩ hAC hθ hm hT hQt hTt h0 hlim hinac htop))).1
  let := IsFunction.of_mem hf
  obtain ⟨i, hip⟩ := mem_range_iff.mp hp
  have hi : i ∈ θ := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hip
  have he : p = ∅ := by
    rw [← value_eq_of_kpair_mem hip, forcingThreadAction_value hi, htv i hi]
    simpa only [forcingRecodedCode, forcingCodet_code, forcingRecodedTops_value hi] using ht i hi
  exact he ▸ hz
end ZFVP
