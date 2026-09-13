import ZFVP.ModelTheory.WoodinSparseStageRules

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseInitial_no_zero {q : V} (hq : q ∈ (woodinSparseInitialCarrier : V)) :
    (∅ : V) ∉ domain q := by
  have he : q ↾ (succ (∅ : V)) = ∅ := by
    exact mem_singleton_iff.mp (mem_sparseNormalizedTwoStep_iff.mp hq).2.1
  intro hz
  have hr : (∅ : V) ∈ domain (q ↾ (succ (∅ : V))) := by
    rw [domain_restrict_eq]
    exact mem_inter_iff.mpr ⟨hz, mem_succ_self ∅⟩
  rw [he, domain_empty] at hr
  exact not_mem_empty hr

variable {Ω θ q : V} [IsOrdinal θ]

theorem woodinSparseStageCode_restrict_mem (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ θ) (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    q ↾ (succ (woodinSourceIndex i)) ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i := by
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have hm := (woodinSparseStageCode_valid hΩ hAC hθ).system.split.projMaps
    i hi' θ (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi) q hq
  rw [woodinSparseStageCode_projection hΩ hAC hθ hi hq] at hm
  simpa only [woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code,
    (woodinSparseRecodingHistory_values hi').1,
    (woodinSparseRecodingHistory_values (mem_succ_self i)).1] using hm

theorem woodinSparseStageCode_no_zero (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) : (∅ : V) ∉ domain q := by
  by_cases hz : θ = ∅
  · subst θ
    rw [(woodinSparseStageCode_initial).1] at hq
    exact woodinSparseInitial_no_zero hq
  · have hzero : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ hz he.symm)
    have hm := woodinSparseStageCode_restrict_mem hΩ hAC hθ hzero hq
    rw [(woodinSparseStageCode_initial).1] at hm
    intro hqzero
    apply woodinSparseInitial_no_zero hm
    rw [domain_restrict_eq]
    refine mem_inter_iff.mpr ⟨hqzero, ?_⟩
    rw [woodinSourceIndex_zero]
    exact mem_succ_iff.mpr (Or.inr (by change (∅ : V) ∈ succ ∅; exact mem_succ_self ∅))

theorem woodinSparseStageCode_direct_domain (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) : domain q ⊆ θ := by
  rw [(woodinSparseStageCode_direct h0 hlim hinac).1] at hq
  exact ((mem_woodinSparseInverseBase_iff (woodinSparsePrefixCode_valid hΩ hAC hθ)).mp
    (mem_woodinSparseDirectBase_iff.mp hq).1).1.2.1

theorem woodinSparseStageCode_direct_no_self (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) : θ ∉ domain q :=
  fun hx ↦ mem_irrefl θ (woodinSparseStageCode_direct_domain hΩ hAC hθ h0 hlim hinac hq θ hx)

theorem woodinSparseStageCode_no_earlier_direct (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {d : V} (hd : d ∈ θ) (h0 : d ≠ ∅) (hlim : d ≠ succ (⋃ˢ d))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix d)))
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) : d ∉ domain q := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hd
  have hdsub : d ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ (hθ d hd)
  have hm := woodinSparseStageCode_restrict_mem hΩ hAC hθ hd hq
  have hn := woodinSparseStageCode_direct_no_self hΩ hAC hdsub h0 hlim hinac hm
  have hz : (∅ : V) ∈ d := (IsOrdinal.subset_iff.mp (empty_subset d)).resolve_left (fun he ↦ h0 he.symm)
  intro hx
  apply hn
  rw [domain_restrict_eq, woodinSourceIndex_limit d hz (ordinal_limit_of_not_successor hlim)]
  exact mem_inter_iff.mpr ⟨hx, mem_succ_self d⟩

end ZFVP

