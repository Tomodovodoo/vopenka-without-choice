import ZFVP.ModelTheory.WoodinSparseDirectBase
import ZFVP.ModelTheory.WoodinRecodedDirect

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseDirectMap (θ c m : V) : V :=
  compose (compose (woodinRecodedDirectMap θ c m) (forcingSparseDecode θ c (forcingCodeUniverse c)))
    (woodinSparseDirectFlatten θ c)

instance woodinSparseDirectMap_definable : ℒₛₑₜ-function₃[V] woodinSparseDirectMap := by
  unfold woodinSparseDirectMap
  apply Language.DefinableFunction₂.comp
  · apply Language.DefinableFunction₂.comp
    · apply Language.DefinableFunction₃.comp <;> definability
    · apply Language.DefinableFunction₃.comp
      · definability
      · definability
      · unfold forcingCodeUniverse
        definability
  · apply Language.DefinableFunction₂.comp <;> definability

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
local notation "U" => forcingCodeUniverse (woodinIterationPrefix θ)
local notation "D" => forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c) (forcingCodeE c) (forcingCodeUniverse c)

include hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE in
theorem woodinSparseDirectFlatten_recoded_isomorphism :
    IsForcingIsomorphism D (forcingThreadOrder θ (forcingCodeR c) D)
      (woodinSparseDirectBase θ c) (woodinSparseDirectOrder θ c) (woodinSparseDirectFlatten θ c) := by
  have h0' : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  apply woodinSparseDirectFlatten_isomorphism
    (forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hθ) hm hT hQt hTt)
    h0' (ordinal_limit_of_not_successor hlim)
  · simpa only [forcingRecodedCode, forcingCodeP_code] using hsp
  · simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeπ_code] using hπ
  · simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeE_code] using hE

variable (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))

include hΩ hAC hθ hm hT hQt hTt h0 hlim hinac in
theorem woodinSparseDirect_mapped_thread_mem {p : V} (hp : p ∈ (forcingCodeP C) ‘ θ) :
    forcingThreadAction θ m p ∈ D := by
  rw [(woodinNormalized_direct_dictionary hΩ hAC hθ h0 hlim hinac).1] at hp
  have hi := forcingRecodedSparse_thread_isomorphism (woodinNormalizedPrefixCode_valid hΩ hAC hθ)
    hm hT hQt hTt (woodinNormalizedPrefix_subset_universe hΩ hAC hθ)
  have hmem := function_value_mem hi.1 hp
  rwa [forcingThreadActionMap_value hp] at hmem

include hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE hinac

theorem woodinSparseDirectMap_isomorphism :
    IsForcingIsomorphism ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ)
      (woodinSparseDirectBase θ c) (woodinSparseDirectOrder θ c) (woodinSparseDirectMap θ c m) := by
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hθ) hm hT hQt hTt
  exact ((woodinRecodedDirectMap_isomorphism hΩ hAC hθ h0 hlim hinac hm hT hQt hTt).comp
    (forcingSparseDecode_isomorphism hc hc.subset_universe)).comp
    (woodinSparseDirectFlatten_recoded_isomorphism hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE)

theorem woodinSparseDirectMap_value {p : V} (hp : p ∈ (forcingCodeP C) ‘ θ) :
    (woodinSparseDirectMap θ c m) ‘ p = ⋃ˢ range (forcingThreadAction θ m p) := by
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hθ) hm hT hQt hTt
  have hf := woodinRecodedDirectMap_isomorphism hΩ hAC hθ h0 hlim hinac hm hT hQt hTt
  have hd := forcingSparseDecode_isomorphism hc hc.subset_universe
  have hg := woodinSparseDirectFlatten_recoded_isomorphism hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE
  have hp' := hp
  rw [(woodinNormalized_direct_dictionary hΩ hAC hθ h0 hlim hinac).1] at hp'
  have hdec : (forcingSparseDecode θ c (forcingCodeUniverse c)) ‘ ((woodinRecodedDirectMap θ c m) ‘ p) =
      forcingThreadAction θ m p :=
    forcingRecodedSparseMap_decode (woodinNormalizedPrefixCode_valid hΩ hAC hθ)
      hm hT hQt hTt (woodinNormalizedPrefix_subset_universe hΩ hAC hθ) hp'
  rw [woodinSparseDirectMap, value_compose_of_mem_function (hf.comp hd).1 hg.1 hp,
    value_compose_of_mem_function hf.1 hd.1 hp,
    woodinSparseDirectFlatten_value (function_value_mem hd.1 (function_value_mem hf.1 hp)), hdec]

theorem woodinSparseDirectMap_restrict {p i : V} (hp : p ∈ (forcingCodeP C) ‘ θ) (hi : i ∈ θ) :
    ((woodinSparseDirectMap θ c m) ‘ p) ↾ (succ (woodinSourceIndex i)) = (m ‘ i) ‘ (p ‘ i) := by
  have hsp' : ∀ i ∈ θ, ∀ q ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) q := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hsp
  have hπ' : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ q ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ q = q ↾ (succ (woodinSourceIndex i)) := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeπ_code] using hπ
  have ht := woodinSparseDirect_mapped_thread_mem hΩ hAC hθ hm hT hQt hTt h0 hlim hinac hp
  have hti : forcingThreadAction θ m p ∈ forcingInverseCodePoset θ c := forcingDirectLimit_subset _ _ _ _ _ _ ht
  rw [woodinSparseInverse_threads hsp' hπ'] at hti
  rw [woodinSparseDirectMap_value hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE hinac hp]
  have he := sparseRestrictionThread_union_restrict hti hi
  simpa only [woodinSparseBounds_value hi, forcingThreadAction_value hi] using he

theorem woodinSparseDirectMap_of_support {p k : V} (hp : p ∈ (forcingCodeP C) ‘ θ)
    (hk : IsThreadSupport θ (forcingCodeE N) p k) :
    (woodinSparseDirectMap θ c m) ‘ p = (m ‘ k) ‘ (p ‘ k) := by
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC hθ
  have hp' := hp
  rw [(woodinNormalized_direct_dictionary hΩ hAC hθ h0 hlim hinac).1] at hp'
  have hpi := forcingDirectLimit_subset _ _ _ _ _ _ hp'
  have hk' : IsThreadSupport θ (forcingCodeE c) (forcingThreadAction θ m p) k := by
    simpa only [forcingRecodedCode, forcingCodeE_code] using (forcingRecodedThread_support_iff hs hm hpi).mpr hk
  have ht := woodinSparseDirect_mapped_thread_mem hΩ hAC hθ hm hT hQt hTt h0 hlim hinac hp
  have hti : forcingThreadAction θ m p ∈ forcingInverseCodePoset θ c := forcingDirectLimit_subset _ _ _ _ _ _ ht
  have hπ' : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ q ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ q = q ↾ (succ (woodinSourceIndex i)) := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeπ_code] using hπ
  have hE' : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ q ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ q = q := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeE_code] using hE
  rw [woodinSparseDirectMap_value hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE hinac hp,
    woodinSparseDirect_union_of_support hπ' hE' hti hk', forcingThreadAction_value hk.1]

end ZFVP
