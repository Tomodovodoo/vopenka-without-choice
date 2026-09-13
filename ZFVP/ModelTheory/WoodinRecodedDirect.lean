import ZFVP.ModelTheory.ForcingRecodedSparse
import ZFVP.ModelTheory.ForcingNormalizedDirectOrder
import ZFVP.ModelTheory.WoodinNormalizedSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinRecodedDirectMap (θ z m : V) : V :=
  forcingRecodedSparseMap θ (woodinNormalizedPrefixCode θ) z m
    (forcingCodeUniverse (woodinIterationPrefix θ))

instance woodinRecodedDirectMap_definable : ℒₛₑₜ-function₃[V] woodinRecodedDirectMap := by
  unfold woodinRecodedDirectMap
  apply Language.DefinableFunction₅.comp <;> definability

variable {Ω θ : V} [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "U" => forcingCodeUniverse (woodinIterationPrefix θ)
local notation "D" => forcingDirectLimit θ (forcingCodeP N) (forcingCodeπ N) (forcingCodeE N) U

theorem woodinNormalizedPrefix_subset_universe
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    ∀ i ∈ θ, (forcingCodeP N) ‘ i ⊆ U := by
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
  have hn := woodinNormalizationHistory_actual_prefix hΩ hAC hθ
  intro i hi p hp
  apply hs.code.subset_universe i hi
  apply hn.inclusion i hi p
  simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code] using hp

theorem woodinNormalized_direct_dictionary
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ = D ∧
      (forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ = forcingThreadOrder θ (forcingCodeR N) D := by
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
  have hn := woodinNormalizationHistory_actual_prefix hΩ hAC hθ
  constructor
  · rw [woodinNormalized_direct_poset h0 hlim hinac, forcingNormalized_direct_fixedPoints hn hs.code]
    simp only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code,
      forcingCodeπ_code, forcingCodeE_code]
  · rw [woodinNormalized_direct_order h0 hlim hinac, forcingNormalized_direct_fixedPoints hn hs.code]
    simpa only [forcingDirectCode, forcingThreadCode_order, woodinNormalizedPrefixCode,
      forcingNormalizedCode, forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingCodeE_code]
      using (forcingNormalized_direct_threadOrder hn hs.code :
        forcingOrderRestriction _ (forcingThreadOrder θ _ (forcingDirectLimit θ _ _ _ U)) = _)

variable {Q T m : V}
local notation "c" => forcingRecodedCode θ N Q T m
local notation "A" => forcingSparseCodes θ c (forcingCodeUniverse c)
local notation "B" => forcingSparseOrder θ c (forcingCodeUniverse c)

theorem woodinRecodedDirectMap_isomorphism
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T) :
    IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ) A B (woodinRecodedDirectMap θ c m) := by
  obtain ⟨hp, hr⟩ := woodinNormalized_direct_dictionary hΩ hAC hθ h0 hlim hinac
  rw [hp, hr]
  exact forcingRecodedSparseMap_isomorphism (woodinNormalizedPrefixCode_valid hΩ hAC hθ)
    hm hT hQt hTt (woodinNormalizedPrefix_subset_universe hΩ hAC hθ)

theorem woodinRecodedDirectMap_coordinate {f i : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
    (hf : f ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ) (hi : i ∈ θ) :
    ((forcingSparseDecode θ c (forcingCodeUniverse c)) ‘ ((woodinRecodedDirectMap θ c m) ‘ f)) ‘ i =
      (m ‘ i) ‘ (f ‘ i) := by
  rw [(woodinNormalized_direct_dictionary hΩ hAC hθ h0 hlim hinac).1] at hf
  exact forcingRecodedSparseMap_coordinate (woodinNormalizedPrefixCode_valid hΩ hAC hθ)
    hm hT hQt hTt (woodinNormalizedPrefix_subset_universe hΩ hAC hθ) hf hi

end ZFVP
