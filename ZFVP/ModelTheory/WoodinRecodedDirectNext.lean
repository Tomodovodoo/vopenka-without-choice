import ZFVP.ModelTheory.WoodinRecodedDirect
import ZFVP.ModelTheory.WoodinNormalizedPrefix
import ZFVP.ModelTheory.ForcingRecodedExtension
import ZFVP.ModelTheory.ForcingRecodedPrefix

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinRecodedDirectNextCode (θ Q T m : V) : V :=
  let c := forcingRecodedCode θ (woodinNormalizedPrefixCode θ) Q T m
  forcingRecodedCode (succ θ) (woodinNormalizedStageCode θ)
    (forcingFamilyNext θ Q (forcingSparseCodes θ c (forcingCodeUniverse c)))
    (forcingFamilyNext θ T (forcingSparseOrder θ c (forcingCodeUniverse c)))
    (forcingFamilyNext θ m (woodinRecodedDirectMap θ c m))

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₅.comp

instance woodinRecodedDirectNextCode_definable : ℒₛₑₜ-function₄[V] woodinRecodedDirectNextCode := by
  unfold woodinRecodedDirectNextCode
  dsimp only
  apply Language.DefinableFunction₅.comp
  · definability
  · definability
  · apply Language.DefinableFunction₃.comp
    · definability
    · definability
    · apply Language.DefinableFunction₃.comp
      · definability
      · apply Language.DefinableFunction₅.comp <;> definability
      · unfold forcingCodeUniverse
        simp only [forcingRecodedCode, forcingCodeP_code]
        definability
  · apply Language.DefinableFunction₃.comp
    · definability
    · definability
    · apply Language.DefinableFunction₃.comp
      · definability
      · apply Language.DefinableFunction₅.comp <;> definability
      · unfold forcingCodeUniverse
        simp only [forcingRecodedCode, forcingCodeP_code]
        definability
  · apply Language.DefinableFunction₃.comp
    · definability
    · definability
    · apply Language.DefinableFunction₃.comp
      · definability
      · apply Language.DefinableFunction₅.comp <;> definability
      · definability

variable {Ω θ Q T m : V} [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "c" => forcingRecodedCode θ N Q T m
local notation "A" => forcingSparseCodes θ c (forcingCodeUniverse c)
local notation "B" => forcingSparseOrder θ c (forcingCodeUniverse c)
local notation "f" => woodinRecodedDirectMap θ c m
local notation "next" => woodinRecodedDirectNextCode θ Q T m

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
variable (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
variable (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)

include hΩ hAC hθ h0 hlim hinac hm hT hQt hTt

theorem woodinRecodedDirectNext_family :
    ∀ i ∈ succ θ, IsForcingIsomorphism ((forcingCodeP C) ‘ i) ((forcingCodeR C) ‘ i)
      ((forcingFamilyNext θ Q A) ‘ i) ((forcingFamilyNext θ T B) ‘ i)
      ((forcingFamilyNext θ m f) ‘ i) := by
  let := hΩ.inaccessible.1
  apply forcingRecoded_next_family
    (fun _ hi ↦ (woodinNormalizedStage_old_carrier_order hΩ hAC hθ hi).1)
    (fun _ hi ↦ (woodinNormalizedStage_old_carrier_order hΩ hAC hθ hi).2) hm
  exact woodinRecodedDirectMap_isomorphism hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ)
    h0 hlim hinac hm hT hQt hTt

theorem woodinRecodedDirectNext_valid : IsForcingIterationCode (succ θ) next := by
  let := hΩ.inaccessible.1
  apply forcingRecoded_next_code (woodinNormalizedStageCode_valid hΩ hAC hθ)
    (fun _ hi ↦ (woodinNormalizedStage_old_carrier_order hΩ hAC hθ hi).1)
    (fun _ hi ↦ (woodinNormalizedStage_old_carrier_order hΩ hAC hθ hi).2) hm hT
    (woodinRecodedDirectMap_isomorphism hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ)
      h0 hlim hinac hm hT hQt hTt)
  unfold forcingSparseOrder forcingPullbackOrder
  exact sep_subset

theorem woodinRecodedDirectNext_extends : ForcingCodeExtends c next := by
  let := hΩ.inaccessible.1
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ)
  exact forcingRecoded_extends hs (woodinNormalizedStageCode_valid hΩ hAC hθ)
    (woodinNormalizedStage_extends hΩ hAC hθ)
    (fun _ hi ↦ mem_succ_iff.mpr (Or.inr hi))
    (fun _ hi ↦ (forcingFamilyNext_old hi).symm)
    (fun _ hi ↦ (forcingFamilyNext_old hi).symm)
    (fun _ hi ↦ (forcingFamilyNext_old hi).symm)
    (forcingRecoded_code hs hm hT hQt hTt)
    (woodinRecodedDirectNext_valid hΩ hAC hθ h0 hlim hinac hm hT hQt hTt)

theorem woodinRecodedDirectNext_restrictions :
    (forcingCodeP next) ↾ θ = forcingCodeP c ∧ (forcingCodeR next) ↾ θ = forcingCodeR c ∧
    (forcingCodeπ next) ↾ (θ ×ˢ θ) = forcingCodeπ c ∧ (forcingCodeE next) ↾ (θ ×ˢ θ) = forcingCodeE c ∧
    (forcingCodeL next) ↾ (θ ×ˢ θ) = forcingCodeL c ∧ (forcingCodet next) ↾ θ = forcingCodet c := by
  let := hΩ.inaccessible.1
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ)
  exact (woodinRecodedDirectNext_extends hΩ hAC hθ h0 hlim hinac hm hT hQt hTt).restrictions
    (forcingRecoded_code hs hm hT hQt hTt)
    (woodinRecodedDirectNext_valid hΩ hAC hθ h0 hlim hinac hm hT hQt hTt)
    (fun _ hi ↦ mem_succ_iff.mpr (Or.inr hi))

omit hΩ hAC hθ h0 hlim hinac hm hT hQt hTt [IsOrdinal θ] in
theorem woodinRecodedDirectNext_carrier_order :
    (forcingCodeP next) ‘ θ = A ∧ (forcingCodeR next) ‘ θ = B := by
  simp only [woodinRecodedDirectNextCode, forcingRecodedCode, forcingCodeP_code,
    forcingCodeR_code, forcingFamilyNext_new, and_self]

omit hΩ hAC hθ h0 hinac hm hT hQt hTt in
theorem woodinRecodedDirectNext_rank (hQ : ∀ i ∈ θ, Q ‘ i ∈ hierarchy θ) :
    (forcingCodeP next) ‘ θ ⊆ hierarchy θ ∧ (forcingCodeR next) ‘ θ ⊆ hierarchy θ := by
  rw [woodinRecodedDirectNext_carrier_order.1, woodinRecodedDirectNext_carrier_order.2]
  have hQc : ∀ i ∈ θ, (forcingCodeP c) ‘ i ∈ hierarchy θ := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hQ
  exact ⟨forcingSparseCodes_subset_hierarchy (ordinal_limit_of_not_successor hlim) hQc,
    forcingSparseOrder_subset_hierarchy (ordinal_limit_of_not_successor hlim) hQc⟩

end ZFVP
