import ZFVP.ModelTheory.ForcingRecodedPrefix
import ZFVP.ModelTheory.WoodinNormalizedInversePrefix
import ZFVP.ModelTheory.WoodinRecodedInverseNext

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ Q T m : V} [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "c" => forcingRecodedCode θ N Q T m
local notation "next" => woodinRecodedInverseNextCode θ Q T m

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
variable (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
variable (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
variable (hQrank : ∀ i ∈ θ, Q ‘ i ∈ hierarchy (woodinNormalizedInverseCutoff θ))

include hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank

theorem woodinRecodedInverseNext_extends : ForcingCodeExtends c next := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC hsub
  have hz := woodinNormalizedStageCode_valid hΩ hAC hθ
  have hc := forcingRecoded_code hs hm hT hQt hTt
  have hnxt := woodinRecodedInverseNext_valid hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank
  rw [woodinRecodedInverseNextCode] at hnxt ⊢
  exact forcingRecoded_extends hs hz (woodinNormalizedStage_inverse_extends hΩ hAC hθ h0 hlim hn)
    (fun _ hi ↦ mem_succ_iff.mpr (Or.inr hi))
    (fun _ hi ↦ (forcingFamilyNext_old hi).symm)
    (fun _ hi ↦ (forcingFamilyNext_old hi).symm)
    (fun _ hi ↦ (forcingFamilyNext_old hi).symm) hc hnxt

theorem woodinRecodedInverseNext_restrictions :
    (forcingCodeP next) ↾ θ = forcingCodeP c ∧ (forcingCodeR next) ↾ θ = forcingCodeR c ∧
    (forcingCodeπ next) ↾ (θ ×ˢ θ) = forcingCodeπ c ∧ (forcingCodeE next) ↾ (θ ×ˢ θ) = forcingCodeE c ∧
    (forcingCodeL next) ↾ (θ ×ˢ θ) = forcingCodeL c ∧ (forcingCodet next) ↾ θ = forcingCodet c := by
  let := hΩ.inaccessible.1
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ)
  exact (woodinRecodedInverseNext_extends hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank).restrictions
    (forcingRecoded_code hs hm hT hQt hTt)
    (woodinRecodedInverseNext_valid hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank)
    (fun _ hi ↦ mem_succ_iff.mpr (Or.inr hi))

end ZFVP
