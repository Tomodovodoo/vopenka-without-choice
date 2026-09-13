import ZFVP.ModelTheory.NormalizedWoodinModel
import ZFVP.SetTheory.HartogsDictionary
import ZFVP.SetTheory.UniformRank
import ZFVP.SetTheory.ElementaryDependentChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R one κ δ : V}
  (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
  (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
  (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
  (G : Set V)

local notation "Q" => saturatedWoodinPrefixPosetName P R one κ δ
local notation "S" => saturatedWoodinPrefixOrderName P R one κ δ
local notation "C" => twoStepConditions P R Q ∅
local notation "T" => twoStepOrder P R Q S ∅

theorem normalizedWoodinPrefix_checked_truth (hG : IsExternalForcingGeneric C T G)
    {n : ℕ} (φ : SetTheorySemisentence n) (a : Fin n → V) :
    φ.Evalb (fun i ↦ (normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).check (a i)) ↔
    φ.Evalb (fun i ↦ (twoStepTotalContext hR ht (saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ) hG).check (a i)) := by
  have hh := (normalizedWoodinPrefixElementaryMap hR ht hδ hP hκδ hκ G hG).evalb φ
    (fun i ↦ (normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).check (a i))
  have he : (normalizedWoodinPrefixElementaryMap hR ht hδ hP hκδ hκ G hG ∘
      fun i ↦ (normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).check (a i)) =
      (fun i ↦ (twoStepTotalContext hR ht (saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ) hG).check (a i)) := by
    funext i
    exact normalizedWoodinPrefixModelEquiv_check hR ht hδ hP hκδ hκ G hG (a i)
  rwa [he] at hh

theorem normalizedWoodinPrefixModelEquiv_hartogs (hG : IsExternalForcingGeneric C T G) (γ : V) :
    normalizedWoodinPrefixModelEquiv hR ht hδ hP hκδ hκ G hG
      (hartogsNumber ((normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).check γ)) =
    hartogsNumber ((twoStepTotalContext hR ht (saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ) hG).check γ) := by
  have hh := (normalizedWoodinPrefixElementaryMap hR ht hδ hP hκδ hκ G hG).map_hartogsNumber
    ((normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).check γ)
  change normalizedWoodinPrefixModelEquiv hR ht hδ hP hκδ hκ G hG _ =
    hartogsNumber (normalizedWoodinPrefixModelEquiv hR ht hδ hP hκδ hκ G hG _) at hh
  simpa only [normalizedWoodinPrefixModelEquiv_check] using hh

theorem normalizedWoodinPrefixModelEquiv_hierarchy (hG : IsExternalForcingGeneric C T G) (γ : V) :
    normalizedWoodinPrefixModelEquiv hR ht hδ hP hκδ hκ G hG
      (hierarchy ((normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).check γ)) =
    hierarchy ((twoStepTotalContext hR ht (saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ) hG).check γ) := by
  have hh := (normalizedWoodinPrefixElementaryMap hR ht hδ hP hκδ hκ G hG).map_hierarchy
    ((normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).check γ)
  change normalizedWoodinPrefixModelEquiv hR ht hδ hP hκδ hκ G hG _ =
    hierarchy (normalizedWoodinPrefixModelEquiv hR ht hδ hP hκδ hκ G hG _) at hh
  simpa only [normalizedWoodinPrefixModelEquiv_check] using hh

theorem normalizedWoodinPrefix_dependentChoiceAt (hG : IsExternalForcingGeneric C T G) (γ : V) :
    InternalDependentChoiceAt ((normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).check γ) ↔
    InternalDependentChoiceAt ((twoStepTotalContext hR ht (saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ) hG).check γ) := by
  simpa using normalizedWoodinPrefix_checked_truth hR ht hδ hP hκδ hκ G hG dependentChoiceAtFormula ![γ]

theorem normalizedWoodinPrefix_dependentChoiceBelow (hG : IsExternalForcingGeneric C T G) (γ : V) :
    (∀ η ∈ (normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).check γ, InternalDependentChoiceAt η) ↔
    (∀ η ∈ (twoStepTotalContext hR ht (saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ) hG).check γ,
      InternalDependentChoiceAt η) := by
  simpa using normalizedWoodinPrefix_checked_truth hR ht hδ hP hκδ hκ G hG dependentChoiceBelowFormula ![γ]

end ZFVP
