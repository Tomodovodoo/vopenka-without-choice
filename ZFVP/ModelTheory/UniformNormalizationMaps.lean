import ZFVP.ModelTheory.UniformLeastRankNormalization
import ZFVP.ModelTheory.NormalizedMapDefinability
import ZFVP.SetTheory.UniformFunctionOperations
import ZFVP.SetTheory.ForcingRetractionFixedPoints

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingGuardedNormalizationFormula : SetTheorySemisentence 6 :=
  f“z P R o p τ. !forcingLeastRankNameFormula z P R o (!forcingRestrictedNameFormula P R p τ)”

def boundedNameTwoStepFormula : SetTheorySemisentence 5 :=
  f“C P R δ Q. ∀ z, z ∈ C ↔ z ∈ !prod.dfn P (!hierarchyFormula δ) ∧
    !forcingNameFormula P (!kpair.π₂.dfn z) ∧
    !kpair.π₁.dfn z ∈ !atomicMembershipFormula P R (!kpair.π₂.dfn z) Q”

def guardedTwoStepCodeFormula : SetTheorySemisentence 5 :=
  “y P R o z. ∃ p, ∃ σ, ∃ τ,
    !kpair.π₁.dfn p z ∧ !kpair.π₂.dfn σ z ∧
    !forcingGuardedNormalizationFormula τ P R o p σ ∧ !kpair.dfn y p τ”

def guardedTwoStepMapFormula : SetTheorySemisentence 6 :=
  f“M P R o δ Q. ∀ z, z ∈ M ↔ ∃ x ∈ !boundedNameTwoStepFormula P R δ Q,
    z = !kpair.dfn x (!guardedTwoStepCodeFormula P R o x)”

def equivalentSuborderFixFormula : SetTheorySemisentence 4 :=
  f“y N f q. (q ∈ N ∧ y = q) ∨ (q ∉ N ∧ !value.dfn y f q)”

def equivalentSuborderRetractionFormula : SetTheorySemisentence 4 :=
  f“r P N f. ∀ z, z ∈ r ↔ ∃ x ∈ P, z = !kpair.dfn x (!equivalentSuborderFixFormula N f x)”

def normalizedTwoStepRetractionFormula : SetTheorySemisentence 6 :=
  “r P R o δ Q. ∃ C, ∃ N, ∃ f,
    !boundedNameTwoStepFormula C P R δ Q ∧
    !normalizedNameTwoStepFormula N P R o δ Q ∧ !guardedTwoStepMapFormula f P R o δ Q ∧
    !equivalentSuborderRetractionFormula r C N f”

def retractedBaseTwoStepCodeFormula : SetTheorySemisentence 3 :=
  f“y m z. y = !kpair.dfn (!value.dfn m (!kpair.π₁.dfn z)) (!nameActionFormula m (!kpair.π₂.dfn z))”

def retractedBaseTwoStepMapFormula : SetTheorySemisentence 6 :=
  f“f P R δ Q m. ∀ z, z ∈ f ↔ ∃ x ∈ !boundedNameTwoStepFormula P R δ Q,
    z = !kpair.dfn x (!retractedBaseTwoStepCodeFormula m x)”

def normalizedBaseTwoStepMapFormula : SetTheorySemisentence 9 :=
  “f P R N T o δ Q m. ∃ g, ∃ h, ∃ U,
    !retractedBaseTwoStepMapFormula g P R δ Q m ∧
    !nameActionFormula U m Q ∧
    !normalizedTwoStepRetractionFormula h N T o δ U ∧ !composeFormula f g h”

def forcingThreadActionFormula : SetTheorySemisentence 4 :=
  f“g θ m f. ∀ z, z ∈ g ↔ ∃ i ∈ θ,
    z = !kpair.dfn i (!value.dfn (!value.dfn m i) (!value.dfn f i))”

def forcingThreadActionMapFormula : SetTheorySemisentence 4 :=
  f“r θ m C. ∀ z, z ∈ r ↔ ∃ f ∈ C, z = !kpair.dfn f (!forcingThreadActionFormula θ m f)”

def forcingMapFixedPointsFormula : SetTheorySemisentence 3 :=
  f“N P m. ∀ p, p ∈ N ↔ p ∈ P ∧ !value.dfn p m p”

def forcingOrderRestrictionFormula : SetTheorySemisentence 3 :=
  f“T N R. ∀ z, z ∈ T ↔ z ∈ !prod.dfn N N ∧ z ∈ R”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingGuardedNormalizationFormula_defined :
    ℒₛₑₜ-function₅[V] forcingGuardedNormalization via forcingGuardedNormalizationFormula :=
  ⟨fun v ↦ by simp [forcingGuardedNormalizationFormula, forcingGuardedNormalization]⟩

instance boundedNameTwoStepFormula_defined :
    ℒₛₑₜ-function₄[V] boundedNameTwoStep via boundedNameTwoStepFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [boundedNameTwoStepFormula, boundedNameTwoStep]⟩

instance guardedTwoStepCodeFormula_defined :
    ℒₛₑₜ-function₄[V] guardedTwoStepCode via guardedTwoStepCodeFormula :=
  ⟨fun v ↦ by simp [guardedTwoStepCodeFormula, guardedTwoStepCode]⟩

instance guardedTwoStepMapFormula_defined :
    ℒₛₑₜ-function₅[V] guardedTwoStepMap via guardedTwoStepMapFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [guardedTwoStepMapFormula, guardedTwoStepMap, mem_definableGraph_iff]⟩

instance equivalentSuborderFixFormula_defined :
    ℒₛₑₜ-function₃[V] equivalentSuborderFix via equivalentSuborderFixFormula :=
  ⟨fun v ↦ by
    classical
    by_cases h : v 3 ∈ v 1 <;> simp [equivalentSuborderFixFormula, equivalentSuborderFix, h]⟩

instance equivalentSuborderRetractionFormula_defined :
    ℒₛₑₜ-function₃[V] equivalentSuborderRetraction via equivalentSuborderRetractionFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [equivalentSuborderRetractionFormula, equivalentSuborderRetraction, mem_definableGraph_iff]⟩

instance normalizedTwoStepRetractionFormula_defined :
    ℒₛₑₜ-function₅[V] normalizedTwoStepRetraction via normalizedTwoStepRetractionFormula :=
  ⟨fun v ↦ by simp [normalizedTwoStepRetractionFormula, normalizedTwoStepRetraction]⟩

instance retractedBaseTwoStepCodeFormula_defined :
    ℒₛₑₜ-function₂[V] retractedBaseTwoStepCode via retractedBaseTwoStepCodeFormula :=
  ⟨fun v ↦ by simp [retractedBaseTwoStepCodeFormula, retractedBaseTwoStepCode]⟩

instance retractedBaseTwoStepMapFormula_defined :
    ℒₛₑₜ-function₅[V] retractedBaseTwoStepMap via retractedBaseTwoStepMapFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [retractedBaseTwoStepMapFormula, retractedBaseTwoStepMap, mem_definableGraph_iff]⟩

instance normalizedBaseTwoStepMapFormula_defined :
    Defined (fun v : Fin 9 → V ↦ v 0 = normalizedBaseTwoStepMap
      (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) normalizedBaseTwoStepMapFormula :=
  ⟨fun v ↦ by simp [normalizedBaseTwoStepMapFormula, normalizedBaseTwoStepMap]⟩

instance forcingThreadActionFormula_defined :
    ℒₛₑₜ-function₃[V] forcingThreadAction via forcingThreadActionFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingThreadActionFormula, forcingThreadAction, mem_definableGraph_iff]⟩

instance forcingThreadActionMapFormula_defined :
    ℒₛₑₜ-function₃[V] forcingThreadActionMap via forcingThreadActionMapFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingThreadActionMapFormula, forcingThreadActionMap, mem_definableGraph_iff]⟩

instance forcingMapFixedPointsFormula_defined :
    ℒₛₑₜ-function₂[V] forcingMapFixedPoints via forcingMapFixedPointsFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingMapFixedPointsFormula, forcingMapFixedPoints, eq_comm]⟩

instance forcingOrderRestrictionFormula_defined :
    ℒₛₑₜ-function₂[V] forcingOrderRestriction via forcingOrderRestrictionFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingOrderRestrictionFormula, forcingOrderRestriction]⟩

def normalizationMapsDictionary : SetFormulaDictionary :=
  [⟨6, forcingGuardedNormalizationFormula⟩, ⟨5, boundedNameTwoStepFormula⟩,
   ⟨5, guardedTwoStepCodeFormula⟩, ⟨6, guardedTwoStepMapFormula⟩,
   ⟨4, equivalentSuborderFixFormula⟩, ⟨4, equivalentSuborderRetractionFormula⟩,
   ⟨6, normalizedTwoStepRetractionFormula⟩, ⟨3, retractedBaseTwoStepCodeFormula⟩,
   ⟨6, retractedBaseTwoStepMapFormula⟩, ⟨9, normalizedBaseTwoStepMapFormula⟩,
   ⟨4, forcingThreadActionFormula⟩, ⟨4, forcingThreadActionMapFormula⟩,
   ⟨3, forcingMapFixedPointsFormula⟩, ⟨3, forcingOrderRestrictionFormula⟩]

def normalizationMapsDictionaryBound : ℕ := levyDictionaryBound normalizationMapsDictionary

theorem normalizationMapsDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ normalizationMapsDictionary) (p : LevyPolarity) :
    IsLevyFormula p normalizationMapsDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
