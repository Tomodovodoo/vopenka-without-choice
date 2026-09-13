import ZFVP.SetTheory.CohenOrbitEvaluationName
import ZFVP.SetTheory.SymmetricSequenceNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCohenSupportPool (D : V) : Prop :=
  ∀ z ∈ D, IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) (kpair.π₁ z) ∧
    IsCohenNameSupport (kpair.π₁ z) (kpair.π₂ z)

instance isCohenSupportPool_definable : ℒₛₑₜ-predicate[V] IsCohenSupportPool := by
  unfold IsCohenSupportPool
  definability

noncomputable def cohenOrbitFamilySequence (D : V) : V :=
  definableGraph D (fun z ↦ cohenOrbitEvaluationName (kpair.π₂ z) (kpair.π₁ z)) (by definability)

theorem domain_cohenOrbitFamilySequence (D : V) : domain (cohenOrbitFamilySequence D) = D :=
  domain_definableGraph _ _ _

theorem cohenOrbitFamilySequence_value {D z : V} (hz : z ∈ D) :
    (cohenOrbitFamilySequence D) ‘ z = cohenOrbitEvaluationName (kpair.π₂ z) (kpair.π₁ z) :=
  value_definableGraph _ _ _ hz

theorem cohenOrbitFamilySequence_values_hs {D : V} (hD : IsCohenSupportPool D) :
    ∀ z ∈ domain (cohenOrbitFamilySequence D),
      IsHereditarilySymmetricName (cohenConditions (ω : V))
        (cohenGroup (ω : V)) (cohenFilter (ω : V)) ((cohenOrbitFamilySequence D) ‘ z) := by
  intro z hz
  rw [domain_cohenOrbitFamilySequence] at hz
  rw [cohenOrbitFamilySequence_value hz]
  exact cohenOrbitEvaluationName_hereditarilySymmetric (hD z hz).2.1 (hD z hz).2.2.1 (hD z hz).1

theorem cohenOrbitFamilySequence_values_fixed {D b : V} (hD : IsCohenSupportPool D)
    (hb : b ∈ cohenGroup (ω : V)) :
    ∀ z ∈ domain (cohenOrbitFamilySequence D),
      nameAction b ((cohenOrbitFamilySequence D) ‘ z) = (cohenOrbitFamilySequence D) ‘ z := by
  intro z hz
  rw [domain_cohenOrbitFamilySequence] at hz
  rw [cohenOrbitFamilySequence_value hz]
  obtain ⟨a, ha, rfl⟩ := (mem_cohenGroup (ω : V) b).mp hb
  exact (cohenOrbitEvaluationName_empty_support (hD z hz).2.1 (hD z hz).1.1).2.2 a ha
    (fun _ hi ↦ (not_mem_empty hi).elim)

/-- A ground-indexed internal family of the invariant orbit-evaluation maps. -/
noncomputable def cohenOrbitFamilyName (D : V) : V := sequenceName ∅ (cohenOrbitFamilySequence D)

theorem cohenOrbitFamilyName_hereditarilySymmetric {D : V} (hD : IsCohenSupportPool D) :
    IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) (cohenOrbitFamilyName D) := by
  apply hereditarilySymmetric_sequenceName (cohen_poset (ω : V)) (cohenGroup_group (ω : V))
    (cohenFilter_normal (ω : V)) (cohen_top (ω : V)) (cohenOrbitFamilySequence_values_hs hD)
  exact ⟨cohenGroup (ω : V), (cohenFilter_normal (ω : V)).2.1,
    fun b hb ↦ cohenOrbitFamilySequence_values_fixed hD hb⟩

end ZFVP
