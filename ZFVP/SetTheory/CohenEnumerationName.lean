import ZFVP.SetTheory.CohenSetName
import ZFVP.SetTheory.ForcingPairNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The full enumeration is an ordinary forcing name. Hereditary symmetry is not asserted. -/
noncomputable def cohenEnumerationName (I : V) : V :=
  repl (fun i ↦ ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName I i), (∅ : V)⟩ₖ) (by definability) I

theorem mem_cohenEnumerationName (I z : V) : z ∈ cohenEnumerationName I ↔
    ∃ i ∈ I, z = ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName I i), (∅ : V)⟩ₖ := repl_spec _

instance cohenEnumerationName_definable : ℒₛₑₜ-function₁[V] cohenEnumerationName := by
  have h : ℒₛₑₜ-relation[V] (fun A I ↦ ∀ z, z ∈ A ↔
      ∃ i ∈ I, z = ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName I i), (∅ : V)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cohenEnumerationName (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_cohenEnumerationName]

theorem cohenEnumerationName_isName (I : V) :
    IsForcingName (cohenConditions I) (cohenEnumerationName I) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨i, hi, rfl⟩ := (mem_cohenEnumerationName I z).mp hz
  exact ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName I i), ∅, (cohen_top I).1, rfl,
    orderedPairName_isName (cohen_top I).1 (checkName_isName (cohen_top I).1 i) (cohenRealName_isName I i)⟩

end ZFVP
