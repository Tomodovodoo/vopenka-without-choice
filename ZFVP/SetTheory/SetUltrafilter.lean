import ZFVP.SetTheory.BoundedRankTables
import ZFVP.SetTheory.Hartogs

/-! Ultrafilters and ordinal-indexed completeness as internal set predicates. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def relativeComplement (K X : V) : V := {z ∈ K ; z ∉ X}

instance relativeComplement_definable : ℒₛₑₜ-function₂[V] relativeComplement := by
  have hd : ℒₛₑₜ-relation₃[V] (fun Y K X ↦ ∀ z, z ∈ Y ↔ z ∈ K ∧ z ∉ X) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = relativeComplement (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [relativeComplement, mem_sep_iff]

@[simp] theorem mem_relativeComplement_iff (z K X : V) :
    z ∈ relativeComplement K X ↔ z ∈ K ∧ z ∉ X := by simp [relativeComplement]

noncomputable def indexedIntersection (K I g : V) : V := {z ∈ K ; ∀ i ∈ I, z ∈ g ‘ i}

instance indexedIntersection_definable : ℒₛₑₜ-function₃[V] indexedIntersection := by
  have hd : ℒₛₑₜ-relation₄[V] (fun X K I g ↦ ∀ z,
    z ∈ X ↔ z ∈ K ∧ ∀ i ∈ I, z ∈ g ‘ i) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = indexedIntersection (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [indexedIntersection, mem_sep_iff]

@[simp] theorem mem_indexedIntersection_iff (z K I g : V) :
    z ∈ indexedIntersection K I g ↔ z ∈ K ∧ ∀ i ∈ I, z ∈ g ‘ i := by
  simp [indexedIntersection]

def IsSetUltrafilter (K U : V) : Prop :=
  U ⊆ ℘ K ∧ K ∈ U ∧ (∅ : V) ∉ U ∧
    (∀ X ∈ U, ∀ Y, Y ⊆ K → X ⊆ Y → Y ∈ U) ∧
    (∀ X ∈ U, ∀ Y ∈ U, X ∩ Y ∈ U) ∧
    ∀ X, X ⊆ K → X ∈ U ∨ relativeComplement K X ∈ U

def IsOrdinalComplete (κ U : V) : Prop :=
  ∀ α ∈ κ, ∀ g ∈ U ^ α, indexedIntersection κ α g ∈ U

def IsNonprincipalSetUltrafilter (κ U : V) : Prop :=
  IsSetUltrafilter κ U ∧ ∀ x ∈ κ, ({x} : V) ∉ U

def IsMeasurableOrdinal (κ : V) : Prop :=
  IsInitialOrdinal κ ∧ (ω : V) ∈ κ ∧
    ∃ U, IsNonprincipalSetUltrafilter κ U ∧ IsOrdinalComplete κ U

instance isSetUltrafilter_definable : ℒₛₑₜ-relation[V] IsSetUltrafilter := by
  unfold IsSetUltrafilter
  definability

instance isOrdinalComplete_definable : ℒₛₑₜ-relation[V] IsOrdinalComplete := by
  unfold IsOrdinalComplete
  definability

instance isNonprincipalSetUltrafilter_definable : ℒₛₑₜ-relation[V] IsNonprincipalSetUltrafilter := by
  unfold IsNonprincipalSetUltrafilter
  definability

instance isMeasurableOrdinal_definable : ℒₛₑₜ-predicate[V] IsMeasurableOrdinal := by
  unfold IsMeasurableOrdinal
  definability

end ZFVP
