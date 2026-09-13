import ZFVP.SetTheory.WellOrderedSelection
import ZFVP.SetTheory.ChoiceDictionary

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def svcWitnessFormula : SetTheorySemisentence 1 :=
  f“D. ∀ A, ∃ α, !IsOrdinal.dfn α ∧
    ∃ f ∈ !function.dfn A (!prod.dfn D α), !range.dfn f = A”

def smallViolationsOfChoiceSentence : SetTheorySentence := ∃¹ svcWitnessFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsSVCWitness (D : V) : Prop :=
  ∀ A : V, ∃ α, IsOrdinal α ∧ ∃ f ∈ A ^ (D ×ˢ α), range f = A

def InternalSmallViolationsOfChoice (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop := ∃ D : V, IsSVCWitness D

instance svcWitnessFormula_defined : ℒₛₑₜ-predicate[V] IsSVCWitness via svcWitnessFormula :=
  ⟨fun v ↦ by simp [svcWitnessFormula, IsSVCWitness]⟩

instance isSVCWitness_definable : ℒₛₑₜ-predicate[V] IsSVCWitness := by
  unfold IsSVCWitness
  definability

instance smallViolationsOfChoiceSentence_defined :
    Defined (fun _ : Fin 0 → V ↦ InternalSmallViolationsOfChoice V) smallViolationsOfChoiceSentence :=
  ⟨fun v ↦ by simp [smallViolationsOfChoiceSentence, InternalSmallViolationsOfChoice]⟩

theorem IsSVCWitness.nonempty {D : V} (hD : IsSVCWitness D) : IsNonempty D := by
  obtain ⟨α, _, f, hf, hr⟩ := hD ({∅} : V)
  have hz : (∅ : V) ∈ range f := by rw [hr]; simp
  obtain ⟨x, hx⟩ := mem_range_iff.mp hz
  have hxd : x ∈ D ×ˢ α := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hx
  obtain ⟨d, hd, _, _, _⟩ := mem_prod_iff.mp hxd
  exact ⟨d, hd⟩

theorem internalChoice_of_wellOrderable_svcWitness {D : V} (hD : IsSVCWitness D)
    (hw : IsWellOrderable D) : InternalChoice V := by
  apply internalChoice_of_all_wellOrderable
  intro A
  obtain ⟨α, hα, f, hf, hr⟩ := hD A
  have : IsOrdinal α := hα
  exact wellOrderable_of_surjective_function (wellOrderable_prod hw (ordinal_wellOrderable α)) hf hr

end ZFVP

