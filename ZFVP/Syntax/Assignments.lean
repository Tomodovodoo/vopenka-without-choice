import ZFVP.SetTheory.NaturalPredecessor
import ZFVP.SetTheory.FunctionValue

/-! Quantifiers prepend a value at index zero, matching Foundation's `x :> b`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def prependValue (b x i : V) : V := by
  classical
  exact if i = 0 then x else b ‘ (⋃ˢ i)

instance prependValue_definable : ℒₛₑₜ-function₃[V] prependValue := by
  have h : ℒₛₑₜ-relation₄ (fun y b x i : V ↦
      (i = 0 ∧ y = x) ∨ (i ≠ 0 ∧ y = b ‘ (⋃ˢ i))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = prependValue (v 1) (v 2) (v 3) ↔ _
  unfold prependValue
  split <;> simp_all

noncomputable def assignmentPrepend (n b x : V) : V :=
  definableGraph (succ n) (prependValue b x) (by definability)

instance assignmentPrepend_isFunction (n b x : V) : IsFunction (assignmentPrepend n b x) :=
  definableGraph_isFunction _ _ _

@[simp] theorem domain_assignmentPrepend (n b x : V) : domain (assignmentPrepend n b x) = succ n :=
  domain_definableGraph _ _ _

instance assignmentPrepend_definable : ℒₛₑₜ-function₃[V] assignmentPrepend := by
  have h : ℒₛₑₜ-relation₄ (fun B n b x : V ↦ ∀ p, p ∈ B ↔
      ∃ i ∈ succ n, p = ⟨i, prependValue b x i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = assignmentPrepend (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [assignmentPrepend, mem_definableGraph_iff]

theorem assignmentPrepend_mem_function {A n b x : V} (hn : n ∈ (ω : V))
    (hb : b ∈ A ^ n) (hx : x ∈ A) : assignmentPrepend n b x ∈ A ^ succ n := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  unfold prependValue
  split
  · exact hx
  · next hne => exact function_value_mem hb (natural_predecessor_mem hn hi hne)

theorem assignmentPrepend_zero {n : V} (hn : n ∈ (ω : V)) (b x : V) :
    (assignmentPrepend n b x) ‘ (0 : V) = x := by
  have h := value_definableGraph (succ n) (prependValue b x) (by definability)
    (zero_mem_succ_natural hn)
  simpa [assignmentPrepend, prependValue] using h

theorem assignmentPrepend_succ {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) (b x : V) :
    (assignmentPrepend n b x) ‘ (succ i) = b ‘ i := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal i := IsOrdinal.of_mem hi
  have hne : succ i ≠ (0 : V) := by
    intro h
    have hm : i ∈ succ i := by simp
    rw [h] at hm
    exact not_mem_empty hm
  have h := value_definableGraph (succ n) (prependValue b x) (by definability)
    (succ_mem_succ_of_natural_mem hn hi)
  simpa [assignmentPrepend, prependValue, hne, sUnion_succ_of_transitive] using h

end ZFVP
