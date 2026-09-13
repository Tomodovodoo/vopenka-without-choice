import ZFVP.Syntax.TermSubstitutionSemantics

/-! Prepending and shifting assignments indexed by the full internal omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def omegaAssignmentPrepend (e x : V) : V :=
  definableGraph ω (prependValue e x) (by definability)

noncomputable def omegaAssignmentShift (e : V) : V :=
  definableGraph ω (fun i ↦ e ‘ (succ i)) (by definability)

instance omegaAssignmentPrepend_definable : ℒₛₑₜ-function₂[V] omegaAssignmentPrepend := by
  have h : ℒₛₑₜ-relation₃ (fun E e x : V ↦ ∀ p, p ∈ E ↔ ∃ i ∈ (ω : V), p = ⟨i, prependValue e x i⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = omegaAssignmentPrepend (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [omegaAssignmentPrepend, mem_definableGraph_iff]

instance omegaAssignmentShift_definable : ℒₛₑₜ-function₁[V] omegaAssignmentShift := by
  have h : ℒₛₑₜ-relation (fun E e : V ↦ ∀ p, p ∈ E ↔ ∃ i ∈ (ω : V), p = ⟨i, e ‘ (succ i)⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = omegaAssignmentShift (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [omegaAssignmentShift, mem_definableGraph_iff]

theorem omegaAssignmentPrepend_zero (e x : V) : (omegaAssignmentPrepend e x) ‘ (0 : V) = x := by
  rw [omegaAssignmentPrepend, value_definableGraph _ _ _ (show (0 : V) ∈ (ω : V) by simp [zero_def])]
  simp [prependValue]

theorem omegaAssignmentPrepend_succ (e x : V) {i : V} (hi : i ∈ (ω : V)) :
    (omegaAssignmentPrepend e x) ‘ (succ i) = e ‘ i := by
  have : IsOrdinal i := IsOrdinal.of_mem hi
  have hne : succ i ≠ (0 : V) := by
    intro he
    exact not_mem_empty (he ▸ mem_succ_self i)
  rw [omegaAssignmentPrepend, value_definableGraph _ _ _ (ω_succ_closed hi)]
  simp only [prependValue, hne, ite_false, sUnion_succ_of_transitive]

theorem omegaAssignmentShift_value (e : V) {i : V} (hi : i ∈ (ω : V)) :
    (omegaAssignmentShift e) ‘ i = e ‘ (succ i) := value_definableGraph _ _ _ hi

theorem omegaAssignmentPrepend_mem {A e x : V} (he : e ∈ A ^ (ω : V)) (hx : x ∈ A) :
    omegaAssignmentPrepend e x ∈ A ^ (ω : V) := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  rcases internalNatural_cases hi with rfl | ⟨j, hj, rfl⟩
  · simpa [prependValue] using hx
  · have hval := omegaAssignmentPrepend_succ e x hj
    rw [omegaAssignmentPrepend, value_definableGraph _ _ _ (ω_succ_closed hj)] at hval
    rw [hval]
    exact function_value_mem he hj

theorem omegaAssignmentShift_mem {A e : V} (he : e ∈ A ^ (ω : V)) :
    omegaAssignmentShift e ∈ A ^ (ω : V) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hi ↦ function_value_mem he (ω_succ_closed hi))

theorem omegaAssignmentShift_prepend {A e x : V} (he : e ∈ A ^ (ω : V)) (hx : x ∈ A) :
    omegaAssignmentShift (omegaAssignmentPrepend e x) = e := by
  apply function_eq_of_values (omegaAssignmentShift_mem (omegaAssignmentPrepend_mem he hx)) he
  intro i hi
  rw [omegaAssignmentShift_value _ hi, omegaAssignmentPrepend_succ _ _ hi]

end ZFVP
