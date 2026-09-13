import ZFVP.Syntax.TermSubstitutionSemantics

/-! Induced semantic assignments commute with binder lifting. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evaluate_liftBoundReplacement {L Δ n m M B b e x : V}
    (hM : IsStructureCode L M) (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hB : B ∈ termSet L Δ m ^ n) (hb : b ∈ structureDomain M ^ m)
    (he : e ∈ structureDomain M ^ Δ) (hx : x ∈ structureDomain M) :
    compose (liftBoundReplacement L Δ m n B)
      (termEvaluation L Δ (succ m) M (assignmentPrepend m b x) e) =
      assignmentPrepend n (compose B (termEvaluation L Δ m M b e)) x := by
  have hT := termEvaluation_mem_function hM hm Δ hb he
  have hT' := termEvaluation_mem_function hM (ω_succ_closed hm) Δ
    (assignmentPrepend_mem_function hm hb hx) he
  have hB' := liftBoundReplacement_mem hM.language hm hn hB
  apply function_eq_of_values (compose_function hB' hT')
    (assignmentPrepend_mem_function hn (compose_function hB hT) hx)
  intro i hi
  have hiω : i ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hi (ω_succ_closed hn)
  rcases internalNatural_cases hiω with rfl | ⟨j, hj, rfl⟩
  · rw [value_compose_of_mem_function hB' hT' hi, liftBoundReplacement_zero hn,
      termEvaluation_boundVar hM.language (ω_succ_closed hm) Δ M _ e (zero_mem_succ_natural hm),
      assignmentPrepend_zero hm, assignmentPrepend_zero hn]
  · have : IsOrdinal j := IsOrdinal.of_mem hj
    have hne : succ j ≠ (0 : V) := by
      intro h
      have hjj : j ∈ succ j := by simp
      rw [h] at hjj
      exact not_mem_empty hjj
    have hjn : j ∈ n := by
      simpa [sUnion_succ_of_transitive] using natural_predecessor_mem hn hi hne
    rw [value_compose_of_mem_function hB' hT' hi,
      liftBoundReplacement_succ hM.language hm hn hB hjn,
      termEvaluation_boundShift hM hm hb he hx (function_value_mem hB hjn),
      assignmentPrepend_succ hn hjn, value_compose_of_mem_function hB hT hjn]

theorem evaluate_liftFreeReplacement {L Γ Δ m M E b e x : V}
    (hM : IsStructureCode L M) (hm : m ∈ (ω : V))
    (hE : E ∈ termSet L Δ m ^ Γ) (hb : b ∈ structureDomain M ^ m)
    (he : e ∈ structureDomain M ^ Δ) (hx : x ∈ structureDomain M) :
    compose (liftFreeReplacement L Δ m E)
      (termEvaluation L Δ (succ m) M (assignmentPrepend m b x) e) =
      compose E (termEvaluation L Δ m M b e) := by
  have hT := termEvaluation_mem_function hM hm Δ hb he
  have hT' := termEvaluation_mem_function hM (ω_succ_closed hm) Δ
    (assignmentPrepend_mem_function hm hb hx) he
  have hE' := liftFreeReplacement_mem hM.language hm hE
  apply function_eq_of_values (compose_function hE' hT') (compose_function hE hT)
  intro y hy
  rw [value_compose_of_mem_function hE' hT' hy,
    liftFreeReplacement_value hM.language hm hE hy,
    termEvaluation_boundShift hM hm hb he hx (function_value_mem hE hy),
    value_compose_of_mem_function hE hT hy]

end ZFVP
