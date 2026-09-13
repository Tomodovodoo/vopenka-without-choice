import ZFVP.Syntax.LiftSubstitution
import ZFVP.Syntax.TermEvaluation

/-! Substitution commutes with evaluation for every internal term. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem function_eq_of_values {A C f g : V} (hf : f ∈ C ^ A) (hg : g ∈ C ^ A)
    (h : ∀ x ∈ A, f ‘ x = g ‘ x) : f = g := by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsFunction g := IsFunction.of_mem hg
  apply function_ext hf hg
  intro x hx y _ hxy
  apply kpair_mem_iff_value.mpr
  exact ⟨by simpa [domain_eq_of_mem_function hg] using hx,
    (h x hx).symm.trans (value_eq_of_kpair_mem hxy)⟩

theorem termEvaluation_substitution {L Γ Δ n m M B E b e : V}
    (hM : IsStructureCode L M) (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hB : B ∈ termSet L Δ m ^ n) (hE : E ∈ termSet L Δ m ^ Γ)
    (hb : b ∈ structureDomain M ^ m) (he : e ∈ structureDomain M ^ Δ) :
    ∀ t ∈ termSet L Γ n,
      (termEvaluation L Δ m M b e) ‘ ((termSubstitution L Γ n B E) ‘ t) =
        (termEvaluation L Γ n M (compose B (termEvaluation L Δ m M b e))
          (compose E (termEvaluation L Δ m M b e))) ‘ t := by
  let T := termEvaluation L Δ m M b e
  let S := termSubstitution L Γ n B E
  let U := termEvaluation L Γ n M (compose B T) (compose E T)
  have hT : T ∈ structureDomain M ^ termSet L Δ m := termEvaluation_mem_function hM hm Δ hb he
  have hS : S ∈ termSet L Δ m ^ termSet L Γ n := termSubstitution_mem_function hM.language hn hm hB hE
  have hU : U ∈ structureDomain M ^ termSet L Γ n :=
    termEvaluation_mem_function hM hn Γ (compose_function hB hT) (compose_function hE hT)
  change (∀ t ∈ termSet L Γ n, (T) ‘ ((S) ‘ t) = (U) ‘ t)
  apply termSet_induction hM.language hn Γ (fun t ↦ (T) ‘ ((S) ‘ t) = (U) ‘ t) (by definability)
  · intro i hi
    change (T) ‘ ((termSubstitution L Γ n B E) ‘ (boundVarCode i)) =
      (termEvaluation L Γ n M (compose B T) (compose E T)) ‘ (boundVarCode i)
    rw [termSubstitution_boundVar hM.language hn Γ B E hi,
      termEvaluation_boundVar hM.language hn Γ M _ _ hi]
    exact (value_compose_of_mem_function hB hT hi).symm
  · intro x hx
    change (T) ‘ ((termSubstitution L Γ n B E) ‘ (freeVarCode x)) =
      (termEvaluation L Γ n M (compose B T) (compose E T)) ‘ (freeVarCode x)
    rw [termSubstitution_freeVar hM.language hn Γ B E hx,
      termEvaluation_freeVar hM.language hn Γ M _ _ hx]
    exact (value_compose_of_mem_function hE hT hx).symm
  · intro f hf args ha ih
    have ht := (termSet_closed hM.language hn Γ).2.2 f hf args ha
    have haS := compose_function ha hS
    have ht' := (termSet_closed hM.language hm Δ).2.2 f hf (compose args S) haS
    change (termEvaluation L Δ m M b e) ‘ ((termSubstitution L Γ n B E) ‘ (functionTermCode f args)) =
      (termEvaluation L Γ n M (compose B T) (compose E T)) ‘ (functionTermCode f args)
    rw [termSubstitution_function hM.language hn Γ B E ht,
      termEvaluation_function hM.language hm Δ M b e ht',
      termEvaluation_function hM.language hn Γ M _ _ ht]
    apply congrArg (fun a ↦ ((structureFunctions M) ‘ f) ‘ a)
    apply function_eq_of_values (compose_function haS hT) (compose_function ha hU)
    intro i hi
    rw [value_compose_of_mem_function haS hT hi,
      value_compose_of_mem_function ha hS hi, value_compose_of_mem_function ha hU hi]
    exact ih _ (mem_range_of_kpair_mem (by
      have : IsFunction args := IsFunction.of_mem ha
      exact kpair_value_mem (by simpa [domain_eq_of_mem_function ha] using hi)))

theorem termEvaluation_boundShift {L Γ n M b e x t : V}
    (hM : IsStructureCode L M) (hn : n ∈ (ω : V))
    (hb : b ∈ structureDomain M ^ n) (he : e ∈ structureDomain M ^ Γ)
    (hx : x ∈ structureDomain M) (ht : t ∈ termSet L Γ n) :
    (termEvaluation L Γ (succ n) M (assignmentPrepend n b x) e) ‘ ((termBoundShift L Γ n) ‘ t) =
      (termEvaluation L Γ n M b e) ‘ t := by
  let T := termEvaluation L Γ (succ n) M (assignmentPrepend n b x) e
  have hT : T ∈ structureDomain M ^ termSet L Γ (succ n) :=
    termEvaluation_mem_function hM (ω_succ_closed hn) Γ (assignmentPrepend_mem_function hn hb hx) he
  have hB := boundShiftReplacement_mem hM.language hn Γ
  have hE := freeIdentityReplacement_mem hM.language (ω_succ_closed hn) Γ
  have hBc : compose (boundShiftReplacement n) T = b := by
    apply function_eq_of_values (compose_function hB hT) hb
    intro i hi
    rw [value_compose_of_mem_function hB hT hi, boundShiftReplacement_value hi]
    exact (termEvaluation_boundVar hM.language (ω_succ_closed hn) Γ M _ e
      (succ_mem_succ_of_natural_mem hn hi)).trans (assignmentPrepend_succ hn hi b x)
  have hEc : compose (freeIdentityReplacement Γ) T = e := by
    apply function_eq_of_values (compose_function hE hT) he
    intro y hy
    rw [value_compose_of_mem_function hE hT hy, freeIdentityReplacement_value hy]
    exact termEvaluation_freeVar hM.language (ω_succ_closed hn) Γ M _ e hy
  have h := termEvaluation_substitution hM hn (ω_succ_closed hn) hB hE
    (assignmentPrepend_mem_function hn hb hx) he t ht
  change (T) ‘ ((termBoundShift L Γ n) ‘ t) = _
  change (T) ‘ ((termBoundShift L Γ n) ‘ t) =
    (termEvaluation L Γ n M (compose (boundShiftReplacement n) T) (compose (freeIdentityReplacement Γ) T)) ‘ t at h
  rwa [hBc, hEc] at h

end ZFVP
