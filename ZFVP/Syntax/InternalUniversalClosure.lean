import ZFVP.SetTheory.UniformParameterizedRecursion
import ZFVP.SetTheory.NaturalAddition
import ZFVP.Syntax.UniformFormulaCodes
import ZFVP.Syntax.UniformSatisfaction
import ZFVP.ModelTheory.CodedSequentQuantifiers

/-! Universal closure by any internal finite number of quantifiers. Its
semantics quantifies over every internal assignment, not just standard tuples. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def internalAllClosureStepFormula : SetTheorySemisentence 3 :=
  f“r φ g. (!domain.dfn g = !isEmpty ∧ r = φ) ∨
    (!domain.dfn g ≠ !isEmpty ∧ r = !allCodeFormula (!value.dfn g (!sUnion.dfn (!domain.dfn g))))”

def internalAllClosureFormula : SetTheorySemisentence 3 :=
  parameterRecursionFormula internalAllClosureStepFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def internalAllClosureStep (φ g : V) : V := by
  classical
  exact if domain g = ∅ then φ else allCode (g ‘ (⋃ˢ domain g))

instance internalAllClosureStep_defined :
    ℒₛₑₜ-function₂[V] internalAllClosureStep via internalAllClosureStepFormula :=
  ⟨fun v ↦ by
    by_cases h : domain (v 2) = ∅
    · simp [internalAllClosureStepFormula, internalAllClosureStep, h]
    · simp [internalAllClosureStepFormula, internalAllClosureStep, h, -ne_empty_iff_isNonempty]⟩

instance internalAllClosureStep_definable : ℒₛₑₜ-function₂[V] internalAllClosureStep :=
  internalAllClosureStep_defined.to_definable

noncomputable def internalAllClosureCode (φ n : V) : V :=
  parameterRecursion internalAllClosureStep internalAllClosureStep_definable φ n

instance internalAllClosureCode_defined :
    ℒₛₑₜ-function₂[V] internalAllClosureCode via internalAllClosureFormula :=
  parameterRecursionFormula_defined internalAllClosureStep internalAllClosureStepFormula

instance internalAllClosureCode_definable : ℒₛₑₜ-function₂[V] internalAllClosureCode :=
  internalAllClosureCode_defined.to_definable

theorem internalAllClosureCode_zero (φ : V) : internalAllClosureCode φ 0 = φ := by
  have h := Replacement.transfiniteRec_spec (internalAllClosureStep φ) (by definability)
    (IsOrdinal.toOrdinal (0 : V))
  change internalAllClosureCode φ 0 = internalAllClosureStep φ
    (definableGraph 0 (internalAllClosureCode φ) (by definability)) at h
  simpa only [internalAllClosureStep, domain_definableGraph, zero_def, ite_true] using h

theorem internalAllClosureCode_succ (φ : V) {n : V} (hn : n ∈ (ω : V)) :
    internalAllClosureCode φ (succ n) = allCode (internalAllClosureCode φ n) := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have h := Replacement.transfiniteRec_spec (internalAllClosureStep φ) (by definability)
    (IsOrdinal.toOrdinal (succ n))
  change internalAllClosureCode φ (succ n) = internalAllClosureStep φ
    (definableGraph (succ n) (internalAllClosureCode φ) (by definability)) at h
  have hne : succ n ≠ (∅ : V) := by
    intro he
    exact not_mem_empty (he ▸ mem_succ_self n)
  simpa only [internalAllClosureStep, domain_definableGraph, hne, ite_false,
    sUnion_succ_of_transitive, value_definableGraph _ _ _ (mem_succ_self n)] using h

theorem assignmentPrepend_successorIndices {D n b : V} (hn : n ∈ (ω : V))
    (hb : b ∈ D ^ succ n) :
    assignmentPrepend n (compose (successorIndices n) b) (b ‘ (0 : V)) = b := by
  have ht := compose_function (successorIndices_function hn) hb
  have hx := function_value_mem hb (zero_mem_succ_natural hn)
  apply function_eq_of_values (assignmentPrepend_mem_function hn ht hx) hb
  intro i hi
  have hiω : i ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hi (ω_succ_closed hn)
  rcases internalNatural_cases hiω with rfl | ⟨j, hj, rfl⟩
  · exact assignmentPrepend_zero hn _ _
  · have : IsOrdinal j := IsOrdinal.of_mem hj
    have hne : succ j ≠ (0 : V) := by
      intro he
      exact not_mem_empty (he ▸ mem_succ_self j)
    have hjn : j ∈ n := by
      simpa only [sUnion_succ_of_transitive] using natural_predecessor_mem hn hi hne
    rw [assignmentPrepend_succ hn hjn,
      value_compose_of_mem_function (successorIndices_function hn) hb hjn,
      show (successorIndices n) ‘ j = succ j from value_definableGraph _ _ _ hjn]

theorem all_assignments_allCode_iff {L Γ M e n φ : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L Γ (succ n)) :
    (∀ b ∈ structureDomain M ^ n, Satisfies L Γ M e n (allCode φ) b) ↔
      ∀ b ∈ structureDomain M ^ succ n, Satisfies L Γ M e (succ n) φ b := by
  constructor
  · intro h b hb
    have ht := compose_function (successorIndices_function hn) hb
    have hx := function_value_mem hb (zero_mem_succ_natural hn)
    have hs := (satisfies_all hL hn hφ ht).mp (h _ ht) _ hx
    rwa [assignmentPrepend_successorIndices hn hb] at hs
  · intro h b hb
    exact (satisfies_all hL hn hφ hb).mpr (fun x hx ↦ h _ (assignmentPrepend_mem_function hn hb hx))

private theorem add_succ_interchange {n k : V} (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) :
    ordinalAdd (succ n) k = ordinalAdd n (succ k) := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal k := IsOrdinal.of_mem hk
  rw [ordinalAdd_succ_left_natural hn hk, ordinalAdd_succ]

theorem internalAllClosureCode_valid {L Γ k n φ : V} (hL : IsLanguageCode L)
    (hk : k ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ (ordinalAdd n k)) :
    internalAllClosureCode φ k ∈ formulaSet L Γ n := by
  have H : ∀ k ∈ (ω : V), ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet L Γ (ordinalAdd n k),
      internalAllClosureCode φ k ∈ formulaSet L Γ n := by
    apply naturalNumber_induction (fun k ↦ ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet L Γ (ordinalAdd n k),
      internalAllClosureCode φ k ∈ formulaSet L Γ n) (by definability)
    · intro n hn φ hφ
      rw [internalAllClosureCode_zero]
      simpa only [zero_def, ordinalAdd_zero] using hφ
    · intro k hk ih n hn φ hφ
      rw [internalAllClosureCode_succ φ hk]
      apply (formulaSet_quantifiers hL hn ?_).1
      exact ih (succ n) (ω_succ_closed hn) φ ((add_succ_interchange hn hk).symm ▸ hφ)
  exact H k hk n hn φ hφ

theorem internalAllClosureCode_all_assignments_iff {L Γ M e k n φ : V}
    (hL : IsLanguageCode L) (hk : k ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ (ordinalAdd n k)) :
    (∀ b ∈ structureDomain M ^ n, Satisfies L Γ M e n (internalAllClosureCode φ k) b) ↔
      ∀ b ∈ structureDomain M ^ ordinalAdd n k, Satisfies L Γ M e (ordinalAdd n k) φ b := by
  have H : ∀ k ∈ (ω : V), ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet L Γ (ordinalAdd n k),
      (∀ b ∈ structureDomain M ^ n, Satisfies L Γ M e n (internalAllClosureCode φ k) b) ↔
        ∀ b ∈ structureDomain M ^ ordinalAdd n k, Satisfies L Γ M e (ordinalAdd n k) φ b := by
    apply naturalNumber_induction (fun k ↦ ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet L Γ (ordinalAdd n k),
      (∀ b ∈ structureDomain M ^ n, Satisfies L Γ M e n (internalAllClosureCode φ k) b) ↔
        ∀ b ∈ structureDomain M ^ ordinalAdd n k, Satisfies L Γ M e (ordinalAdd n k) φ b) (by definability)
    · intro n hn φ hφ
      rw [internalAllClosureCode_zero]
      simp only [zero_def, ordinalAdd_zero]
    · intro k hk ih n hn φ hφ
      have hφ' : φ ∈ formulaSet L Γ (ordinalAdd (succ n) k) := (add_succ_interchange hn hk).symm ▸ hφ
      rw [internalAllClosureCode_succ φ hk,
        all_assignments_allCode_iff hL hn (internalAllClosureCode_valid hL hk (ω_succ_closed hn) hφ'),
        ih (succ n) (ω_succ_closed hn) φ hφ', add_succ_interchange hn hk]
  exact H k hk n hn φ hφ

theorem internalAllClosureCode_sentence_valid {L Γ n φ : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L Γ n) :
    internalAllClosureCode φ n ∈ formulaSet L Γ 0 :=
  internalAllClosureCode_valid hL hn (by simp)
    ((ordinalAdd_zero_left_natural hn).symm ▸ hφ)

theorem internalAllClosureCode_satisfies_iff {L Γ M e n φ : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L Γ n) :
    Satisfies L Γ M e 0 (internalAllClosureCode φ n) ∅ ↔
      ∀ b ∈ structureDomain M ^ n, Satisfies L Γ M e n φ b := by
  have h := internalAllClosureCode_all_assignments_iff (M := M) (e := e) hL hn (by simp)
    ((ordinalAdd_zero_left_natural hn).symm ▸ hφ)
  rw [ordinalAdd_zero_left_natural hn] at h
  have he : (∅ : V) ∈ structureDomain M ^ (0 : V) := by simp [mem_function_iff, zero_def]
  constructor
  · intro hs
    apply h.mp
    intro b hb
    have hb0 : b = (∅ : V) := by
      apply function_eq_of_values hb he
      intro i hi
      exact False.elim (not_mem_empty hi)
    simpa only [hb0] using hs
  · intro hs
    exact (h.mpr hs) ∅ he

end ZFVP
