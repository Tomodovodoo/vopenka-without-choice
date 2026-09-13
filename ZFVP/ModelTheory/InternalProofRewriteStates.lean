import ZFVP.ModelTheory.InternalProofRewriteVariables
import ZFVP.Syntax.TermSubstitutionSemantics

/-! Valid internal substitution states for free-variable shift, eigenvariable opening, and witnesses. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def proofRewriteSource (s d : V) : V := by
  classical
  exact if s = 0 then d else succ d

instance proofRewriteSource_definable : ℒₛₑₜ-function₂[V] proofRewriteSource := by
  have h : ℒₛₑₜ-relation₃ (fun n s d : V ↦ (s = 0 ∧ n = d) ∨ (s ≠ 0 ∧ n = succ d)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = proofRewriteSource (v 1) (v 2) ↔ _
  unfold proofRewriteSource
  split <;> simp_all

theorem proofRewriteSource_natural (s : V) {d : V} (hd : d ∈ (ω : V)) :
    proofRewriteSource s d ∈ (ω : V) := by
  unfold proofRewriteSource
  split
  · exact hd
  · exact ω_succ_closed hd

@[simp] theorem proofRewriteSource_succ (s d : V) :
    proofRewriteSource s (succ d) = succ (proofRewriteSource s d) := by
  unfold proofRewriteSource
  split <;> rfl

noncomputable def proofRewriteBoundTable (s d : V) : V :=
  definableGraph (proofRewriteSource s d)
    (fun i ↦ naturalProofRewriteTerm s d (succ (naturalSquarePair 0 i))) (by definability)

instance proofRewriteBoundTable_definable : ℒₛₑₜ-function₂[V] proofRewriteBoundTable := by
  have h : ℒₛₑₜ-relation₃ (fun B s d : V ↦ ∀ p, p ∈ B ↔
      ∃ i ∈ proofRewriteSource s d, p = ⟨i, naturalProofRewriteTerm s d (succ (naturalSquarePair 0 i))⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = proofRewriteBoundTable (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [proofRewriteBoundTable, mem_definableGraph_iff]

theorem proofRewriteBoundTable_value {s d i : V} (hi : i ∈ proofRewriteSource s d) :
    (proofRewriteBoundTable s d) ‘ i = naturalProofRewriteTerm s d (succ (naturalSquarePair 0 i)) :=
  value_definableGraph _ _ _ hi

theorem naturalProofRewriteTerm_bound_mem {s d i : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hi : i ∈ proofRewriteSource s d) :
    naturalProofRewriteTerm s d (succ (naturalSquarePair 0 i)) ∈ termSet membershipLanguageCode ω d := by
  classical
  by_cases hs0 : s = 0
  · have hi' : i ∈ d := by simpa only [proofRewriteSource, hs0, ite_true] using hi
    rw [naturalProofRewriteTerm_bound_below hs hd hi']
    exact (termSet_closed membershipLanguageCode_valid hd _).1 _ hi'
  · have hi' : i ∈ succ d := by simpa only [proofRewriteSource, hs0, ite_false] using hi
    rcases mem_succ_iff.mp hi' with rfl | hi'
    · rw [naturalProofRewriteTerm_bound_edge hs hd hs0]
      exact (termSet_closed membershipLanguageCode_valid hd _).2.1 _ (evalSet_natural _ hs)
    · rw [naturalProofRewriteTerm_bound_below hs hd hi']
      exact (termSet_closed membershipLanguageCode_valid hd _).1 _ hi'

theorem proofRewriteBoundTable_mem {s d : V} (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) :
    proofRewriteBoundTable s d ∈ termSet membershipLanguageCode ω d ^ proofRewriteSource s d :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hi ↦ naturalProofRewriteTerm_bound_mem hs hd hi)

theorem proofRewriteFreeTable_mem {s d : V} (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) :
    proofRewriteVariableTable s d 1 ∈ termSet membershipLanguageCode ω d ^ (ω : V) := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  rw [naturalProofRewriteTerm_free hs hd hi]
  exact (termSet_closed membershipLanguageCode_valid hd _).2.1 _
    (evalSet_natural _ (naturalSquarePair_natural hs hi))

noncomputable def proofRewriteState (s d : V) : V :=
  substitutionState (proofRewriteSource s d) d (proofRewriteBoundTable s d) (proofRewriteVariableTable s d 1)

@[simp] theorem stateSource_proofRewriteState (s d : V) :
    stateSource (proofRewriteState s d) = proofRewriteSource s d := stateSource_code _ _ _ _

@[simp] theorem stateTarget_proofRewriteState (s d : V) :
    stateTarget (proofRewriteState s d) = d := stateTarget_code _ _ _ _

@[simp] theorem stateBound_proofRewriteState (s d : V) :
    stateBound (proofRewriteState s d) = proofRewriteBoundTable s d := stateBound_code _ _ _ _

@[simp] theorem stateFree_proofRewriteState (s d : V) :
    stateFree (proofRewriteState s d) = proofRewriteVariableTable s d 1 := stateFree_code _ _ _ _

instance proofRewriteState_definable : ℒₛₑₜ-function₂[V] proofRewriteState := by
  unfold proofRewriteState
  definability

theorem proofRewriteState_valid {s d : V} (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) :
    IsSubstitutionState membershipLanguageCode ω ω (proofRewriteState s d) := by
  simp only [proofRewriteState, IsSubstitutionState, stateSource_code, stateTarget_code, stateBound_code, stateFree_code]
  exact ⟨proofRewriteSource_natural s hd, hd, proofRewriteBoundTable_mem hs hd, proofRewriteFreeTable_mem hs hd⟩

end ZFVP
