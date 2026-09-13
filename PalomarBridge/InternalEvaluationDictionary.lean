import PalomarBridge.InternalSyntaxDictionary
import ZFVP.Syntax.SatisfactionDefinability

namespace PalomarBridge
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {M : Type u} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "mem" => (fun x y : M => x ∈ y)

@[simp] theorem coding_predecessors (R D x : M) :
    Coding.predecessors mem R D x = ZFVP.predecessors R D x := by
  apply setValue_eq
  simp

@[simp] theorem coding_subterms (T : M) : Coding.subterms mem T = ZFVP.subtermRelation T := by
  apply setValue_eq
  intro p
  simp only [ZFVP.subtermRelation, mem_sep_iff, mem_prod_iff, coding_pair,
    coding_functionTerm, coding_range]
  constructor
  · rintro ⟨⟨s, hs, t, ht, rfl⟩, h⟩
    exact ⟨s, t, rfl, hs, ht, by simpa using h⟩
  · rintro ⟨s, t, rfl, hs, ht, h⟩
    exact ⟨⟨s, hs, t, ht, rfl⟩, by simpa using h⟩

@[simp] theorem coding_termStep (S b t previous : M) :
    Coding.termStep mem S b t previous = ZFVP.termEvaluationStep S b ∅ t previous := by
  unfold Coding.termStep
  rw [coding_first, coding_numeral, coding_numeral]
  simp [ZFVP.termEvaluationStep]

theorem coding_termEvaluationGraph {L n : M} (hL : ZFVP.IsLanguageCode L)
    (hn : n ∈ (ω : M)) (S b g : M) :
    Coding.TermEvaluationGraph mem L n S b g ↔
      ZFVP.termEvaluation L ∅ n S b ∅ = g := by
  rw [ZFVP.termEvaluation_eq_iff]
  simp only [Coding.TermEvaluationGraph, coding_isFunction, coding_domain, coding_terms hL hn,
    coding_value, coding_subterms, coding_predecessors, coding_restrict, coding_termStep]
  constructor
  · rintro ⟨hf, hd, hrec⟩
    refine ⟨⟨hf, ⟨?_, ?_⟩, ?_⟩, hd⟩
    · rw [hd]
    · intro x hx y hy
      rw [hd]
      exact (ZFVP.mem_predecessors_iff _ _ _ _).mp hy |>.1
    · intro x hx
      exact hrec x (hd ▸ hx)
  · rintro ⟨⟨hf, _, hrec⟩, hd⟩
    exact ⟨hf, hd, fun x hx => hrec x (hd.symm ▸ hx)⟩

@[simp] theorem coding_termEvaluation {L n : M} (hL : ZFVP.IsLanguageCode L)
    (hn : n ∈ (ω : M)) (S b : M) :
    Coding.termEvaluation mem L n S b = ZFVP.termEvaluation L ∅ n S b ∅ := by
  have he : ∃ g : M, Coding.TermEvaluationGraph mem L n S b g :=
    ⟨_, (coding_termEvaluationGraph hL hn S b _).mpr rfl⟩
  exact ((coding_termEvaluationGraph hL hn S b _).mp (Classical.epsilon_spec he)).symm

@[simp] theorem coding_evaluatedArguments {L n : M} (hL : ZFVP.IsLanguageCode L)
    (hn : n ∈ (ω : M)) (S b args : M) :
    Coding.evaluatedArguments mem L S n b args = ZFVP.evaluatedArguments L ∅ S ∅ n b args := by
  simp [Coding.evaluatedArguments, coding_termEvaluation hL hn, ZFVP.evaluatedArguments,
    ZFVP.evaluateWithFreeAssignment]

@[simp] theorem coding_atomicHolds {L n : M} (hL : ZFVP.IsLanguageCode L)
    (hn : n ∈ (ω : M)) (S b r args : M) :
    Coding.AtomicHolds mem L S n b r args ↔ ZFVP.AtomicHolds L ∅ S ∅ n b r args := by
  simp [Coding.AtomicHolds, coding_evaluatedArguments hL hn, ZFVP.AtomicHolds,
    ZFVP.equalityToken, ZFVP.relationToken]

end PalomarBridge


