import PalomarBridge.InternalEvaluationDictionary
import ZFVP.SetTheory.VopenkaScheme

namespace PalomarBridge
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {M : Type u} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "mem" => (fun x y : M => x ∈ y)

@[simp] theorem coding_prependValue (b x i : M) :
    Coding.prependValue mem b x i = ZFVP.prependValue b x i := by
  unfold Coding.prependValue
  rw [coding_numeral]
  simp [ZFVP.prependValue]

@[simp] theorem coding_prepend (n b x : M) :
    Coding.prepend mem n b x = ZFVP.assignmentPrepend n b x := by
  apply setValue_eq
  simp [ZFVP.assignmentPrepend, ZFVP.mem_definableGraph_iff]

@[simp] theorem coding_immediateSubformula (s t : M) :
    Coding.ImmediateSubformula mem s t ↔ ZFVP.IsImmediateSubformula s t := by
  simp [Coding.ImmediateSubformula, ZFVP.IsImmediateSubformula]

@[simp] theorem coding_subformulas (F : M) :
    Coding.subformulas mem F = ZFVP.subformulaRelation F := by
  apply setValue_eq
  intro p
  simp only [ZFVP.subformulaRelation, mem_sep_iff, mem_prod_iff, coding_pair,
    coding_immediateSubformula]
  constructor
  · rintro ⟨⟨s, hs, t, ht, rfl⟩, h⟩
    exact ⟨s, t, rfl, hs, ht, by simpa using h⟩
  · rintro ⟨s, t, rfl, hs, ht, h⟩
    exact ⟨⟨s, hs, t, ht, rfl⟩, by simpa using h⟩

@[simp] theorem coding_satisfactionStep {L p : M} (hL : ZFVP.IsLanguageCode L)
    (hp : kpair.π₁ p ∈ (ω : M)) (S previous b : M) :
    Coding.SatisfactionStep mem L S p previous b ↔
      ZFVP.SatisfactionStepHolds L ∅ S ∅ p previous b := by
  simp [Coding.SatisfactionStep, ZFVP.SatisfactionStepHolds, coding_atomicHolds hL hp]

theorem coding_satisfactionGraph {L : M} (hL : ZFVP.IsLanguageCode L) (S g : M) :
    Coding.SatisfactionGraph mem L S g ↔ ZFVP.IsSatisfactionGraph L ∅ S ∅ g := by
  simp only [Coding.SatisfactionGraph, ZFVP.IsSatisfactionGraph, coding_isFunction,
    coding_domain, coding_formulas hL, coding_value, coding_structureDomain,
    coding_first, coding_functions, coding_subformulas, coding_predecessors, coding_restrict]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  have hn : kpair.π₁ p ∈ (ω : M) := by
    obtain ⟨n, hn, q, rfl⟩ := ZFVP.formulaFamily_context hL ∅ hp
    simpa using hn
  apply forall_congr'
  intro b
  rw [coding_satisfactionStep hL hn]

@[simp] theorem coding_satisfaction {L : M} (hL : ZFVP.IsLanguageCode L) (S : M) :
    Coding.satisfaction mem L S = ZFVP.satisfactionGraph L ∅ S ∅ := by
  have he : ∃ g : M, Coding.SatisfactionGraph mem L S g :=
    ⟨_, (coding_satisfactionGraph hL S _).mpr (ZFVP.satisfactionGraph_eq_iff _ _ _ _ _ |>.mp rfl)⟩
  have hs := (coding_satisfactionGraph hL S _).mp (Classical.epsilon_spec he)
  exact (ZFVP.satisfactionGraph_eq_iff _ _ _ _ _ |>.mpr hs).symm

@[simp] theorem coding_holds {L : M} (hL : ZFVP.IsLanguageCode L) (S n p b : M) :
    Coding.Holds mem L S n p b ↔ ZFVP.Satisfies L ∅ S ∅ n p b := by
  simp [Coding.Holds, ZFVP.Satisfies, coding_satisfaction hL]

@[simp] theorem coding_elementary (L S T f : M) :
    Coding.Elementary mem L S T f ↔ ZFVP.IsCodedElementaryEmbedding L S T f := by
  simp only [Coding.Elementary, ZFVP.IsCodedElementaryEmbedding, coding_isStructure,
    coding_structureDomain, coding_functions, coding_omega, coding_pair, coding_compose]
  constructor
  · rintro ⟨hS, hT, hf, h⟩
    refine ⟨hS, hT, hf, ?_⟩
    intro n hn p hp b hb
    have hp' : ⟨n, p⟩ₖ ∈ Coding.formulas mem L := by
      simpa [coding_formulas hS.language] using (ZFVP.mem_formulaSet_iff _ _ _ _).mp hp
    simpa [coding_holds hS.language] using h n hn p hp' b hb
  · rintro ⟨hS, hT, hf, h⟩
    refine ⟨hS, hT, hf, ?_⟩
    intro n hn p hp b hb
    have hp' : p ∈ ZFVP.formulaSet L ∅ n := by
      apply (ZFVP.mem_formulaSet_iff _ _ _ _).mpr
      simpa [coding_formulas hS.language] using hp
    simpa [coding_holds hS.language] using h n hn p hp' b hb

/-- The independent VP definition is exactly the full imported VP scheme. -/
theorem coding_vopenka_iff :
    Coding.Vopenka mem ↔ ∀ p : SetTheorySemisentence 2, ZFVP.VopenkaInstance (V := M) p := by
  have realization (p : SetTheorySemisentence 2) (S a : M) :
      (fromFoundation p).Realize mem ![S, a] ↔ p.Evalb ![S, a] := by
    simpa using (realize_toFoundation (fromFoundation p) ![S, a]).symm
  constructor
  · intro h p
    simpa [Coding.Vopenka, ZFVP.VopenkaInstance, ZFVP.IsProperClass,
      realization, coding_isStructure, coding_elementary] using h (fromFoundation p)
  · intro h p
    simpa [ZFVP.VopenkaInstance, ZFVP.IsProperClass, realize_toFoundation,
      coding_isStructure, coding_elementary] using h p.toFoundation

end PalomarBridge

