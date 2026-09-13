import ZFVP.SetTheory.BoundedCheckNames
import ZFVP.SetTheory.DeltaOneNameAction

/-! The canonical check-name operation has two existential bounded certificates. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneCheckNameFormula (answer : Bool) : SetTheorySemisentence 3 :=
  “one x y. ∃ C, ∃ T, ∃ f, !IsTransitive.dfn C ∧ x ∈ C ∧
    !boundedCheckNameTableFormula one C T f ∧ !(nameActionAnswerEntryFormula answer) T f x y”

def piOneCheckNameFormula : SetTheorySemisentence 3 := ∼sigmaOneCheckNameFormula false

theorem sigmaOneCheckNameFormula_sigmaOne (answer : Bool) : IsSigmaFormula 1 (sigmaOneCheckNameFormula answer) :=
  .exs (.exs (.exs (.and (.bounded (isTransitiveFormula_bounded.subst _))
    (.and (.bounded (.rel _ _)) (.and (.bounded (boundedCheckNameTableFormula_bounded.subst _))
      (.bounded ((nameActionAnswerEntryFormula_bounded answer).subst _)))))))

theorem piOneCheckNameFormula_piOne : IsPiFormula 1 piOneCheckNameFormula :=
  (sigmaOneCheckNameFormula_sigmaOne false).neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneCheckNameFormula (answer : Bool) (one x y : V) :
    (sigmaOneCheckNameFormula answer).Evalb ![one, x, y] ↔ TruthAnswer answer (y = checkName one x) := by
  have he : (sigmaOneCheckNameFormula answer).Evalb ![one, x, y] ↔
      ∃ C T f : V, IsTransitive C ∧ x ∈ C ∧ boundedCheckNameTableFormula.Evalb ![one, C, T, f] ∧
        (nameActionAnswerEntryFormula answer).Evalb ![T, f, x, y] := by
    simp [sigmaOneCheckNameFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def]
  rw [he]
  constructor
  · rintro ⟨C, T, f, hC, hx, htable, hentry⟩
    let := hC
    have hf := (eval_boundedCheckNameTableFormula one C T f).mp htable
    rw [eval_nameActionAnswerEntryFormula hf.1 hx, hf.correct x hx] at hentry
    exact hentry
  · intro h
    let C := transitiveClosure ({x} : V)
    have hC : IsTransitive C := transitiveClosure_transitive _
    let := hC
    have hx : x ∈ C := subset_transitiveClosure _ _ (by simp)
    obtain ⟨T, f, hf⟩ := checkNameTable_exists one C
    refine ⟨C, T, f, hC, hx, (eval_boundedCheckNameTableFormula one C T f).mpr hf, ?_⟩
    rw [eval_nameActionAnswerEntryFormula hf.1 hx, hf.correct x hx]
    exact h

theorem eval_piOneCheckNameFormula (one x y : V) :
    piOneCheckNameFormula.Evalb ![one, x, y] ↔ y = checkName one x := by
  simp [piOneCheckNameFormula, eval_sigmaOneCheckNameFormula, TruthAnswer]

end ZFVP
