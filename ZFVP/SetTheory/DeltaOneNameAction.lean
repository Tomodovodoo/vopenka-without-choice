import ZFVP.SetTheory.BoundedNameAction
import ZFVP.SetTheory.DeltaOneNameClosure
import ZFVP.Syntax.SigmaOneBoundedModelTruth

/-! Name action has both Sigma_1 answers on names and condition functions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def nameActionAnswerEntryFormula (answer : Bool) : SetTheorySemisentence 4 :=
  if answer then “T f τ y. !boundedPairMemberFormula f τ y”
  else “T f τ y. ∃ z ∈ T, !boundedPairMemberFormula f τ z ∧ z ≠ y”

def sigmaOneNameActionFormula (answer : Bool) : SetTheorySemisentence 4 :=
  “P π τ y. ∃ C, ∃ T, ∃ f, !sigmaOneNameClosureFormula C τ ∧
    !boundedNameActionTableFormula P π C T f ∧ !(nameActionAnswerEntryFormula answer) T f τ y”

def piOneNameActionFormula : SetTheorySemisentence 4 := ∼sigmaOneNameActionFormula false

theorem nameActionAnswerEntryFormula_bounded (answer : Bool) :
    IsBoundedSetFormula (nameActionAnswerEntryFormula answer) := by
  cases answer
  · exact .exs (.bvar 0) (.and (boundedPairMemberFormula_bounded.subst _) (.nrel _ _))
  · exact boundedPairMemberFormula_bounded.subst _

theorem sigmaOneNameActionFormula_sigmaOne (answer : Bool) : IsSigmaFormula 1 (sigmaOneNameActionFormula answer) :=
  .exs (.exs (.exs (.and (sigmaOneNameClosureFormula_sigmaOne.subst _)
    (.and (.bounded (boundedNameActionTableFormula_bounded.subst _))
      (.bounded ((nameActionAnswerEntryFormula_bounded answer).subst _))))))

theorem piOneNameActionFormula_piOne : IsPiFormula 1 piOneNameActionFormula :=
  (sigmaOneNameActionFormula_sigmaOne false).neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_nameActionAnswerEntryFormula {C T f τ : V} (hf : f ∈ T ^ C) (hτ : τ ∈ C)
    (answer : Bool) (y : V) : (nameActionAnswerEntryFormula answer).Evalb ![T, f, τ, y] ↔
      TruthAnswer answer (y = f ‘ τ) := by
  let := IsFunction.of_mem hf
  cases answer
  · simp only [nameActionAnswerEntryFormula, Bool.false_eq_true, reduceIte]
    simp
    rw [exists_function_pair_value_iff hf hτ]
    exact ne_comm
  · simp [nameActionAnswerEntryFormula, TruthAnswer]
    exact ⟨fun h ↦ (value_eq_of_kpair_mem h).symm, fun h ↦ h ▸
      kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using hτ)⟩

theorem eval_sigmaOneNameActionFormula {P π τ : V} (hπ : π ∈ P ^ P) (hτ : IsForcingName P τ)
    (answer : Bool) (y : V) : (sigmaOneNameActionFormula answer).Evalb ![P, π, τ, y] ↔
      TruthAnswer answer (y = nameAction π τ) := by
  have he : (sigmaOneNameActionFormula answer).Evalb ![P, π, τ, y] ↔
      ∃ T f, IsNameActionTable P π (nameClosure τ) T f ∧
        (nameActionAnswerEntryFormula answer).Evalb ![T, f, τ, y] := by
    simp [sigmaOneNameActionFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, eval_boundedNameActionTableFormula hπ]
  rw [he]
  constructor
  · rintro ⟨T, f, hf, he⟩
    rw [eval_nameActionAnswerEntryFormula hf.1 (mem_nameClosure_self τ)] at he
    exact (hf.correct (nameClosure_closed τ) (fun _ h ↦ forcingName_mem_closure hτ h)
      τ (mem_nameClosure_self τ)) ▸ he
  · intro he
    obtain ⟨T, f, hf⟩ := nameActionTable_exists P π (nameClosure τ) (nameClosure_closed τ)
      (fun _ h ↦ forcingName_mem_closure hτ h)
    refine ⟨T, f, hf, (eval_nameActionAnswerEntryFormula hf.1 (mem_nameClosure_self τ) answer y).mpr ?_⟩
    rwa [hf.correct (nameClosure_closed τ) (fun _ h ↦ forcingName_mem_closure hτ h) τ (mem_nameClosure_self τ)]

theorem eval_piOneNameActionFormula {P π τ : V} (hπ : π ∈ P ^ P) (hτ : IsForcingName P τ) (y : V) :
    piOneNameActionFormula.Evalb ![P, π, τ, y] ↔ y = nameAction π τ := by
  simp [piOneNameActionFormula, eval_sigmaOneNameActionFormula hπ hτ, TruthAnswer]

end ZFVP
