import ZFVP.SetTheory.PiWitnessRankStages
import ZFVP.Syntax.BoundedStandardTuples

/-! Bounded assembly of the least-witness tuple inside a transitive ambient set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedWitnessFamilyTupleFormula : SetTheorySemisentence 7 :=
  “A e ν U W X c. ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A,
    !boundedKpairFormula r X c ∧ !boundedKpairFormula q W r ∧
    !boundedKpairFormula p U q ∧ !boundedKpairFormula e ν p”

theorem boundedWitnessFamilyTupleFormula_bounded : IsBoundedSetFormula boundedWitnessFamilyTupleFormula :=
  .exs (.bvar 0) (.exs (.bvar 1) (.exs (.bvar 2)
    (.and (boundedKpairFormula_bounded.subst _) (.and (boundedKpairFormula_bounded.subst _)
      (.and (boundedKpairFormula_bounded.subst _) (boundedKpairFormula_bounded.subst _))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedWitnessFamilyTupleFormula {A e : V} [IsTransitive A] (he : e ∈ A)
    (ν U W X c : V) :
    boundedWitnessFamilyTupleFormula.Evalb ![A, e, ν, U, W, X, c] ↔
      e = ⟨ν, ⟨U, ⟨W, ⟨X, c⟩ₖ⟩ₖ⟩ₖ⟩ₖ := by
  simp [boundedWitnessFamilyTupleFormula]
  constructor
  · rintro ⟨_, _, _, he⟩
    exact he
  · intro heq
    rw [heq] at he
    have hp := (kpair_components_mem_transitive he).2
    have hq := (kpair_components_mem_transitive hp).2
    have hr := (kpair_components_mem_transitive hq).2
    exact ⟨hp, hq, hr, heq⟩

end ZFVP
