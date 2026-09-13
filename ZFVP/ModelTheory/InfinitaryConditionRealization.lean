import ZFVP.ModelTheory.InfinitaryConditionFreezing

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.FiniteCondition
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

theorem realizable (p : H.FiniteCondition) :
    ∃ b : Fin (1 + p.1) → H.Domain, Formula.WeakEval H.weakQuantifier p.2.formula b := by
  classical
  by_contra hn
  have hf := exsN_closed p.1 p.2.in_fragment
  have hq := (H.weakQuantifier_fiber hf).mpr p.2.large
  let x : H.Domain := Classical.choice inferInstance
  apply H.weakQuantifier_not_subset_twoPoints x x ?_ hq
  intro y hy
  rw [H.fiber_weakEval hf, Formula.weakEval_exsN_one_iff] at hy
  obtain ⟨b, _, hb⟩ := hy
  exact (hn ⟨b, hb⟩).elim

theorem not_forces_both (p : H.FiniteCondition) {n} {φ : Formula (limit L) n}
    (hp : Forces p φ) (hn : Forces p (.neg φ)) : False := by
  obtain ⟨b, hb⟩ := realizable p
  obtain ⟨h, hh⟩ := hp
  obtain ⟨g, hg⟩ := hn
  exact hg b hb (hh b hb)

/-- Every finite collection of forced formulas is jointly realized in the old model. -/
theorem finite_forced_realization (p : H.FiniteCondition) {I : Type*}
    (a : I → TaggedFormula (limit L)) (h : ∀ i, Forces p (a i).2) :
    ∃ b : Fin (1 + p.1) → H.Domain,
      ∀ i, ∃ hn : (a i).1 ≤ 1 + p.1,
        Formula.WeakEval H.weakQuantifier (a i).2 (b ∘ Formula.rightEmbed hn) := by
  obtain ⟨b, hb⟩ := realizable p
  refine ⟨b, ?_⟩
  intro i
  obtain ⟨hn, hh⟩ := h i
  exact ⟨hn, hh b hb⟩

end HenkinConstruction.FragmentExtension.FiniteCondition
end ZFVP.Infinitary
