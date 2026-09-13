import ZFVP.ModelTheory.InfinitaryProjectedSequenceDensity
import ZFVP.ModelTheory.InfinitaryQInterchangeDensity

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  (H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S)))

/-- A finite tuple condition with Q-many possible values of its last coordinate. -/
structure LargeCondition (n : ℕ) where
  formula : Formula (limit L) (1 + n)
  in_fragment : ⟨1 + n, formula⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)
  large : .q (Formula.exsN n formula) ∈ H.carrier

namespace LargeCondition
variable {H}

def SameLevelRefines {n} (p q : H.LargeCondition n) : Prop :=
  ∀ b : Fin (1 + n) → H.Domain,
    Formula.WeakEval H.weakQuantifier q.formula b → Formula.WeakEval H.weakQuantifier p.formula b

def NextLevelRefines {n} (p : H.LargeCondition n) (q : H.LargeCondition (n + 1)) : Prop :=
  ∀ b : Fin (1 + (n + 1)) → H.Domain,
    Formula.WeakEval H.weakQuantifier q.formula b →
      Formula.WeakEval H.weakQuantifier p.formula (fun i ↦ b i.succ)

theorem decide {n} (p : H.LargeCondition n) {ψ : Formula (limit L) (1 + n)}
    (hψ : ⟨1 + n, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    ∃ q : H.LargeCondition n, SameLevelRefines p q ∧
      (q.formula = p.formula.and ψ ∨ q.formula = p.formula.and (.neg ψ)) := by
  rcases H.q_mem_projected_split n p.in_fragment hψ p.large with hp | hn
  · refine ⟨⟨p.formula.and ψ, and_closed p.in_fragment hψ, hp⟩, ?_, Or.inl rfl⟩
    intro b hb
    exact (Formula.weakEval_and _ _ _ _).mp hb |>.1
  · refine ⟨⟨p.formula.and (.neg ψ), and_closed p.in_fragment (neg_closed hψ), hn⟩, ?_, Or.inr rfl⟩
    intro b hb
    exact (Formula.weakEval_and _ _ _ _).mp hb |>.1

theorem conjunction {n} (p : H.LargeCondition n) {f : ℕ → Formula (limit L) (1 + n)}
    (hf : ⟨1 + n, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    ∃ q : H.LargeCondition n, SameLevelRefines p q ∧
      (q.formula = p.formula.and (.conj f) ∨ ∃ i, q.formula = p.formula.and (.neg (f i))) := by
  rcases H.q_mem_projected_conjunction_split n p.in_fragment hf p.large with hp | ⟨i, hn⟩
  · refine ⟨⟨p.formula.and (.conj f), and_closed p.in_fragment hf, hp⟩, ?_, Or.inl rfl⟩
    intro b hb
    exact (Formula.weakEval_and _ _ _ _).mp hb |>.1
  · refine ⟨⟨p.formula.and (.neg (f i)),
        and_closed p.in_fragment (neg_closed (sequence_member_closed hf i)), hn⟩, ?_, Or.inr ⟨i, rfl⟩⟩
    intro b hb
    exact (Formula.weakEval_and _ _ _ _).mp hb |>.1

theorem witness_large {n} (p : H.LargeCondition n) {ψ : Formula (limit L) (1 + (n + 1))}
    (hψ : ⟨1 + (n + 1), ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hq : .q (Formula.exsN n (p.formula.and (.exs ψ))) ∈ H.carrier) :
    .q (Formula.exsN (n + 1) ((p.formula.rename Fin.succ).and ψ)) ∈ H.carrier := by
  have hw := and_closed (rename_closed p.in_fragment Fin.succ) hψ
  have he : H.fiber (Formula.exsN n (p.formula.and (.exs ψ))) =
      H.fiber (Formula.exsN (n + 1) ((p.formula.rename Fin.succ).and ψ)) := by
    ext x
    rw [H.fiber_weakEval (exsN_closed n (and_closed p.in_fragment (exs_closed hψ))),
      H.fiber_weakEval (exsN_closed (n + 1) hw)]
    apply Formula.weakEval_exsN_congr
    intro b
    simp only [Formula.weakEval_and, Formula.weakEval_exs, Formula.weakEval_rename]
    have he (a : H.Domain) : (a :> b) ∘ Fin.succ = b := rfl
    simp only [he, exists_and_left]
  exact (H.q_mem_extensional (exsN_closed n (and_closed p.in_fragment (exs_closed hψ)))
    (exsN_closed (n + 1) hw) he).mp hq

/-- An existential requirement either is rejected or acquires a fresh coordinate
as its witness, without reducing the large projection to a small set. -/
theorem existential {n} (p : H.LargeCondition n) {ψ : Formula (limit L) (1 + (n + 1))}
    (hψ : ⟨1 + (n + 1), ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    (∃ q : H.LargeCondition n, SameLevelRefines p q ∧
      q.formula = p.formula.and (.neg (.exs ψ))) ∨
    (∃ q : H.LargeCondition (n + 1), NextLevelRefines p q ∧
      q.formula = (p.formula.rename Fin.succ).and ψ) := by
  rcases H.q_mem_projected_split n p.in_fragment (exs_closed hψ) p.large with hp | hn
  · right
    refine ⟨⟨(p.formula.rename Fin.succ).and ψ,
      and_closed (rename_closed p.in_fragment Fin.succ) hψ, p.witness_large hψ hp⟩, ?_, rfl⟩
    intro b hb
    have hl := (Formula.weakEval_and _ _ _ _).mp hb |>.1
    exact (Formula.weakEval_rename _ _ _ _).mp hl
  · left
    refine ⟨⟨p.formula.and (.neg (.exs ψ)),
      and_closed p.in_fragment (neg_closed (exs_closed hψ)), hn⟩, ?_, rfl⟩
    intro b hb
    exact (Formula.weakEval_and _ _ _ _).mp hb |>.1

end LargeCondition
end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary
