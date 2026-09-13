import ZFVP.ModelTheory.InfinitaryRightCoordinates

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

namespace LargeCondition

theorem raise_large {n m} (p : H.LargeCondition n) (h : n ≤ m) :
    .q (Formula.exsN m (p.formula.rename (Formula.rightEmbed (Nat.add_le_add_left h 1)))) ∈ H.carrier := by
  let e := Formula.rightEmbed (Nat.add_le_add_left h 1)
  have hf := rename_closed p.in_fragment e
  have he : H.fiber (Formula.exsN n p.formula) = H.fiber (Formula.exsN m (p.formula.rename e)) := by
    ext x
    rw [H.fiber_weakEval (exsN_closed n p.in_fragment), H.fiber_weakEval (exsN_closed m hf),
      Formula.weakEval_exsN_one_iff, Formula.weakEval_exsN_one_iff]
    constructor
    · rintro ⟨b, hb, hp⟩
      refine ⟨Formula.extendRight (Nat.add_le_add_left h 1) b, ?_, ?_⟩
      · rw [← Formula.rightEmbed_last (Nat.add_le_add_left h 1), Formula.extendRight_embed, hb]
      · rw [Formula.weakEval_rename]
        simpa only [e, Formula.extendRight_comp] using hp
    · rintro ⟨b, hb, hp⟩
      refine ⟨b ∘ e, ?_, (Formula.weakEval_rename _ _ _ _).mp hp⟩
      simpa only [Function.comp_apply, e, Formula.rightEmbed_last] using hb
  exact (H.q_mem_extensional (exsN_closed n p.in_fragment) (exsN_closed m hf) he).mp p.large

noncomputable def raise {n m} (p : H.LargeCondition n) (h : n ≤ m) : H.LargeCondition m where
  formula := p.formula.rename (Formula.rightEmbed (Nat.add_le_add_left h 1))
  in_fragment := rename_closed p.in_fragment _
  large := p.raise_large h

end LargeCondition

/-- Conditions of arbitrary finite arity, with a fixed last coordinate. -/
def FiniteCondition (H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))) :=
  Σ n, H.LargeCondition n

namespace FiniteCondition

def Refines (p q : H.FiniteCondition) : Prop :=
  ∃ h : p.1 ≤ q.1, ∀ b : Fin (1 + q.1) → H.Domain,
    Formula.WeakEval H.weakQuantifier q.2.formula b →
      Formula.WeakEval H.weakQuantifier p.2.formula
        (b ∘ Formula.rightEmbed (Nat.add_le_add_left h 1))

theorem refines_refl (p : H.FiniteCondition) : Refines p p := by
  refine ⟨le_refl _, ?_⟩
  intro b hb
  simpa only [Formula.rightEmbed_refl, Function.comp_def] using hb

theorem refines_trans {p q r : H.FiniteCondition} (hpq : Refines p q) (hqr : Refines q r) :
    Refines p r := by
  obtain ⟨h, hp⟩ := hpq
  obtain ⟨g, hq⟩ := hqr
  refine ⟨h.trans g, ?_⟩
  intro b hb
  have hh := hp _ (hq b hb)
  simpa only [Function.comp_def, Formula.rightEmbed_trans] using hh

theorem refines_same {n} {p q : H.LargeCondition n} (h : p.SameLevelRefines q) :
    Refines ⟨n, p⟩ ⟨n, q⟩ := by
  refine ⟨le_refl _, ?_⟩
  intro b hb
  simpa only [Formula.rightEmbed_refl, Function.comp_def] using h b hb

theorem refines_next {n} {p : H.LargeCondition n} {q : H.LargeCondition (n + 1)}
    (h : p.NextLevelRefines q) : Refines ⟨n, p⟩ ⟨n + 1, q⟩ := by
  refine ⟨Nat.le_succ _, ?_⟩
  intro b hb
  simpa only [Formula.rightEmbed_succ, Function.comp_def] using h b hb

theorem refines_raise {n m} (p : H.LargeCondition n) (h : n ≤ m) :
    Refines ⟨n, p⟩ ⟨m, p.raise h⟩ := by
  refine ⟨h, ?_⟩
  intro b hb
  exact (Formula.weakEval_rename _ _ _ _).mp hb

/-- Any requested finite list of coordinates can be accommodated. -/
theorem exists_raise (p : H.FiniteCondition) (n : ℕ) :
    ∃ q : H.FiniteCondition, Refines p q ∧ n ≤ q.1 := by
  exact ⟨⟨max p.1 n, p.2.raise (Nat.le_max_left _ _)⟩,
    refines_raise p.2 (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

end FiniteCondition
end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary
