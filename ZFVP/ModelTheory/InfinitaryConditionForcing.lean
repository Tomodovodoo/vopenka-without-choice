import ZFVP.ModelTheory.InfinitaryFiniteConditions

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.FiniteCondition
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

def Forces (p : H.FiniteCondition) {n} (φ : Formula (limit L) n) : Prop :=
  ∃ h : n ≤ 1 + p.1, ∀ b : Fin (1 + p.1) → H.Domain,
    Formula.WeakEval H.weakQuantifier p.2.formula b →
      Formula.WeakEval H.weakQuantifier φ (b ∘ Formula.rightEmbed h)

theorem forces_persistent {p q : H.FiniteCondition} (hpq : Refines p q) {n}
    {φ : Formula (limit L) n} (hp : Forces p φ) : Forces q φ := by
  obtain ⟨g, hg⟩ := hpq
  obtain ⟨h, hh⟩ := hp
  refine ⟨h.trans (Nat.add_le_add_left g 1), ?_⟩
  intro b hb
  have := hh _ (hg b hb)
  simpa only [Function.comp_def, Formula.rightEmbed_trans] using this

theorem decide_dense (p : H.FiniteCondition) {n} {φ : Formula (limit L) n}
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    ∃ q : H.FiniteCondition, Refines p q ∧ (Forces q φ ∨ Forces q (.neg φ)) := by
  obtain ⟨r, hpr, hn⟩ := exists_raise p n
  have h : n ≤ 1 + r.1 := by omega
  obtain ⟨s, hrs, hs⟩ := r.2.decide (rename_closed hφ (Formula.rightEmbed h))
  refine ⟨⟨r.1, s⟩, refines_trans hpr (refines_same hrs), ?_⟩
  rcases hs with hs | hs
  · left
    refine ⟨h, ?_⟩
    intro b hb
    rw [hs, Formula.weakEval_and] at hb
    exact (Formula.weakEval_rename _ _ _ _).mp hb.2
  · right
    refine ⟨h, ?_⟩
    intro b hb
    rw [hs, Formula.weakEval_and] at hb
    exact fun hh ↦ hb.2 ((Formula.weakEval_rename _ _ _ _).mpr hh)

theorem conjunction_dense (p : H.FiniteCondition) {n} {f : ℕ → Formula (limit L) n}
    (hf : ⟨n, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    ∃ q : H.FiniteCondition, Refines p q ∧
      (Forces q (.conj f) ∨ ∃ i, Forces q (.neg (f i))) := by
  obtain ⟨r, hpr, hn⟩ := exists_raise p n
  have h : n ≤ 1 + r.1 := by omega
  have hh := rename_closed hf (Formula.rightEmbed h)
  change (⟨1 + r.1, Formula.conj (fun i ↦ (f i).rename (Formula.rightEmbed h))⟩ : TaggedFormula (limit L)) ∈ FragmentClosure.carrier (SequenceClosure.carrier S) at hh
  obtain ⟨s, hrs, hs⟩ := r.2.conjunction hh
  refine ⟨⟨r.1, s⟩, refines_trans hpr (refines_same hrs), ?_⟩
  rcases hs with hs | ⟨i, hs⟩
  · left
    refine ⟨h, ?_⟩
    intro b hb
    rw [hs, Formula.weakEval_and] at hb
    exact (Formula.weakEval_rename _ _ _ _).mp hb.2
  · right
    refine ⟨i, h, ?_⟩
    intro b hb
    rw [hs, Formula.weakEval_and] at hb
    exact fun hh ↦ hb.2 ((Formula.weakEval_rename _ _ _ _).mpr hh)

end HenkinConstruction.FragmentExtension.FiniteCondition
end ZFVP.Infinitary

