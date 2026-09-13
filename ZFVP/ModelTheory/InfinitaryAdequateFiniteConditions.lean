import ZFVP.ModelTheory.InfinitaryAdequateFreezing

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

namespace AdequateCondition

theorem raise_projection {n m} (p : AdequateCondition M S n) (h : n ≤ m) :
    p.formula.projection = ParameterInstance.projection (k := m)
      (p.formula.rename (Formula.rightEmbed (Nat.add_le_add_left h 1))) := by
  let e := Formula.rightEmbed (Nat.add_le_add_left h 1)
  ext x
  rw [ParameterInstance.mem_projection, ParameterInstance.mem_projection]
  constructor
  · rintro ⟨b, hb, hp⟩
    refine ⟨Formula.extendRight (Nat.add_le_add_left h 1) b, ?_, ?_⟩
    · rw [← Formula.rightEmbed_last (Nat.add_le_add_left h 1), Formula.extendRight_embed, hb]
    · rw [ParameterInstance.eval_rename]
      simpa only [Formula.extendRight_comp] using hp
  · rintro ⟨b, hb, hp⟩
    refine ⟨b ∘ e, ?_, (ParameterInstance.eval_rename _ _ _).mp hp⟩
    simpa only [Function.comp_apply, e, Formula.rightEmbed_last] using hb

noncomputable def raise {n m} (p : AdequateCondition M S n) (h : n ≤ m) :
    AdequateCondition M S m where
  formula := p.formula.rename (Formula.rightEmbed (Nat.add_le_add_left h 1))
  large := p.raise_projection h ▸ p.large

end AdequateCondition

/-- All finite arities of the semantic condition construction. -/
def AdequateFiniteCondition (M : WeakModel.{u,v} L) (S : Set (TaggedFormula L)) :=
  Σ n, AdequateCondition M S n

namespace AdequateFiniteCondition

def Refines (p q : AdequateFiniteCondition M S) : Prop :=
  ∃ h : p.1 ≤ q.1, ∀ b : Fin (1 + q.1) → M.Domain,
    q.2.formula.Eval b → p.2.formula.Eval (b ∘ Formula.rightEmbed (Nat.add_le_add_left h 1))

theorem refines_refl (p : AdequateFiniteCondition M S) : Refines p p := by
  refine ⟨le_refl _, ?_⟩
  intro b hb
  simpa only [Formula.rightEmbed_refl, Function.comp_def] using hb

theorem refines_trans {p q r : AdequateFiniteCondition M S} (hpq : Refines p q) (hqr : Refines q r) :
    Refines p r := by
  obtain ⟨h, hp⟩ := hpq
  obtain ⟨g, hq⟩ := hqr
  refine ⟨h.trans g, ?_⟩
  intro b hb
  have hh := hp _ (hq b hb)
  simpa only [Function.comp_def, Formula.rightEmbed_trans] using hh

theorem refines_same {n} {p q : AdequateCondition M S n} (h : p.Refines q) :
    Refines ⟨n, p⟩ ⟨n, q⟩ := by
  refine ⟨le_refl _, ?_⟩
  intro b hb
  simpa only [Formula.rightEmbed_refl, Function.comp_def] using h b hb

theorem refines_next {n} {p : AdequateCondition M S n} {q : AdequateCondition M S (n + 1)}
    (h : p.NextRefines q) : Refines ⟨n, p⟩ ⟨n + 1, q⟩ := by
  refine ⟨Nat.le_succ _, ?_⟩
  intro b hb
  simpa only [Formula.rightEmbed_succ, Function.comp_def] using h b hb

theorem refines_raise {n m} (p : AdequateCondition M S n) (h : n ≤ m) :
    Refines ⟨n, p⟩ ⟨m, p.raise h⟩ := by
  refine ⟨h, ?_⟩
  intro b hb
  exact (ParameterInstance.eval_rename _ _ _).mp hb

theorem exists_raise (p : AdequateFiniteCondition M S) (n : ℕ) :
    ∃ q : AdequateFiniteCondition M S, Refines p q ∧ n ≤ q.1 :=
  ⟨⟨max p.1 n, p.2.raise (Nat.le_max_left _ _)⟩,
    refines_raise p.2 (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

def Forces (p : AdequateFiniteCondition M S) {n} (φ : ParameterInstance M S n) : Prop :=
  ∃ h : n ≤ 1 + p.1, ∀ b : Fin (1 + p.1) → M.Domain,
    p.2.formula.Eval b → φ.Eval (b ∘ Formula.rightEmbed h)

theorem forces_persistent {p q : AdequateFiniteCondition M S} (hpq : Refines p q) {n}
    {φ : ParameterInstance M S n} (hp : Forces p φ) : Forces q φ := by
  obtain ⟨g, hg⟩ := hpq
  obtain ⟨h, hh⟩ := hp
  refine ⟨h.trans (Nat.add_le_add_left g 1), ?_⟩
  intro b hb
  have ht := hh _ (hg b hb)
  simpa only [Function.comp_def, Formula.rightEmbed_trans] using ht

theorem decide_dense (hM : M.Adequate S) (p : AdequateFiniteCondition M S) {n}
    (φ : ParameterInstance M S n) :
    ∃ q : AdequateFiniteCondition M S, Refines p q ∧ (Forces q φ ∨ Forces q φ.neg) := by
  obtain ⟨r, hpr, hn⟩ := exists_raise p n
  have h : n ≤ 1 + r.1 := by omega
  obtain ⟨s, hrs, hs⟩ := r.2.decide hM (φ.rename (Formula.rightEmbed h))
  refine ⟨⟨r.1, s⟩, refines_trans hpr (refines_same hrs), ?_⟩
  rcases hs with hs | hs
  · left
    refine ⟨h, ?_⟩
    intro b hb
    rw [hs, ParameterInstance.eval_and] at hb
    exact (ParameterInstance.eval_rename _ _ _).mp hb.2
  · right
    refine ⟨h, ?_⟩
    intro b hb
    rw [hs, ParameterInstance.eval_and] at hb
    exact fun hh ↦ hb.2 ((ParameterInstance.eval_rename _ _ _).mpr hh)

theorem conjunction_dense (hM : M.Adequate S) (p : AdequateFiniteCondition M S) {n}
    (f : ParameterSequence M S n) :
    ∃ q : AdequateFiniteCondition M S, Refines p q ∧
      (Forces q f.conj ∨ ∃ i, Forces q (f.component i).neg) := by
  obtain ⟨r, hpr, hn⟩ := exists_raise p n
  have h : n ≤ 1 + r.1 := by omega
  obtain ⟨s, hrs, hs⟩ := r.2.conjunction hM (f.rename (Formula.rightEmbed h))
  refine ⟨⟨r.1, s⟩, refines_trans hpr (refines_same hrs), ?_⟩
  rcases hs with hs | ⟨i, hs⟩
  · left
    refine ⟨h, ?_⟩
    intro b hb
    rw [hs, ParameterInstance.eval_and] at hb
    apply (ParameterSequence.eval_conj _ _).mpr
    intro i
    exact (ParameterSequence.eval_rename_component _ _ i b).mp ((ParameterSequence.eval_conj _ b).mp hb.2 i)
  · right
    refine ⟨i, h, ?_⟩
    intro b hb
    rw [hs, ParameterInstance.eval_and] at hb
    exact fun hh ↦ hb.2 ((ParameterSequence.eval_rename_component _ _ i b).mpr hh)

end AdequateFiniteCondition
end WeakModel
end ZFVP.Infinitary
