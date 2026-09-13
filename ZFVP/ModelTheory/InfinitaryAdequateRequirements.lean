import ZFVP.ModelTheory.InfinitaryAdequateFiniteConditions

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel.AdequateFiniteCondition
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

def HasWitness (p : AdequateFiniteCondition M S) {n} (φ : ParameterInstance M S (n + 1)) : Prop :=
  ∃ h : n ≤ 1 + p.1, ∃ i : Fin (1 + p.1), ∀ b : Fin (1 + p.1) → M.Domain,
    p.2.formula.Eval b → φ.Eval (b i :> b ∘ Formula.rightEmbed h)

theorem hasWitness_persistent {p q : AdequateFiniteCondition M S} (hpq : Refines p q) {n}
    {φ : ParameterInstance M S (n + 1)} (hp : HasWitness p φ) : HasWitness q φ := by
  obtain ⟨g, hg⟩ := hpq
  obtain ⟨h, i, hi⟩ := hp
  refine ⟨h.trans (Nat.add_le_add_left g 1), Formula.rightEmbed (Nat.add_le_add_left g 1) i, ?_⟩
  intro b hb
  have ht := hi _ (hg b hb)
  simpa only [Function.comp_def, Formula.rightEmbed_trans] using ht

theorem existential_dense (hM : M.Adequate S) (p : AdequateFiniteCondition M S) {n}
    (φ : ParameterInstance M S (n + 1)) :
    ∃ q : AdequateFiniteCondition M S, Refines p q ∧ (Forces q φ.exs.neg ∨ HasWitness q φ) := by
  obtain ⟨r, hpr, hn⟩ := exists_raise p n
  have h : n ≤ 1 + r.1 := by omega
  let ψ := φ.rename (liftRenaming (Formula.rightEmbed h))
  rcases r.2.existential hM ψ with ⟨s, hrs, hs⟩ | ⟨s, hrs, hs⟩
  · refine ⟨⟨r.1, s⟩, refines_trans hpr (refines_same hrs), Or.inl ⟨h, ?_⟩⟩
    intro b hb hx
    rw [hs, ParameterInstance.eval_and] at hb
    obtain ⟨x, hx⟩ := (ParameterInstance.eval_exs _ _).mp hx
    apply hb.2
    apply (ParameterInstance.eval_exs _ _).mpr
    refine ⟨x, (ParameterInstance.eval_rename _ _ _).mpr ?_⟩
    simpa only [compose_liftRenaming] using hx
  · refine ⟨⟨r.1 + 1, s⟩, refines_trans hpr (refines_next hrs), Or.inr ?_⟩
    let hnew : n ≤ 1 + (r.1 + 1) := h.trans (Nat.le_succ (1 + r.1))
    refine ⟨hnew, 0, ?_⟩
    intro b hb
    rw [hs, ParameterInstance.eval_and] at hb
    have ht := (ParameterInstance.eval_rename φ (liftRenaming (Formula.rightEmbed h)) b).mp hb.2
    have he : b ∘ liftRenaming (Formula.rightEmbed h) = b 0 :> b ∘ Formula.rightEmbed hnew := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        change b (Formula.rightEmbed h i).succ = b (Formula.rightEmbed hnew i)
        congr 1
        simpa only [Formula.rightEmbed_succ] using
          (Formula.rightEmbed_trans h (Nat.le_succ (1 + r.1)) i)
    rwa [he] at ht

def Freezes (p : AdequateFiniteCondition M S) {n} (i : Fin n) (ψ : ParameterInstance M S 1) : Prop :=
  ∃ h : n ≤ 1 + p.1,
    (∀ b, p.2.formula.Eval b → ¬ψ.Eval (b (Formula.rightEmbed h i) :> Fin.elim0)) ∨
      ∃ a : M.Domain, ∀ b, p.2.formula.Eval b → b (Formula.rightEmbed h i) = a

theorem freezes_persistent {p q : AdequateFiniteCondition M S} (hpq : Refines p q) {n}
    {i : Fin n} {ψ : ParameterInstance M S 1} (hp : Freezes p i ψ) : Freezes q i ψ := by
  obtain ⟨g, hg⟩ := hpq
  obtain ⟨h, hh⟩ := hp
  refine ⟨h.trans (Nat.add_le_add_left g 1), ?_⟩
  rcases hh with hh | ⟨a, hh⟩
  · left
    intro b hb
    have ht := hh _ (hg b hb)
    simpa only [Function.comp_def, Formula.rightEmbed_trans] using ht
  · right
    refine ⟨a, ?_⟩
    intro b hb
    have ht := hh _ (hg b hb)
    simpa only [Function.comp_def, Formula.rightEmbed_trans] using ht

theorem freezing_dense (hM : M.Adequate S) (p : AdequateFiniteCondition M S) {n}
    (i : Fin n) (ψ : ParameterInstance M S 1) (hs : ¬M.Q {x | ψ.Eval (x :> Fin.elim0)}) :
    ∃ q : AdequateFiniteCondition M S, Refines p q ∧ Freezes q i ψ := by
  obtain ⟨r, hpr, hn⟩ := exists_raise p n
  have h : n ≤ 1 + r.1 := by omega
  obtain ⟨s, hrs, hh⟩ := r.2.freeze hM (Formula.rightEmbed h i) ψ hs
  exact ⟨⟨r.1, s⟩, refines_trans hpr (refines_same hrs), h, hh⟩

def Avoids (p : AdequateFiniteCondition M S) (a : M.Domain) : Prop :=
  ∀ b, p.2.formula.Eval b → b (Formula.lastCoordinate p.1) ≠ a

theorem avoids_persistent {p q : AdequateFiniteCondition M S} (hpq : Refines p q)
    {a : M.Domain} (hp : Avoids p a) : Avoids q a := by
  obtain ⟨h, hh⟩ := hpq
  intro b hb
  have ht := hp _ (hh b hb)
  simpa only [Function.comp_apply, Formula.rightEmbed_last] using ht

theorem avoidance_dense (hM : M.Adequate S) (p : AdequateFiniteCondition M S) (a : M.Domain) :
    ∃ q : AdequateFiniteCondition M S, Refines p q ∧ Avoids q a := by
  obtain ⟨q, hpq, hq⟩ := p.2.avoid hM a
  exact ⟨⟨p.1, q⟩, refines_same hpq, hq⟩

end WeakModel.AdequateFiniteCondition
end ZFVP.Infinitary
