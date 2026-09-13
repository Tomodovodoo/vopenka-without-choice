import ZFVP.ModelTheory.InfinitaryParameterAdequacy

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

namespace ParameterInstance

def exsN : (k : ℕ) → {n : ℕ} → ParameterInstance M S (n + k) → ParameterInstance M S n
  | 0, _, p => p
  | k + 1, _, p => exsN k p.exs

theorem eval_exsN_iff (k : ℕ) {n} (p : ParameterInstance M S (n + k)) (a : Fin n → M.Domain) :
    (p.exsN k).Eval a ↔ ∃ b : Fin (n + k) → M.Domain, Formula.dropFirst k b = a ∧ p.Eval b := by
  induction k with
  | zero =>
    constructor
    · intro h; exact ⟨a, rfl, h⟩
    · rintro ⟨b, rfl, h⟩; exact h
  | succ k ih =>
    rw [exsN, ih]
    simp only [eval_exs]
    constructor
    · rintro ⟨b, hb, x, hx⟩
      exact ⟨x :> b, hb, hx⟩
    · rintro ⟨b, hb, hx⟩
      refine ⟨fun i ↦ b i.succ, hb, b 0, ?_⟩
      have he : (b 0 :> fun i : Fin (n + k) ↦ b i.succ) = b := by
        funext i
        cases i using Fin.cases <;> rfl
      rwa [he]

def projection {k} (p : ParameterInstance M S (1 + k)) : Set M.Domain :=
  {x | (p.exsN k).Eval (x :> Fin.elim0)}

theorem mem_projection {k} (p : ParameterInstance M S (1 + k)) (x : M.Domain) :
    x ∈ p.projection ↔ ∃ b : Fin (1 + k) → M.Domain, b (Formula.lastCoordinate k) = x ∧ p.Eval b := by
  change (p.exsN k).Eval (x :> Fin.elim0) ↔ _
  rw [eval_exsN_iff]
  apply exists_congr
  intro b
  rw [Formula.dropFirst_one]
  constructor
  · rintro ⟨he, hp⟩
    exact ⟨congrFun he 0, hp⟩
  · rintro ⟨he, hp⟩
    exact ⟨by rw [he], hp⟩

end ParameterInstance
namespace ParameterSequence

def exsN : (k : ℕ) → {n : ℕ} → ParameterSequence M S (n + k) → ParameterSequence M S n
  | 0, _, p => p
  | k + 1, _, p => exsN k p.exs

theorem eval_exsN_component (k : ℕ) {n} (s : ParameterSequence M S (n + k))
    (i : ℕ) (a : Fin n → M.Domain) :
    ((s.exsN k).component i).Eval a ↔ ((s.component i).exsN k).Eval a := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih s.exs

end ParameterSequence
namespace Adequate

/-- A decision can retain a large last-coordinate projection in an arbitrary adequate model. -/
theorem parameter_projected_split (hM : M.Adequate S) {k}
    (p q : ParameterInstance M S (1 + k)) (hq : M.Q p.projection) :
    M.Q (p.and q).projection ∨ M.Q (p.and q.neg).projection := by
  have hsub : p.projection ⊆ {x | ((p.and q).exsN k).Eval (x :> Fin.elim0) ∨
      ((p.and q.neg).exsN k).Eval (x :> Fin.elim0)} := by
    intro x hx
    obtain ⟨b, hb, hp⟩ := (p.mem_projection x).mp hx
    by_cases hh : q.Eval b
    · exact Or.inl ((ParameterInstance.mem_projection _ x).mpr ⟨b, hb, (p.eval_and q b).mpr ⟨hp, hh⟩⟩)
    · exact Or.inr ((ParameterInstance.mem_projection _ x).mpr ⟨b, hb, (p.eval_and q.neg b).mpr ⟨hp, hh⟩⟩)
  exact hM.parameter_finite_union ((p.and q).exsN k) ((p.and q.neg).exsN k) Fin.elim0
    (M.mono hsub hq)

/-- The conjunction witness density uses only represented sequences of finitely named instances. -/
theorem parameter_projected_conjunction_split (hM : M.Adequate S) {k}
    (p : ParameterInstance M S (1 + k)) (s : ParameterSequence M S (1 + k))
    (hq : M.Q p.projection) :
    M.Q (p.and s.conj).projection ∨ ∃ i, M.Q (p.and (s.component i).neg).projection := by
  rcases hM.parameter_projected_split p s.conj hq with hp | hn
  · exact Or.inl hp
  right
  let r := (ParameterSequence.andLeft p s.neg).exsN k
  have hsub : (p.and s.conj.neg).projection ⊆ {x | ∃ i, (r.component i).Eval (x :> Fin.elim0)} := by
    intro x hx
    obtain ⟨b, hb, ht⟩ := (ParameterInstance.mem_projection _ x).mp hx
    obtain ⟨hp, hs⟩ := (ParameterInstance.eval_and _ _ b).mp ht
    have hi : ∃ i, ¬(s.component i).Eval b := by
      simpa only [ParameterInstance.eval_neg, ParameterSequence.eval_conj, not_forall] using hs
    obtain ⟨i, hi⟩ := hi
    refine ⟨i, (ParameterSequence.eval_exsN_component k _ i _).mpr ?_⟩
    apply (ParameterInstance.mem_projection _ x).mpr
    exact ⟨b, hb, (ParameterSequence.eval_andLeft_component p s.neg i b).mpr ⟨hp, hi⟩⟩
  obtain ⟨i, hi⟩ := hM.parameter_countable_union r Fin.elim0 (M.mono hsub hn)
  refine ⟨i, ?_⟩
  have he : {x | (r.component i).Eval (x :> Fin.elim0)} = (p.and (s.component i).neg).projection := by
    ext x
    exact ParameterSequence.eval_exsN_component k _ i _
  exact he ▸ hi

end Adequate
end WeakModel
end ZFVP.Infinitary
