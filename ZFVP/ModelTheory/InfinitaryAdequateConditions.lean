import ZFVP.ModelTheory.InfinitaryParameterProjection
import ZFVP.ModelTheory.InfinitaryRightCoordinates

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

namespace ParameterInstance

def equalName {n} (i : Fin n) (a : M.Domain) : ParameterInstance M S n :=
  ⟨1, ⟨⟨Formula.equal (Fin.castAdd 1 i) (Fin.natAdd n 0), FragmentClosure.fo_closed _⟩, ![a]⟩⟩

@[simp] theorem eval_equalName {n} (i : Fin n) (a : M.Domain) (b : Fin n → M.Domain) :
    (equalName (S := S) i a).Eval b ↔ b i = a := by
  simp [Eval, equalName]

end ParameterInstance

/-- A finite named-template condition with a Q-large last-coordinate projection. -/
structure AdequateCondition (M : WeakModel.{u,v} L) (S : Set (TaggedFormula L)) (n : ℕ) where
  formula : ParameterInstance M S (1 + n)
  large : M.Q formula.projection

namespace AdequateCondition

def Refines {n} (p q : AdequateCondition M S n) : Prop :=
  ∀ b, q.formula.Eval b → p.formula.Eval b

def NextRefines {n} (p : AdequateCondition M S n) (q : AdequateCondition M S (n + 1)) : Prop :=
  ∀ b, q.formula.Eval b → p.formula.Eval (fun i ↦ b i.succ)

theorem countable (hS : S.Countable) (n : ℕ) : Countable (AdequateCondition M S n) := by
  have := ParameterInstance.countable (M := M) hS (1 + n)
  exact Function.Injective.countable (f := fun p : AdequateCondition M S n ↦ p.formula) (by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ h
    cases h
    rfl)

theorem nonempty (hM : M.Adequate S) {n} (p : AdequateCondition M S n) :
    ∃ b, p.formula.Eval b := by
  obtain ⟨x, hx⟩ := hM.nonempty_of_Q p.large
  obtain ⟨b, _, hb⟩ := (p.formula.mem_projection x).mp hx
  exact ⟨b, hb⟩

theorem decide (hM : M.Adequate S) {n} (p : AdequateCondition M S n)
    (ψ : ParameterInstance M S (1 + n)) :
    ∃ q : AdequateCondition M S n, Refines p q ∧
      (q.formula = p.formula.and ψ ∨ q.formula = p.formula.and ψ.neg) := by
  rcases hM.parameter_projected_split p.formula ψ p.large with hp | hn
  · refine ⟨⟨p.formula.and ψ, hp⟩, ?_, Or.inl rfl⟩
    intro b hb
    exact (ParameterInstance.eval_and _ _ b).mp hb |>.1
  · refine ⟨⟨p.formula.and ψ.neg, hn⟩, ?_, Or.inr rfl⟩
    intro b hb
    exact (ParameterInstance.eval_and _ _ b).mp hb |>.1

theorem conjunction (hM : M.Adequate S) {n} (p : AdequateCondition M S n)
    (s : ParameterSequence M S (1 + n)) :
    ∃ q : AdequateCondition M S n, Refines p q ∧
      (q.formula = p.formula.and s.conj ∨ ∃ i, q.formula = p.formula.and (s.component i).neg) := by
  rcases hM.parameter_projected_conjunction_split p.formula s p.large with hp | ⟨i, hn⟩
  · refine ⟨⟨p.formula.and s.conj, hp⟩, ?_, Or.inl rfl⟩
    intro b hb
    exact (ParameterInstance.eval_and _ _ b).mp hb |>.1
  · refine ⟨⟨p.formula.and (s.component i).neg, hn⟩, ?_, Or.inr ⟨i, rfl⟩⟩
    intro b hb
    exact (ParameterInstance.eval_and _ _ b).mp hb |>.1

theorem witness_projection {n} (p : AdequateCondition M S n)
    (ψ : ParameterInstance M S (1 + (n + 1))) :
    (p.formula.and ψ.exs).projection = ParameterInstance.projection (k := n + 1) ((p.formula.rename Fin.succ).and ψ) := by
  ext x
  rw [ParameterInstance.mem_projection, ParameterInstance.mem_projection]
  simp only [ParameterInstance.eval_and, ParameterInstance.eval_exs, ParameterInstance.eval_rename]
  constructor
  · rintro ⟨b, hb, hp, t, ht⟩
    exact ⟨t :> b, hb, hp, ht⟩
  · rintro ⟨b, hb, hp, ht⟩
    refine ⟨fun i ↦ b i.succ, hb, hp, b 0, ?_⟩
    have he : (b 0 :> fun i : Fin (1 + n) ↦ b i.succ) = b := by
      funext i
      cases i using Fin.cases <;> rfl
    exact he.symm ▸ ht

theorem existential (hM : M.Adequate S) {n} (p : AdequateCondition M S n)
    (ψ : ParameterInstance M S (1 + (n + 1))) :
    (∃ q : AdequateCondition M S n, Refines p q ∧ q.formula = p.formula.and ψ.exs.neg) ∨
    (∃ q : AdequateCondition M S (n + 1), NextRefines p q ∧
      q.formula = (p.formula.rename Fin.succ).and ψ) := by
  rcases hM.parameter_projected_split p.formula ψ.exs p.large with hp | hn
  · right
    refine ⟨⟨(p.formula.rename Fin.succ).and ψ, (p.witness_projection ψ) ▸ hp⟩, ?_, rfl⟩
    intro b hb
    exact (ParameterInstance.eval_rename _ _ b).mp ((ParameterInstance.eval_and _ _ b).mp hb).1
  · left
    refine ⟨⟨p.formula.and ψ.exs.neg, hn⟩, ?_, rfl⟩
    intro b hb
    exact (ParameterInstance.eval_and _ _ b).mp hb |>.1

/-- Removing one named old point retains a large distinguished-coordinate projection. -/
theorem avoid (hM : M.Adequate S) {n} (p : AdequateCondition M S n) (a : M.Domain) :
    ∃ q : AdequateCondition M S n, Refines p q ∧
      ∀ b, q.formula.Eval b → b (Formula.lastCoordinate n) ≠ a := by
  let ψ := ParameterInstance.equalName (S := S) (Formula.lastCoordinate n) a
  have hs : ¬M.Q (p.formula.and ψ).projection := by
    intro hq
    apply hM.not_twoPoints a a
    apply M.mono ?_ hq
    intro x hx
    obtain ⟨b, hb, hp⟩ := (ParameterInstance.mem_projection _ x).mp hx
    have ha := (ParameterInstance.eval_equalName _ _ b).mp ((ParameterInstance.eval_and _ _ b).mp hp).2
    have hx : x = a := hb.symm.trans ha
    simp [hx]
  have hn := (hM.parameter_projected_split p.formula ψ p.large).resolve_left hs
  refine ⟨⟨p.formula.and ψ.neg, hn⟩, ?_, ?_⟩
  · intro b hb
    exact (ParameterInstance.eval_and _ _ b).mp hb |>.1
  · intro b hb
    have hh := (ParameterInstance.eval_and _ _ b).mp hb |>.2
    exact fun ha ↦ hh ((ParameterInstance.eval_equalName _ _ b).mpr ha)

end AdequateCondition
end WeakModel
end ZFVP.Infinitary


