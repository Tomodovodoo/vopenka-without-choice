import ZFVP.Syntax.ProofRulePrimrec

/-! A finite, decidable witness format for each first-order LK rule. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

abbrev LKRuleWitness := ℕ × SetTheoryProposition × SetTheoryProposition ×
  Semiproposition ℒₛₑₜ 1 × ℕ × Sequent ℒₛₑₜ × Sequent ℒₛₑₜ

def LKRuleCheck (S : List (Sequent ℒₛₑₜ)) (C : Sequent ℒₛₑₜ) : LKRuleWitness → Prop
  | ⟨tag, φ, ψ, θ, k, Γ, Δ⟩ =>
    match tag with
    | 0 => C = [φ, ∼φ]
    | 1 => (φ :: Γ) ∈ S ∧ (∼φ :: Δ) ∈ S ∧ C = Γ ++ Δ
    | 2 => Δ ∈ S ∧ Δ ⊆ C
    | 3 => C = [⊤]
    | 4 => (φ :: ψ :: Γ) ∈ S ∧ C = (φ ⋎ ψ) :: Γ
    | 5 => (φ :: Γ) ∈ S ∧ (ψ :: Γ) ∈ S ∧ C = (φ ⋏ ψ) :: Γ
    | 6 => (θ.free :: Γ.map Semiformula.shift) ∈ S ∧ C = (∀¹ θ) :: Γ
    | 7 => (θ/[&k] :: Γ) ∈ S ∧ C = (∃¹ θ) :: Γ
    | _ + 8 => False

instance (S C w) : Decidable (LKRuleCheck S C w) := by
  rcases w with ⟨tag, φ, ψ, θ, k, Γ, Δ⟩
  match tag with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | n + 8 => unfold LKRuleCheck; infer_instance

theorem LKRuleCheck.mono {S U : List (Sequent ℒₛₑₜ)} {C w}
    (h : LKRuleCheck S C w) (hSU : S ⊆ U) : LKRuleCheck U C w := by
  rcases w with ⟨tag, φ, ψ, θ, k, Γ, Δ⟩
  match tag with
  | 0 | 3 => exact h
  | 1 => exact ⟨hSU h.1, hSU h.2.1, h.2.2⟩
  | 2 => exact ⟨hSU h.1, h.2⟩
  | 4 | 6 | 7 => exact ⟨hSU h.1, h.2⟩
  | 5 => exact ⟨hSU h.1, hSU h.2.1, h.2.2⟩
  | n + 8 => exact h.elim

theorem LKRuleCheck.sound {S : List (Sequent ℒₛₑₜ)} {C w}
    (h : LKRuleCheck S C w) (hS : ∀ Γ ∈ S, Nonempty (Derivation Γ)) :
    Nonempty (Derivation C) := by
  rcases w with ⟨tag, φ, ψ, θ, k, Γ, Δ⟩
  match tag with
  | 0 => exact ⟨(Derivation.eta φ).cast h.symm⟩
  | 1 =>
    obtain ⟨dp⟩ := hS _ h.1
    obtain ⟨dn⟩ := hS _ h.2.1
    exact ⟨(dp.cut dn).cast h.2.2.symm⟩
  | 2 =>
    obtain ⟨d⟩ := hS _ h.1
    exact ⟨d.contraction h.2⟩
  | 3 => exact ⟨Derivation.verum.cast h.symm⟩
  | 4 =>
    obtain ⟨d⟩ := hS _ h.1
    exact ⟨d.or.cast h.2.symm⟩
  | 5 =>
    obtain ⟨dp⟩ := hS _ h.1
    obtain ⟨dq⟩ := hS _ h.2.1
    exact ⟨(dp.and dq).cast h.2.2.symm⟩
  | 6 =>
    obtain ⟨d⟩ := hS _ h.1
    exact ⟨d.all.cast h.2.symm⟩
  | 7 =>
    obtain ⟨d⟩ := hS _ h.1
    exact ⟨d.exs.cast h.2.symm⟩
  | n + 8 => exact h.elim

end ZFVP
