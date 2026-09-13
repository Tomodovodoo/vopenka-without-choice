import ZFVP.ModelTheory.InfinitaryBooleanDerivation
import ZFVP.ModelTheory.InfinitaryFirstOrderAxioms
import ZFVP.ModelTheory.InfinitaryFirstOrderExpansion
import ZFVP.ModelTheory.InfinitaryInterchange

/-! A syntactic calculus with the first-order, countable Boolean, and standard Q
axiom schemas, including nonempty domains and primitive-existential distribution. Its derivations are well-founded, countably branching proof trees.
This file proves soundness only; standard-model completeness is a separate claim. -/

namespace ZFVP.Infinitary
open LO LO.FirstOrder

inductive KeislerDerivation {L : Language} [L.Eq] (Γ : Set (Sentence L)) :
    {n : ℕ} → Formula L n → Prop where
  | hypothesis {n} {φ : Sentence L} : φ ∈ Γ →
      KeislerDerivation Γ (φ.rename (Fin.elim0 : Fin 0 → Fin n))
  | boolean {n} {φ : Formula L n} : BooleanDerivation ∅ φ → KeislerDerivation Γ φ
  | truth {n} : KeislerDerivation Γ (.fo (.verum : Semisentence L n))
  | nonempty {n} : KeislerDerivation Γ (.exs (.fo (.verum : Semisentence L (n + 1))))
  | expansion {n} (φ : Semisentence L n) :
      KeislerDerivation Γ ((Formula.fo φ).iff (Formula.expandFirstOrder φ))
  | instantiation {n} (φ : Formula L (n + 1)) (t : Semiterm L Empty n) :
      KeislerDerivation Γ (Formula.universalInstantiation φ t)
  | distribution {n} (φ ψ : Formula L (n + 1)) :
      KeislerDerivation Γ (Formula.universalDistribution φ ψ)
  | exDistribution {n} (φ ψ : Formula L (n + 1)) :
      KeislerDerivation Γ (Formula.existentialDistribution φ ψ)
  | vacuous {n} (φ : Formula L n) :
      KeislerDerivation Γ (Formula.vacuousGeneralization φ)
  | eqRefl {n} (t : Semiterm L Empty n) :
      KeislerDerivation Γ (Formula.equalityReflexivity t)
  | eqSubst {n} (φ : Formula L (n + 1)) (s t : Semiterm L Empty n) :
      KeislerDerivation Γ (Formula.equalitySubstitution φ s t)
  | qSmall {n} (i j : Fin n) : KeislerDerivation Γ (Formula.qTwoPoints i j)
  | qInterchange {n} (φ : Formula L (n + 1 + 1)) :
      KeislerDerivation Γ (Formula.qInterchange φ)
  | mp {n} {φ ψ : Formula L n} : KeislerDerivation Γ (φ.imp ψ) →
      KeislerDerivation Γ φ → KeislerDerivation Γ ψ
  | conjunction {n} (φ : ℕ → Formula L n) :
      (∀ i, KeislerDerivation Γ (φ i)) → KeislerDerivation Γ (.conj φ)
  | generalization {n} {φ : Formula L (n + 1)} :
      KeislerDerivation Γ φ → KeislerDerivation Γ (Formula.all φ)
  | substitution {n m} (σ : Fin n → Semiterm L Empty m) {φ : Formula L n} :
      KeislerDerivation Γ φ → KeislerDerivation Γ (φ.subst σ)

namespace KeislerDerivation
variable {L : Language} [L.Eq] {Γ : Set (Sentence L)}

theorem sound {n : ℕ} {φ : Formula L n} (d : KeislerDerivation Γ φ)
    {M : Type*} [Nonempty M] [Structure L M] [Structure.Eq L M]
    (hΓ : ∀ ψ ∈ Γ, Formula.Eval ψ (![] : Fin 0 → M)) (b : Fin n → M) :
    Formula.Eval φ b := by
  classical
  induction d with
  | hypothesis h =>
      rw [Formula.eval_rename]
      have he : b ∘ (Fin.elim0 : Fin 0 → _) = ![] := Subsingleton.elim _ _
      simpa only [he] using hΓ _ h
  | boolean h => exact h.sound b (by simp)
  | truth => trivial
  | nonempty => exact ⟨Classical.choice inferInstance, trivial⟩
  | expansion φ => simp
  | instantiation φ t => exact Formula.eval_universalInstantiation φ t b
  | distribution φ ψ => exact Formula.eval_universalDistribution φ ψ b
  | exDistribution φ ψ => exact Formula.eval_existentialDistribution φ ψ b
  | vacuous φ => exact Formula.eval_vacuousGeneralization φ b
  | eqRefl t => exact Formula.eval_equalityReflexivity t b
  | eqSubst φ s t => exact Formula.eval_equalitySubstitution φ s t b
  | qSmall i j => exact Formula.eval_qTwoPoints i j b
  | qInterchange φ => exact Formula.eval_qInterchange φ b
  | mp _ _ ih₁ ih₂ => exact (Formula.eval_imp _ _ _).mp (ih₁ b) (ih₂ b)
  | conjunction φ _ ih => exact fun i ↦ ih i b
  | generalization _ ih => exact (Formula.eval_all _ _).mpr fun x ↦ ih (x :> b)
  | substitution σ _ ih => exact (Formula.eval_subst _ _ _).mpr (ih _)

def Consistent (Γ : Set (Sentence L)) : Prop :=
  ¬KeislerDerivation Γ (.neg (.fo .verum : Sentence L))

theorem consistent_of_model {M : Type*} [Nonempty M] [Structure L M] [Structure.Eq L M]
    (hΓ : ∀ ψ ∈ Γ, Formula.Eval ψ (![] : Fin 0 → M)) : Consistent Γ := by
  intro d
  exact d.sound hΓ ![] trivial

end KeislerDerivation
end ZFVP.Infinitary
