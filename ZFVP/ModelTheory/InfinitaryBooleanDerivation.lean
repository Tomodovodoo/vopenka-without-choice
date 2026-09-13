import ZFVP.ModelTheory.InfinitaryQuantifierAxioms

/-! A sound syntactic derivation system for the Boolean, countable-conjunction,
and monotonicity/countable-union parts of Keisler's calculus. First-order
quantifier axioms and the Q interchange schema are not included here. -/

namespace ZFVP.Infinitary
open LO LO.FirstOrder

inductive BooleanDerivation {L : Language} {n : ℕ} (Γ : Set (Formula L n)) :
    Formula L n → Prop where
  | hypothesis {φ} : φ ∈ Γ → BooleanDerivation Γ φ
  | k (φ ψ : Formula L n) : BooleanDerivation Γ (φ.imp (ψ.imp φ))
  | s (φ ψ χ : Formula L n) : BooleanDerivation Γ
      ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | dne (φ : Formula L n) : BooleanDerivation Γ ((Formula.neg (.neg φ)).imp φ)
  | contraposition (φ ψ : Formula L n) : BooleanDerivation Γ
      (((Formula.neg φ).imp (.neg ψ)).imp (ψ.imp φ))
  | projection (φ : ℕ → Formula L n) (i) :
      BooleanDerivation Γ (Formula.countableProjection φ i)
  | distribution (φ) (ψ : ℕ → Formula L n) :
      BooleanDerivation Γ (Formula.countableDistribution φ ψ)
  | qMono (φ ψ : Formula L (n + 1)) :
      BooleanDerivation Γ (Formula.qMonotonicity φ ψ)
  | qUnion (φ : ℕ → Formula L (n + 1)) :
      BooleanDerivation Γ (Formula.qCountableUnion φ)
  | mp {φ ψ} : BooleanDerivation Γ (φ.imp ψ) → BooleanDerivation Γ φ →
      BooleanDerivation Γ ψ
  | conjunction (φ : ℕ → Formula L n) :
      (∀ i, BooleanDerivation Γ (φ i)) → BooleanDerivation Γ (.conj φ)

namespace BooleanDerivation
variable {L : Language} {n : ℕ} {Γ : Set (Formula L n)} {φ : Formula L n}

theorem sound (d : BooleanDerivation Γ φ) {M : Type*} [Structure L M]
    (b : Fin n → M) (hΓ : ∀ ψ ∈ Γ, Formula.Eval ψ b) : Formula.Eval φ b := by
  classical
  induction d with
  | hypothesis h => exact hΓ _ h
  | k φ ψ => simp only [Formula.eval_imp]; tauto
  | s φ ψ χ => simp only [Formula.eval_imp]; tauto
  | dne φ => simp
  | contraposition φ ψ => simp only [Formula.eval_imp, Formula.eval_neg]; tauto
  | projection φ i => exact Formula.eval_countableProjection φ i b
  | distribution φ ψ => exact Formula.eval_countableDistribution φ ψ b
  | qMono φ ψ => exact Formula.eval_qMonotonicity φ ψ b
  | qUnion φ => exact Formula.eval_qCountableUnion φ b
  | mp _ _ ih₁ ih₂ => exact (Formula.eval_imp _ _ _).mp ih₁ ih₂
  | conjunction φ _ ih => exact ih

theorem satisfiable_not_refuted {Γ : Set (Sentence L)} {φ : Sentence L}
    (hM : ∃ M : Type, ∃ s : Structure L M,
      (∀ ψ ∈ Γ, @Formula.Eval L M s 0 ψ ![]) ∧ @Formula.Eval L M s 0 φ ![])
    (d : BooleanDerivation Γ (.neg φ)) : False := by
  obtain ⟨M, s, hΓ, hφ⟩ := hM
  exact @sound L 0 Γ (.neg φ) d M s ![] hΓ hφ

end BooleanDerivation
end ZFVP.Infinitary
