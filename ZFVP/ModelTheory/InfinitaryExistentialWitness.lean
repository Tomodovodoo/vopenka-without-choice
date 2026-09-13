import ZFVP.ModelTheory.InfinitaryConstantAbstraction

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace ExistentialWitness
variable {L : Language}

/-- One new constant, distinct from every old-language symbol. -/
def fresh : Semiterm (WithConstants L Unit) Empty 0 :=
  .func (.inr (.const ())) Fin.elim0

def sentence (φ : Formula L 1) : Sentence (WithConstants L Unit) :=
  (φ.lMap (Language.Hom.add₁ L (Language.constant Unit))).substFirst fresh

@[simp] theorem abstract_sentence (φ : Formula L 1) :
    ConstantAbstraction.formula (sentence φ) = φ := by
  rw [sentence, ConstantAbstraction.formula_substFirst, ConstantAbstraction.formula_lMap]
  change (φ.rename Fin.castSucc).substFirst (.bvar 0) = φ
  simp only [Formula.substFirst, ← Formula.rewrite_map, ← Formula.rewrite_subst, Formula.rewrite_comp]
  have he : (Rew.subst (Fin.cases (.bvar 0 : Semiterm L Empty 1) Semiterm.bvar)).comp
      (Rew.map Fin.castSucc id : Rew L Empty 1 Empty 2) = Rew.id := by
    apply Rew.ext
    · intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact i.elim0
    · intro i; exact i.elim
  rw [he, Formula.rewrite_id]

theorem doubleNegIntro [L.Eq] {Γ : Set (Sentence L)} {n} (φ : Formula L n) :
    KeislerDerivation Γ (φ.imp (.neg (.neg φ))) :=
  .mp (.boolean (.contraposition (.neg (.neg φ)) φ)) (.boolean (.dne (.neg φ)))

/-- Adding a fresh constant witnessing a provable existential sentence preserves
syntactic consistency. No model or completeness theorem is assumed. -/
theorem consistent [L.Eq] {Γ : Set (Sentence L)} (hΓ : KeislerDerivation.Consistent Γ)
    (φ : Formula L 1) (hφ : KeislerDerivation Γ (.exs φ)) :
    KeislerDerivation.Consistent
      (insert (sentence φ) (Formula.lMap (Language.Hom.add₁ L (Language.constant Unit)) '' Γ)) := by
  apply (KeislerDerivation.consistent_insert_iff _).mpr
  intro h
  have hn : KeislerDerivation Γ (.neg φ) := by
    simpa only [ConstantAbstraction.formula_neg, abstract_sentence] using ConstantAbstraction.derivation h
  have he : KeislerDerivation Γ ((Formula.exs φ).imp (.exs (.neg (.neg φ)))) :=
    .mp (.exDistribution φ (.neg (.neg φ))) (.generalization (doubleNegIntro φ))
  exact hΓ ((KeislerDerivation.mp he hφ).contradiction (.generalization hn))

/-- In the standard nonempty-domain calculus, arbitrary new constants are
conservative over any consistent old-language theory. -/
theorem consistent_lMap [L.Eq] {C : Type*} {Γ : Set (Sentence L)}
    (hΓ : KeislerDerivation.Consistent Γ) :
    KeislerDerivation.Consistent
      (Formula.lMap (Language.Hom.add₁ L (Language.constant C)) '' Γ) := by
  intro h
  have hn : KeislerDerivation Γ (.neg (.fo (.verum : Semisentence L 1))) :=
    ConstantAbstraction.derivation h
  have he : KeislerDerivation Γ ((Formula.exs (.fo (.verum : Semisentence L 1))).imp
      (.exs (.neg (.neg (.fo .verum))))) :=
    .mp (.exDistribution _ _) (.generalization (doubleNegIntro _))
  exact hΓ ((KeislerDerivation.mp he .nonempty).contradiction (.generalization hn))

end ExistentialWitness
end ZFVP.Infinitary

