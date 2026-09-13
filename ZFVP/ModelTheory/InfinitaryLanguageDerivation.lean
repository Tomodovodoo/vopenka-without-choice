import ZFVP.ModelTheory.InfinitaryLanguageMapLaws

namespace ZFVP.Infinitary
open LO LO.FirstOrder

namespace BooleanDerivation
variable {L K : Language}

theorem lMap (η : L →ᵥ K) {n} {Γ : Set (Formula L n)} {φ : Formula L n}
    (h : BooleanDerivation Γ φ) : BooleanDerivation (Formula.lMap η '' Γ) (φ.lMap η) := by
  induction h with
  | hypothesis h => exact .hypothesis ⟨_, h, rfl⟩
  | k φ ψ => simpa only [Formula.lMap_imp] using BooleanDerivation.k (Γ := Formula.lMap η '' Γ) (φ.lMap η) (ψ.lMap η)
  | s φ ψ χ => simpa only [Formula.lMap_imp] using BooleanDerivation.s (Γ := Formula.lMap η '' Γ) (φ.lMap η) (ψ.lMap η) (χ.lMap η)
  | dne φ => simpa only [Formula.lMap_imp, Formula.lMap_neg] using BooleanDerivation.dne (Γ := Formula.lMap η '' Γ) (φ.lMap η)
  | contraposition φ ψ =>
      simpa only [Formula.lMap_imp, Formula.lMap_neg] using BooleanDerivation.contraposition (Γ := Formula.lMap η '' Γ) (φ.lMap η) (ψ.lMap η)
  | projection φ i =>
      simpa only [Formula.countableProjection, Formula.lMap_imp, Formula.lMap_conj] using
        BooleanDerivation.projection (Γ := Formula.lMap η '' Γ) (fun i ↦ (φ i).lMap η) i
  | distribution φ ψ =>
      simpa only [Formula.countableDistribution, Formula.lMap_imp, Formula.lMap_conj] using
        BooleanDerivation.distribution (Γ := Formula.lMap η '' Γ) (φ.lMap η) (fun i ↦ (ψ i).lMap η)
  | qMono φ ψ =>
      simpa only [Formula.qMonotonicity, Formula.lMap_imp, Formula.lMap_all, Formula.lMap_q] using
        BooleanDerivation.qMono (Γ := Formula.lMap η '' Γ) (φ.lMap η) (ψ.lMap η)
  | qUnion φ =>
      simpa only [Formula.qCountableUnion, Formula.disj, Formula.lMap_imp, Formula.lMap_q, Formula.lMap_neg, Formula.lMap_conj] using
        BooleanDerivation.qUnion (Γ := Formula.lMap η '' Γ) (fun i ↦ (φ i).lMap η)
  | mp h₁ h₂ ih₁ ih₂ => exact .mp (by simpa only [Formula.lMap_imp] using ih₁) ih₂
  | conjunction φ h ih => exact .conjunction _ ih
end BooleanDerivation

namespace KeislerDerivation
variable {L K : Language} [L.Eq] [K.Eq]

/-- Equality-preserving language maps transport all rules of the nonempty calculus. -/
theorem lMap (η : L →ᵥ K) (he : η.rel Language.Eq.eq = Language.Eq.eq)
    {Γ : Set (Sentence L)} {n} {φ : Formula L n} (h : KeislerDerivation Γ φ) :
    KeislerDerivation (Formula.lMap η '' Γ) (φ.lMap η) := by
  induction h with
  | hypothesis h =>
      rw [Formula.lMap_rename]
      exact .hypothesis ⟨_, h, rfl⟩
  | boolean h =>
      apply KeislerDerivation.boolean
      simpa only [Set.image_empty] using h.lMap η
  | truth => exact .truth
  | nonempty => exact .nonempty
  | expansion φ =>
      simpa only [Formula.lMap_iff, Formula.lMap_expandFirstOrder, Formula.lMap] using
        KeislerDerivation.expansion (Γ := Formula.lMap η '' Γ) (φ.lMap η)
  | instantiation φ t =>
      simpa only [Formula.universalInstantiation, Formula.lMap_imp, Formula.lMap_all, Formula.lMap_substFirst] using
        KeislerDerivation.instantiation (Γ := Formula.lMap η '' Γ) (φ.lMap η) (t.lMap η)
  | distribution φ ψ =>
      simpa only [Formula.universalDistribution, Formula.lMap_imp, Formula.lMap_all] using
        KeislerDerivation.distribution (Γ := Formula.lMap η '' Γ) (φ.lMap η) (ψ.lMap η)
  | exDistribution φ ψ =>
      simpa only [Formula.existentialDistribution, Formula.lMap_imp, Formula.lMap_all, Formula.lMap_exs] using
        KeislerDerivation.exDistribution (Γ := Formula.lMap η '' Γ) (φ.lMap η) (ψ.lMap η)
  | vacuous φ =>
      simpa only [Formula.vacuousGeneralization, Formula.lMap_imp, Formula.lMap_all, Formula.lMap_rename] using
        KeislerDerivation.vacuous (Γ := Formula.lMap η '' Γ) (φ.lMap η)
  | eqRefl t =>
      simpa only [Formula.equalityReflexivity, Formula.lMap_termEqual η he] using
        KeislerDerivation.eqRefl (Γ := Formula.lMap η '' Γ) (t.lMap η)
  | eqSubst φ s t =>
      simpa only [Formula.equalitySubstitution, Formula.lMap_imp, Formula.lMap_iff,
        Formula.lMap_termEqual η he, Formula.lMap_substFirst] using
        KeislerDerivation.eqSubst (Γ := Formula.lMap η '' Γ) (φ.lMap η) (s.lMap η) (t.lMap η)
  | qSmall i j =>
      simpa only [Formula.qTwoPoints, Formula.lMap_neg, Formula.lMap_q, Formula.lMap_or, Formula.lMap_equal η he] using
        KeislerDerivation.qSmall (Γ := Formula.lMap η '' Γ) i j
  | qInterchange φ =>
      simpa only [Formula.qInterchange, Formula.lMap_imp, Formula.lMap_or, Formula.lMap_q, Formula.lMap_exs,
        Formula.swapFirstTwo, Formula.lMap_rename] using
        KeislerDerivation.qInterchange (Γ := Formula.lMap η '' Γ) (φ.lMap η)
  | mp h₁ h₂ ih₁ ih₂ => exact .mp (by simpa only [Formula.lMap_imp] using ih₁) ih₂
  | conjunction φ h ih => exact .conjunction _ ih
  | generalization h ih =>
      simpa only [Formula.lMap_all] using KeislerDerivation.generalization ih
  | substitution σ h ih =>
      rw [Formula.lMap_subst]
      exact .substitution _ ih

end KeislerDerivation
end ZFVP.Infinitary
