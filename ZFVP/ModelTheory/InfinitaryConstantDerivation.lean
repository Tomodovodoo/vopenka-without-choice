import ZFVP.ModelTheory.InfinitaryConstantTranslation

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace ConstantTranslation
variable {L : Language} {C : Type*}

theorem boolean {n} (c : C → Semiterm L Empty n) {Γ : Set (Formula (WithConstants L C) n)}
    {φ : Formula (WithConstants L C) n} (h : BooleanDerivation Γ φ) :
    BooleanDerivation (formula c '' Γ) (formula c φ) := by
  induction h with
  | hypothesis h => exact .hypothesis ⟨_, h, rfl⟩
  | k φ ψ => simpa only [formula_imp] using BooleanDerivation.k (Γ := formula c '' Γ) (formula c φ) (formula c ψ)
  | s φ ψ χ => simpa only [formula_imp] using BooleanDerivation.s (Γ := formula c '' Γ) (formula c φ) (formula c ψ) (formula c χ)
  | dne φ => simpa only [formula_imp, formula] using BooleanDerivation.dne (Γ := formula c '' Γ) (formula c φ)
  | contraposition φ ψ =>
      simpa only [formula_imp, formula] using BooleanDerivation.contraposition (Γ := formula c '' Γ) (formula c φ) (formula c ψ)
  | projection φ i =>
      simpa only [Formula.countableProjection, formula_imp, formula] using
        BooleanDerivation.projection (Γ := formula c '' Γ) (fun i ↦ formula c (φ i)) i
  | distribution φ ψ =>
      simpa only [Formula.countableDistribution, formula_imp, formula] using
        BooleanDerivation.distribution (Γ := formula c '' Γ) (formula c φ) (fun i ↦ formula c (ψ i))
  | qMono φ ψ =>
      simpa only [Formula.qMonotonicity, formula_imp, formula_all, formula] using
        BooleanDerivation.qMono (Γ := formula c '' Γ) (formula (fun a ↦ Rew.bShift (c a)) φ) (formula (fun a ↦ Rew.bShift (c a)) ψ)
  | qUnion φ =>
      simpa only [Formula.qCountableUnion, Formula.disj, formula_imp, formula] using
        BooleanDerivation.qUnion (Γ := formula c '' Γ) (fun i ↦ formula (fun a ↦ Rew.bShift (c a)) (φ i))
  | mp h₁ h₂ ih₁ ih₂ => exact .mp (by simpa only [formula_imp] using ih₁) ih₂
  | conjunction φ h ih => exact .conjunction _ ih

/-- Lift closed replacement terms to the current number of free variables. -/
def closed (c : C → Semiterm L Empty 0) {n : ℕ} (a : C) : Semiterm L Empty n :=
  Rew.map Fin.elim0 id (c a)

theorem closed_rewrite (c : C → Semiterm L Empty 0) {n m}
    (w : Rew L Empty n Empty m) (a : C) : w (closed c a) = closed c a := by
  have he : w.comp (Rew.map (Fin.elim0 : Fin 0 → Fin n) id) =
      Rew.map (Fin.elim0 : Fin 0 → Fin m) id := by
    apply Rew.ext
    · intro i; exact i.elim0
    · intro i; exact i.elim
  exact congrArg (fun v ↦ v (c a)) he

theorem closed_bShift (c : C → Semiterm L Empty 0) {n} :
    (fun a ↦ Rew.bShift (closed c a : Semiterm L Empty n)) = closed c :=
  funext (closed_rewrite c Rew.bShift)

@[simp] theorem closed_zero (c : C → Semiterm L Empty 0) : @closed L C c 0 = c := by
  funext a
  have he : (Rew.map (Fin.elim0 : Fin 0 → Fin 0) id : Rew L Empty 0 Empty 0) = Rew.id := by
    apply Rew.ext
    · intro i; exact i.elim0
    · intro i; exact i.elim
  exact congrArg (fun w ↦ w (c a)) he

theorem formula_closed_rename (c : C → Semiterm L Empty 0) {n m}
    (ρ : Fin n → Fin m) (φ : Formula (WithConstants L C) n) :
    formula (closed c) (φ.rename ρ) = (formula (closed c) φ).rename ρ := by
  rw [← Formula.rewrite_map, ← Formula.rewrite_map]
  apply formula_rewrite
  · intro i; rfl
  · intro a; exact (closed_rewrite c _ a).symm

theorem formula_closed_subst (c : C → Semiterm L Empty 0) {n m}
    (σ : Fin n → Semiterm (WithConstants L C) Empty m) (φ : Formula (WithConstants L C) n) :
    formula (closed c) (φ.subst σ) = (formula (closed c) φ).subst (fun i ↦ term (closed c) (σ i)) := by
  rw [← Formula.rewrite_subst, ← Formula.rewrite_subst]
  apply formula_rewrite
  · intro i; simp only [Rew.subst_bvar]
  · intro a; exact (closed_rewrite c _ a).symm

@[simp] theorem formula_termEqual [L.Eq] {n} (c : C → Semiterm L Empty n)
    (s t : Semiterm (WithConstants L C) Empty n) :
    formula c (Formula.termEqual s t) = Formula.termEqual (term c s) (term c t) := by
  change Formula.fo (.rel Language.Eq.eq (fun i ↦ term c (![s, t] i))) = _
  congr 2
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => exact i.elim0

@[simp] theorem formula_equal [L.Eq] {n} (c : C → Semiterm L Empty n) (i j : Fin n) :
    formula c (Formula.equal i j) = Formula.equal (L := L) i j :=
  formula_termEqual c (.bvar i) (.bvar j)

theorem derivation [L.Eq] (c : C → Semiterm L Empty 0) {Γ : Set (Sentence (WithConstants L C))}
    {n} {φ : Formula (WithConstants L C) n} (h : KeislerDerivation Γ φ) :
    KeislerDerivation (formula c '' Γ) (formula (closed c) φ) := by
  induction h with
  | hypothesis h =>
      rw [formula_closed_rename, closed_zero]
      exact .hypothesis ⟨_, h, rfl⟩
  | boolean h =>
      apply KeislerDerivation.boolean
      simpa only [Set.image_empty] using boolean (closed c) h
  | truth => exact .truth
  | nonempty => exact .nonempty
  | expansion φ =>
      simpa only [formula_iff, formula_expandFirstOrder, formula] using
        KeislerDerivation.expansion (Γ := formula c '' Γ) (firstOrder (closed c) φ)
  | instantiation φ t =>
      simpa only [Formula.universalInstantiation, formula_imp, formula_all, formula_substFirst, closed_bShift] using
        KeislerDerivation.instantiation (Γ := formula c '' Γ) (formula (closed c) φ) (term (closed c) t)
  | distribution φ ψ =>
      simpa only [Formula.universalDistribution, formula_imp, formula_all, closed_bShift] using
        KeislerDerivation.distribution (Γ := formula c '' Γ) (formula (closed c) φ) (formula (closed c) ψ)
  | exDistribution φ ψ =>
      simpa only [Formula.existentialDistribution, formula_imp, formula_all, formula, closed_bShift] using
        KeislerDerivation.exDistribution (Γ := formula c '' Γ) (formula (closed c) φ) (formula (closed c) ψ)
  | vacuous φ =>
      simpa only [Formula.vacuousGeneralization, formula_imp, formula_all, closed_bShift, formula_closed_rename] using
        KeislerDerivation.vacuous (Γ := formula c '' Γ) (formula (closed c) φ)
  | eqRefl t =>
      simpa only [Formula.equalityReflexivity, formula_termEqual] using
        KeislerDerivation.eqRefl (Γ := formula c '' Γ) (term (closed c) t)
  | eqSubst φ s t =>
      simpa only [Formula.equalitySubstitution, formula_imp, formula_iff, formula_termEqual, formula_substFirst, closed_bShift] using
        KeislerDerivation.eqSubst (Γ := formula c '' Γ) (formula (closed c) φ) (term (closed c) s) (term (closed c) t)
  | qSmall i j =>
      simpa only [Formula.qTwoPoints, formula, formula_or, formula_equal, closed_bShift] using
        KeislerDerivation.qSmall (Γ := formula c '' Γ) i j
  | qInterchange φ =>
      simpa only [Formula.qInterchange, formula_imp, formula_or, formula, closed_bShift, closed_rewrite,
        Formula.swapFirstTwo, formula_closed_rename] using
        KeislerDerivation.qInterchange (Γ := formula c '' Γ) (formula (closed c) φ)
  | mp h₁ h₂ ih₁ ih₂ => exact .mp (by simpa only [formula_imp] using ih₁) ih₂
  | conjunction φ h ih => exact .conjunction _ ih
  | generalization h ih =>
      simpa only [formula_all, closed_bShift] using KeislerDerivation.generalization ih
  | substitution σ h ih =>
      rw [formula_closed_subst]
      exact .substitution _ ih

/-- Every refutation after adding constants retracts to the old language when
it already has a closed term. A later abstraction argument removes this term hypothesis. -/
theorem consistent_lMap [L.Eq] (t : Semiterm L Empty 0) {Γ : Set (Sentence L)}
    (hΓ : KeislerDerivation.Consistent Γ) :
    KeislerDerivation.Consistent
      (Formula.lMap (Language.Hom.add₁ L (Language.constant C)) '' Γ) := by
  intro h
  have hd := derivation (fun _ : C ↦ t) h
  have he : formula (fun _ : C ↦ t) ''
      (Formula.lMap (Language.Hom.add₁ L (Language.constant C)) '' Γ) = Γ := by
    ext φ
    constructor
    · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      simpa only [formula_lMap] using hψ
    · intro hφ
      exact ⟨_, ⟨φ, hφ, rfl⟩, formula_lMap _ φ⟩
  rw [he] at hd
  exact hΓ hd

end ConstantTranslation
end ZFVP.Infinitary




