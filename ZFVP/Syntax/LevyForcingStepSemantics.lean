import ZFVP.Syntax.LevyForcingSteps
import ZFVP.SetTheory.ForcingFormulaWitnesses

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_or {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.or ψ).Evalb v ↔ φ.Evalb v ∨ ψ.Evalb v := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_all {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    φ.all.Evalb v ↔ ∀ x : V, φ.Evalb (x :> v) := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_exs {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    φ.exs.Evalb v ↔ ∃ x : V, φ.Evalb (x :> v) := Iff.rfl

theorem BoundedFormulaTree.levyForcingBase_meaning {P R : V} (hR : IsForcingPreorder P R)
    (symmetric : Bool) (Γ F : V) {n : ℕ} (φ : BoundedFormulaTree n) (pol : LevyPolarity)
    (v : Fin n → V) (hv : ∀ i, forcingNameClass symmetric P Γ F (v i)) (p : V) :
    (φ.levyForcingBase pol).Evalb (P :> R :> Γ :> F :> p :> v) ↔
      p ∈ selectedForcingFormula symmetric P R Γ F φ.formula (standardTuple v) := by
  have hs : ∀ x, forcingNameClass symmetric P Γ F x → ∀ u s, ⟨u, s⟩ₖ ∈ x →
      forcingNameClass symmetric P Γ F u := fun _ h _ _ hus ↦ forcingNameClass_subname h hus
  cases pol
  · simp only [levyForcingBase, Semiformula.eval_substs]
    simpa [Matrix.comp_vecCons', Function.comp_def, forcingParameterTerms, Semiformula.Evalb, selectedForcingFormula, TruthAnswer] using
      (φ.forcingCertificate_meaning hR (forcingNameClass symmetric P Γ F) (by definability)
        (fun _ h ↦ forcingNameClass_isName h) hs v hv true p)
  · simp only [levyForcingBase, Semiformula.eval_substs]
    simpa [Matrix.comp_vecCons', Function.comp_def, forcingParameterTerms, Semiformula.Evalb, selectedForcingFormula] using
      (φ.forcingPi_meaning hR (forcingNameClass symmetric P Γ F) (by definability)
        (fun _ h ↦ forcingNameClass_isName h) hs v hv p)

theorem eval_levyForcingOrStep {n : ℕ} (φ ψ : SetTheorySemisentence (n + 5))
    (P R Γ F p : V) (v : Fin n → V) :
    (levyForcingOrStep φ ψ).Evalb (P :> R :> Γ :> F :> p :> v) ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        (φ.Evalb (P :> R :> Γ :> F :> r :> v) ∨ ψ.Evalb (P :> R :> Γ :> F :> r :> v)) := by
  simp [levyForcingOrStep, eval_and, eval_or, eval_boundedSetAll, eval_boundedSetExs,
    forcingSystemSubst, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, Structure.rel, ← imp_iff_not_or]

theorem eval_levyForcingAllStep {n : ℕ} {P Γ : V} (hΓ : ∀ π ∈ Γ, π ∈ P ^ P)
    (symmetric : Bool) (φ : SetTheorySemisentence (n + 1 + 5)) (R F p : V) (v : Fin n → V) :
    (levyForcingAllStep symmetric φ).Evalb (P :> R :> Γ :> F :> p :> v) ↔
      p ∈ P ∧ ∀ u, forcingNameClass symmetric P Γ F u → φ.Evalb (P :> R :> Γ :> F :> p :> u :> v) := by
  simp [levyForcingAllStep, eval_and, eval_or, eval_all, forcingSystemSubst, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, forcingParameterTerms,
    Structure.rel, eval_sigmaOneForcingNameClassFormula hΓ, ← imp_iff_not_or]

theorem eval_levyForcingExsStep {n : ℕ} {P Γ : V} (hΓ : ∀ π ∈ Γ, π ∈ P ^ P)
    (symmetric : Bool) (φ : SetTheorySemisentence (n + 1 + 5)) (R F p : V) (v : Fin n → V) :
    (levyForcingExsStep symmetric φ).Evalb (P :> R :> Γ :> F :> p :> v) ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        ∃ u, forcingNameClass symmetric P Γ F u ∧ φ.Evalb (P :> R :> Γ :> F :> r :> u :> v) := by
  simp [levyForcingExsStep, eval_and, eval_or, eval_exs, eval_boundedSetAll, eval_boundedSetExs,
    forcingSystemSubst, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, Structure.rel, eval_sigmaOneForcingNameClassFormula hΓ, ← imp_iff_not_or]

theorem eval_levyForcingBoundedAllBody {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 1 + 5)) (T P R Γ F p : V) (v : Fin n → V) :
    (levyForcingBoundedAllBody t φ).Evalb (T :> P :> R :> Γ :> F :> p :> v) ↔
      p ∈ P ∧ ∀ u ∈ T, ∀ s ∈ T, ⟨u, s⟩ₖ ∈ t.val v Empty.elim →
        ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, s⟩ₖ ∈ R → φ.Evalb (P :> R :> Γ :> F :> q :> u :> v) := by
  simp [levyForcingBoundedAllBody, eval_and, eval_or, eval_boundedSetAll,
    forcingSystemSubst, Semiformula.eval_substs, Semiterm.val_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, forcingParameterTerms,
    Structure.rel, ← imp_iff_not_or]

theorem eval_levyForcingBoundedExsBody {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 1 + 5)) (T P R Γ F p : V) (v : Fin n → V) :
    (levyForcingBoundedExsBody t φ).Evalb (T :> P :> R :> Γ :> F :> p :> v) ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        ∃ u ∈ T, ∃ s ∈ T, ⟨u, s⟩ₖ ∈ t.val v Empty.elim ∧ ⟨r, s⟩ₖ ∈ R ∧
          φ.Evalb (P :> R :> Γ :> F :> r :> u :> v) := by
  simp [levyForcingBoundedExsBody, eval_and, eval_or, eval_boundedSetAll, eval_boundedSetExs,
    forcingSystemSubst, Semiformula.eval_substs, Semiterm.val_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, forcingParameterTerms,
    Structure.rel, ← imp_iff_not_or]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_forcingTransitiveGuard {n : ℕ} (T P R Γ F p : V) (v : Fin n → V) :
    (forcingTransitiveGuard n).Evalb (T :> P :> R :> Γ :> F :> p :> v) ↔ IsTransitive T ∧ ∀ i, v i ∈ T := by
  simp [forcingTransitiveGuard, eval_and, eval_finiteConjunction, Semiformula.eval_substs,
    forcingParameterTerms, Structure.rel]

theorem eval_forcingTransitiveBind {n : ℕ} (pol : LevyPolarity) (φ : SetTheorySemisentence (n + 6))
    (P R Γ F p : V) (v : Fin n → V) (Q : Prop)
    (he : ∀ T : V, IsTransitive T → (∀ i, v i ∈ T) →
      (φ.Evalb (T :> P :> R :> Γ :> F :> p :> v) ↔ Q)) :
    (forcingTransitiveBind pol φ).Evalb (P :> R :> Γ :> F :> p :> v) ↔ Q := by
  cases pol
  · change (∃ T : V, (forcingTransitiveGuard n).Evalb (T :> P :> R :> Γ :> F :> p :> v) ∧
      φ.Evalb (T :> P :> R :> Γ :> F :> p :> v)) ↔ Q
    simp only [eval_forcingTransitiveGuard]
    constructor
    · rintro ⟨T, ⟨hT, hv⟩, hφ⟩
      exact (he T hT hv).mp hφ
    · intro hQ
      obtain ⟨T, hT, hv⟩ := exists_transitive_parameters v
      exact ⟨T, ⟨hT, hv⟩, (he T hT hv).mpr hQ⟩
  · change (∀ T : V, ((∼forcingTransitiveGuard n).Evalb (T :> P :> R :> Γ :> F :> p :> v) ∨
      φ.Evalb (T :> P :> R :> Γ :> F :> p :> v))) ↔ Q
    have hn (T : V) : (∼forcingTransitiveGuard n).Evalb (T :> P :> R :> Γ :> F :> p :> v) ↔
        ¬(IsTransitive T ∧ ∀ i, v i ∈ T) := by simp [eval_forcingTransitiveGuard]
    simp only [hn, ← imp_iff_not_or]
    constructor
    · intro h
      obtain ⟨T, hT, hv⟩ := exists_transitive_parameters v
      exact (he T hT hv).mp (h T ⟨hT, hv⟩)
    · intro h T hT
      exact (he T hT.1 hT.2).mpr h

end ZFVP
