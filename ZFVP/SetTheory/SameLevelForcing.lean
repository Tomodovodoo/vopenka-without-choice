import ZFVP.Syntax.LevyForcingMeaning

/-! Same-level definitions of ordinary and symmetric forcing for every
positive level of the external Levy hierarchy. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def ordinaryForcingSpecialization {n : ℕ} (pol : LevyPolarity) (θ : SetTheorySemisentence (n + 5)) :
    SetTheorySemisentence (n + 3) :=
  let body := forcingSystemSubst θ (.bvar 1) (.bvar 2) (.bvar 0) (.bvar 1) (.bvar 3) (forcingParameterTerms 4 rfl)
  match pol with
  | .sigma => .exs ((boundedEmptyFormula.subst ![.bvar 0]).and body)
  | .pi => .all ((∼(boundedEmptyFormula.subst ![.bvar 0])).or body)

theorem ordinaryForcingSpecialization_levy {n k : ℕ} {pol : LevyPolarity} {θ : SetTheorySemisentence (n + 5)}
    (hk : 0 < k) (hθ : IsLevyFormula pol k θ) : IsLevyFormula pol k (ordinaryForcingSpecialization pol θ) := by
  cases k with
  | zero => omega
  | succ k =>
    cases pol
    · exact .exs (.and (.bounded (boundedEmptyFormula_bounded.subst _)) (forcingSystemSubst_levy hθ _ _ _ _ _ _))
    · exact .all (.or (.bounded (boundedEmptyFormula_bounded.subst _).neg) (forcingSystemSubst_levy hθ _ _ _ _ _ _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinaryForcingSpecialization_meaning {n : ℕ} {φ : SetTheorySemisentence n}
    {θ : SetTheorySemisentence (n + 5)} (he : IsForcingTranslation (V := V) false φ θ)
    (pol : LevyPolarity) {P R : V} (hR : IsForcingPreorder P R) (v : Fin n → V)
    (hv : ∀ i, IsForcingName P (v i)) (p : V) :
    (ordinaryForcingSpecialization pol θ).Evalb (P :> R :> p :> v) ↔
      p ∈ forcingFormula P R φ (standardTuple v) := by
  have hΓ : ∀ π ∈ (∅ : V), π ∈ P ^ P := by simp
  have h := he P R ∅ P hR hΓ v hv p
  change θ.Evalb (P :> R :> ∅ :> P :> p :> v) ↔ p ∈ forcingFormula P R φ (standardTuple v) at h
  have hb (Γ : V) : (boundedEmptyFormula.subst ![.bvar 0]).Evalb (Γ :> P :> R :> p :> v) ↔ Γ = ∅ := by simp
  have hbn (Γ : V) : (∼(boundedEmptyFormula.subst ![.bvar 0])).Evalb (Γ :> P :> R :> p :> v) ↔ Γ ≠ ∅ := by simp
  cases pol
  · change (∃ Γ : V, (boundedEmptyFormula.subst ![.bvar 0]).Evalb (Γ :> P :> R :> p :> v) ∧
      (forcingSystemSubst θ (.bvar 1) (.bvar 2) (.bvar 0) (.bvar 1) (.bvar 3) (forcingParameterTerms 4 rfl)).Evalb
        (Γ :> P :> R :> p :> v)) ↔ _
    simp only [hb, exists_eq_left]
    simpa [Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
      forcingSystemSubst, forcingParameterTerms, Semiformula.Evalb] using h
  · change (∀ Γ : V, (∼(boundedEmptyFormula.subst ![.bvar 0])).Evalb (Γ :> P :> R :> p :> v) ∨
      (forcingSystemSubst θ (.bvar 1) (.bvar 2) (.bvar 0) (.bvar 1) (.bvar 3) (forcingParameterTerms 4 rfl)).Evalb
        (Γ :> P :> R :> p :> v)) ↔ _
    simp only [hbn, ← imp_iff_not_or, forall_eq]
    simpa [Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
      forcingSystemSubst, forcingParameterTerms, Semiformula.Evalb] using h

theorem IsLevyFormula.ordinaryForcing_definition {n k : ℕ} {pol : LevyPolarity} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula pol k φ) (hk : 0 < k) :
    ∃ θ : SetTheorySemisentence (n + 3), IsLevyFormula pol k θ ∧
      ∀ (P R : V), IsForcingPreorder P R → ∀ (v : Fin n → V), (∀ i, IsForcingName P (v i)) → ∀ p,
        θ.Evalb (P :> R :> p :> v) ↔ p ∈ forcingFormula P R φ (standardTuple v) := by
  obtain ⟨θ, hθ, he⟩ := hφ.forcing_translation (V := V) false hk
  exact ⟨ordinaryForcingSpecialization pol θ, ordinaryForcingSpecialization_levy hk hθ,
    fun _ _ hR v hv p ↦ ordinaryForcingSpecialization_meaning he pol hR v hv p⟩

theorem IsLevyFormula.symmetricForcing_definition {n k : ℕ} {pol : LevyPolarity} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula pol k φ) (hk : 0 < k) :
    ∃ θ : SetTheorySemisentence (n + 5), IsLevyFormula pol k θ ∧
      ∀ (P R Γ F : V), IsForcingPreorder P R → IsForcingAutomorphismGroup P R Γ →
        ∀ (v : Fin n → V), (∀ i, IsHereditarilySymmetricName P Γ F (v i)) → ∀ p,
          θ.Evalb (P :> R :> Γ :> F :> p :> v) ↔ p ∈ symmetricForcingFormula P R Γ F φ (standardTuple v) := by
  obtain ⟨θ, hθ, he⟩ := hφ.forcing_translation (V := V) true hk
  exact ⟨θ, hθ, fun P R Γ F hR hΓ v hv p ↦ he P R Γ F hR (fun π hπ ↦ (hΓ.1 π hπ).1) v hv p⟩

end ZFVP
