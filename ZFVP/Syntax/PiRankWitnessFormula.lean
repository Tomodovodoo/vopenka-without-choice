import ZFVP.SetTheory.DeltaOneCheckNames
import ZFVP.SetTheory.SameLevelForcing
import ZFVP.Syntax.RankedFormula

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piRankWitnessFormula {n : ℕ} (θ : SetTheorySemisentence (n + 2 + 5)) : SetTheorySemisentence (n + 8) :=
  (IsOrdinal.dfn.subst ![.bvar 0]).and
    ((piOneHereditarySymmetryFormula.subst ![.bvar 3, .bvar 5, .bvar 6, .bvar 1]).and
      (.all ((∼((sigmaOneCheckNameFormula true).subst ![.bvar 3, .bvar 1, .bvar 0])).or
        (forcingSystemSubst θ (.bvar 4) (.bvar 5) (.bvar 6) (.bvar 7) (.bvar 8)
          (.bvar 0 :> .bvar 2 :> forcingParameterTerms 9 rfl)))))

theorem piRankWitnessFormula_pi {n k : ℕ} {θ : SetTheorySemisentence (n + 2 + 5)}
    (hθ : IsPiFormula k θ) (hk : 0 < k) : IsPiFormula k (piRankWitnessFormula θ) := by
  cases k with
  | zero => omega
  | succ k =>
    exact .and (.bounded (isOrdinalFormula_bounded.subst _))
      (.and ((piOneHereditarySymmetryFormula_piOne.subst _).mono (by omega))
        (.all (.or ((((sigmaOneCheckNameFormula_sigmaOne true).subst _).neg).mono (by omega))
          (forcingSystemSubst_levy hθ _ _ _ _ _ _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_all {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    φ.all.Evalb v ↔ ∀ x : V, φ.Evalb (x :> v) := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_or {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.or ψ).Evalb v ↔ φ.Evalb v ∨ ψ.Evalb v := Iff.rfl

theorem eval_piRankWitnessFormula {P Γ : V} (hΓ : ∀ π ∈ Γ, π ∈ P ^ P)
    {n : ℕ} (θ : SetTheorySemisentence (n + 2 + 5)) (one R F q α τ : V) (v : Fin n → V) :
    (piRankWitnessFormula θ).Evalb (α :> τ :> one :> P :> R :> Γ :> F :> q :> v) ↔
      IsOrdinal α ∧ IsHereditarilySymmetricName P Γ F τ ∧
        θ.Evalb (P :> R :> Γ :> F :> q :> checkName one α :> τ :> v) := by
  simp [piRankWitnessFormula, eval_and, eval_or, eval_all, forcingSystemSubst,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, eval_piOneHereditarySymmetryFormula hΓ,
    eval_sigmaOneCheckNameFormula, TruthAnswer, ← imp_iff_not_or]

end ZFVP
