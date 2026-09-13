import ZFVP.ModelTheory.PiSymmetricRankWitnesses
import ZFVP.SetTheory.PiWitnessFamilyCode

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rankWitnessSectionFormula {n : ℕ} (θ : SetTheorySemisentence (n + 2 + 5)) : SetTheorySemisentence (n + 8) :=
  (piRankWitnessFormula θ).subst (.bvar 1 :> .bvar 0 :> forcingParameterTerms 2 rfl)

def piRankWitnessFamilyFormula {n : ℕ} (k : ℕ) (θ : SetTheorySemisentence (n + 2 + 5)) : SetTheorySemisentence (n + 8) :=
  piWitnessFamilyCodeFormula (n := n + 7) k (rankWitnessSectionFormula θ)

theorem rankWitnessSectionFormula_pi {n k : ℕ} {θ : SetTheorySemisentence (n + 2 + 5)}
    (hθ : IsPiFormula (k + 1) θ) : IsPiFormula (k + 1) (rankWitnessSectionFormula θ) :=
  (piRankWitnessFormula_pi hθ (by omega)).subst _

theorem piRankWitnessFamilyFormula_pi {n k : ℕ} {θ : SetTheorySemisentence (n + 2 + 5)}
    (hθ : IsPiFormula (k + 1) θ) : IsPiFormula (k + 1) (piRankWitnessFamilyFormula k θ) :=
  piWitnessFamilyCodeFormula_pi (rankWitnessSectionFormula_pi hθ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsLeastWitnessCertificate.leastRankWitnessSet {R : V → V → Prop} {x ξ U W C : V}
    (h : IsLeastWitnessCertificate (R x) ξ U W C) : IsLeastRankWitnessSet R x C :=
  ⟨ξ, h.least_rank, h.members⟩

theorem SymmetricContext.rankWitnessSection_meaning (S : SymmetricContext V) {n : ℕ}
    {φ : SetTheorySemisentence (n + 1)} {θ : SetTheorySemisentence (n + 2 + 5)}
    (hθ : IsForcingTranslation (V := V) true (rankedFormula φ) θ)
    (v : Fin n → V) (hv : ∀ i, IsHereditarilySymmetricName S.P S.Γ S.F (v i)) (q α τ : V) :
    (rankWitnessSectionFormula θ).Evalb (τ :> α :> S.one :> S.P :> S.R :> S.Γ :> S.F :> q :> v) ↔
      S.RankWitness φ (standardTuple v) q α τ := by
  simp only [rankWitnessSectionFormula, Semiformula.eval_substs]
  simpa [Matrix.comp_vecCons', Function.comp_def, forcingParameterTerms, Semiformula.Evalb] using
    S.rankWitness_formula_meaning hθ v hv q α τ

theorem SymmetricContext.rankWitnessFamily_existsUnique (S : SymmetricContext V) {n k : ℕ}
    {φ : SetTheorySemisentence (n + 1)} {θ : SetTheorySemisentence (n + 2 + 5)}
    (hθ : IsPiFormula (k + 1) θ) (he : IsForcingTranslation (V := V) true (rankedFormula φ) θ)
    (v : Fin n → V) (hv : ∀ i, IsHereditarilySymmetricName S.P S.Γ S.F (v i)) (q α : V) :
    (∃! c : V, (piRankWitnessFamilyFormula k θ).Evalb
      (c :> α :> S.one :> S.P :> S.R :> S.Γ :> S.F :> q :> v)) ↔
      ∃ τ, S.RankWitness φ (standardTuple v) q α τ := by
  rw [piRankWitnessFamilyFormula, piWitnessFamilyCode_existsUnique_iff (rankWitnessSectionFormula_pi hθ)]
  exact exists_congr (fun τ ↦ S.rankWitnessSection_meaning he v hv q α τ)

theorem SymmetricContext.rankWitnessFamily_sound (S : SymmetricContext V) {n k : ℕ}
    {φ : SetTheorySemisentence (n + 1)} {θ : SetTheorySemisentence (n + 2 + 5)}
    (hθ : IsPiFormula (k + 1) θ) (he : IsForcingTranslation (V := V) true (rankedFormula φ) θ)
    (v : Fin n → V) (hv : ∀ i, IsHereditarilySymmetricName S.P S.Γ S.F (v i)) (q α c : V)
    (hc : (piRankWitnessFamilyFormula k θ).Evalb (c :> α :> S.one :> S.P :> S.R :> S.Γ :> S.F :> q :> v)) :
    ∃ ξ U W X d e : V, c = ⟨ξ, ⟨U, ⟨W, ⟨X, ⟨d, e⟩ₖ⟩ₖ⟩ₖ⟩ₖ⟩ₖ ∧
      IsLeastWitnessCertificate (S.RankWitness φ (standardTuple v) q α) ξ U W X ∧
      IsLeastRankWitnessSet (S.RankWitness φ (standardTuple v) q) α X := by
  obtain ⟨ξ, U, W, X, d, e, hc, hcert⟩ := (eval_piWitnessFamilyCodeFormula (rankWitnessSectionFormula θ) c
    (α :> S.one :> S.P :> S.R :> S.Γ :> S.F :> q :> v)).mp hc
  have ht := ((eval_piWitnessCertificateFormula (rankWitnessSectionFormula_pi hθ) ξ U W X d e
    (α :> S.one :> S.P :> S.R :> S.Γ :> S.F :> q :> v)).mp hcert).1
  have hp : (fun τ ↦ (rankWitnessSectionFormula θ).Evalb
      (τ :> α :> S.one :> S.P :> S.R :> S.Γ :> S.F :> q :> v)) = S.RankWitness φ (standardTuple v) q α := by
    funext τ
    exact propext (S.rankWitnessSection_meaning he v hv q α τ)
  rw [hp] at ht
  exact ⟨ξ, U, W, X, d, e, hc, ht, ht.leastRankWitnessSet⟩

end ZFVP
