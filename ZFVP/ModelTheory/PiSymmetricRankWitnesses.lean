import ZFVP.ModelTheory.SymmetricRankWitnesses
import ZFVP.Syntax.PiRankWitnessFormula

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem SymmetricContext.rankWitness_formula_meaning (S : SymmetricContext V) {n : ℕ}
    {φ : SetTheorySemisentence (n + 1)} {θ : SetTheorySemisentence (n + 2 + 5)}
    (hθ : IsForcingTranslation (V := V) true (rankedFormula φ) θ)
    (v : Fin n → V) (hv : ∀ i, IsHereditarilySymmetricName S.P S.Γ S.F (v i)) (q α τ : V) :
    (piRankWitnessFormula θ).Evalb (α :> τ :> S.one :> S.P :> S.R :> S.Γ :> S.F :> q :> v) ↔
      S.RankWitness φ (standardTuple v) q α τ := by
  have hΓ : ∀ π ∈ S.Γ, π ∈ S.P ^ S.P := fun π hπ ↦ (S.group.1 π hπ).1
  rw [eval_piRankWitnessFormula hΓ]
  unfold SymmetricContext.RankWitness
  apply and_congr Iff.rfl
  apply and_congr_right
  intro hτ
  have hcheck := hereditarilySymmetric_checkName S.poset S.group S.normal S.top α
  exact hθ S.P S.R S.Γ S.F S.poset.1 hΓ (checkName S.one α :> τ :> v)
    (fun i ↦ Fin.cases hcheck (fun j ↦ Fin.cases hτ hv j) i) q

theorem pi_symmetric_rankWitness_definition {n k : ℕ} {φ : SetTheorySemisentence (n + 1)}
    (hφ : IsPiFormula k φ) (hk : 0 < k) :
    ∃ ψ : SetTheorySemisentence (n + 8), IsPiFormula k ψ ∧
      ∀ (S : SymmetricContext V) (v : Fin n → V),
        (∀ i, IsHereditarilySymmetricName S.P S.Γ S.F (v i)) → ∀ q α τ,
          ψ.Evalb (α :> τ :> S.one :> S.P :> S.R :> S.Γ :> S.F :> q :> v) ↔
            S.RankWitness φ (standardTuple v) q α τ := by
  obtain ⟨θ, hθ, he⟩ := (rankedFormula_pi hφ hk).forcing_translation (V := V) true hk
  exact ⟨piRankWitnessFormula θ, piRankWitnessFormula_pi hθ hk,
    fun S v hv q α τ ↦ S.rankWitness_formula_meaning he v hv q α τ⟩

end ZFVP
