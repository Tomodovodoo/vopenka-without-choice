import ZFVP.ModelTheory.PiSymmetricWitnessCodes
import ZFVP.SetTheory.PiWitnessRankEmbedding

/-! Apply the Pi fragment of VP to symmetric value-rank witnesses. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem SymmetricContext.exists_pi_witnessRank_embedding (S : SymmetricContext V) {n k : ℕ}
    (hVP : ∀ ψ : SetTheorySemisentence 2, IsPiFormula (k + 1) ψ → VopenkaInstance (V := V) ψ)
    {φ : SetTheorySemisentence (n + 1)} (hφ : IsPiFormula (k + 1) φ) (v : Fin n → S.Name)
    (hp : IsProperClass (fun x : S.Model ↦ φ.Evalb (x :> fun i ↦ S.ofName (v i))))
    (ρ : V) [IsOrdinal ρ] :
    ∃ q ∈ S.G, ∃ α β X Y θ η f : V,
      α ≠ β ∧ IsRankCriterionHeight θ ∧ IsRankCriterionHeight η ∧ ρ ∈ θ ∧ ρ ∈ η ∧
      IsLeastRankWitnessSet (S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) q) α X ∧
      IsLeastRankWitnessSet (S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) q) β Y ∧
      X ∈ hierarchy θ ∧ Y ∈ hierarchy η ∧ IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f ∧
      f ‘ α = β ∧ f ‘ X = Y ∧ ∀ i ∈ hierarchy ρ, f ‘ i = i := by
  obtain ⟨q, hq, hu⟩ := S.exists_condition_unbounded_rankWitnesses φ v hp
  obtain ⟨χ, hχ, he⟩ := (rankedFormula_pi hφ (by omega)).forcing_translation (V := V) true (by omega)
  let w := S.one :> S.P :> S.R :> S.Γ :> S.F :> q :> fun i ↦ (v i).val
  have hr : (fun a τ : V ↦ (rankWitnessSectionFormula χ).Evalb (τ :> a :> w)) =
      S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) q := by
    funext a τ
    exact propext (S.rankWitnessSection_meaning he (fun i ↦ (v i).val) (fun i ↦ (v i).property) q a τ)
  have hu' : ∀ δ : V, IsOrdinal δ → ∃ α τ : V, IsOrdinal α ∧ δ ∈ α ∧
      (rankWitnessSectionFormula χ).Evalb (τ :> α :> w) := by
    intro δ hδ
    obtain ⟨α, ⟨τ, hτ⟩, hδα⟩ := hu δ hδ
    exact ⟨α, τ, hτ.1, hδα,
      (S.rankWitnessSection_meaning he (fun i ↦ (v i).val) (fun i ↦ (v i).property) q α τ).mpr hτ⟩
  refine ⟨q, hq, ?_⟩
  simpa only [hr] using pi_vopenka_witnessRank_embedding (rankWitnessSectionFormula_pi hχ) hVP ρ w hu'

end ZFVP
