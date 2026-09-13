import ZFVP.ModelTheory.SymmetricRankWitnesses
import ZFVP.SetTheory.RankWitnessStructures

/-! Apply ground-model VP to the canonical family of symmetric value-rank witnesses. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

theorem exists_witnessRank_embedding (S : SymmetricContext V)
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → S.Name)
    (hp : IsProperClass (fun x : S.Model ↦ φ.Evalb (x :> fun i ↦ S.ofName (v i))))
    (ρ : V) [IsOrdinal ρ] :
    ∃ q ∈ S.G, ∃ α β X Y θ η f : V,
      α ≠ β ∧
      IsWitnessRankStage (S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) q) ρ α X θ ∧
      IsWitnessRankStage (S.RankWitness φ (standardTuple (fun i ↦ (v i).val)) q) ρ β Y η ∧
      IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f ∧
      f ‘ α = β ∧ f ‘ X = Y ∧ ∀ i ∈ hierarchy ρ, f ‘ i = i := by
  obtain ⟨q, hqG, hu⟩ := S.exists_condition_unbounded_rankWitnesses φ v hp
  refine ⟨q, hqG, ?_⟩
  apply vopenka_witnessRank_embedding hVP _ (by definability) ρ
  intro δ hδ
  obtain ⟨α, ⟨τ, hτ⟩, hδα⟩ := hu δ hδ
  exact ⟨α, τ, hτ.1, hδα, hτ⟩

end SymmetricContext
end ZFVP
