import ZFVP.SetTheory.RankMarkerStructures

/-! Full arbitrary-language VP supplies arbitrarily high internal ZF rank models. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem vopenka_rankCriterion_unbounded
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (α : V) [IsOrdinal α] : ∃ κ : V, α ∈ κ ∧ IsRankCriterionHeight κ :=
  vopenka_direct_rankCriterion_unbounded hVP α

theorem vopenka_internalZFRanks_unbounded
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (α : V) [IsOrdinal α] : ∃ θ : V, IsOrdinal θ ∧ α ∈ θ ∧ IsInternalZFModel (hierarchy θ) := by
  obtain ⟨θ, hαθ, hθ⟩ := vopenka_rankCriterion_unbounded hVP α
  exact ⟨θ, hθ.1, hαθ, hθ.internalZFModel⟩

def IsLeastZFRankAbove (α θ : V) : Prop :=
  IsLeastOrdinal (fun δ ↦ α ∈ δ ∧ IsInternalZFModel (hierarchy δ)) θ

instance isLeastZFRankAbove_definable : ℒₛₑₜ-relation[V] IsLeastZFRankAbove := by
  unfold IsLeastZFRankAbove IsLeastOrdinal
  definability

theorem leastZFRankAbove_existsUnique
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (α : V) [IsOrdinal α] : ∃! θ : V, IsLeastZFRankAbove α θ :=
  leastOrdinal_existsUnique _ (by definability) (vopenka_internalZFRanks_unbounded hVP α)

end ZFVP
