import ZFVP.ModelTheory.LastPointWitness
import ZFVP.ModelTheory.LastPointBound
import ZFVP.SetTheory.Collection

/-! Mohammd Proposition 6.5(i): eventual equality with the last point.
ZF Collection bounds the sources for all smaller last points at once. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem leastChoiceless_bounded_lastPointWitness {n : ℕ} {α γ δ : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ) (hδγ : δ ∈ γ) :
    ∃ β, IsOrdinal β ∧ ∀ θ, β ∈ θ → ¬LastPointWitness n α δ θ := by
  classical
  let := hγ.1
  let : IsOrdinal δ := IsOrdinal.of_mem hδγ
  by_contra hn
  have hu : ∀ β, IsOrdinal β → ∃ θ, β ∈ θ ∧ LastPointWitness n α δ θ := by
    intro β hβ
    by_contra hno
    apply hn
    refine ⟨β, hβ, ?_⟩
    intro θ hβθ hE
    exact hno ⟨θ, hβθ, hE⟩
  have hs := lastPointWitness_unbounded_supercompact hu
  have hδ := hs.extendible
  have hle := hγ.2.2 δ hδ.ordinal hδ
  exact mem_irrefl δ (hle δ hδγ)

theorem leastChoiceless_uniform_lastPointBound {n : ℕ} {α γ : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ) :
    ∃ β, IsOrdinal β ∧ ∀ θ, β ⊆ θ → ∀ δ ∈ γ, ¬LastPointWitness n α δ θ := by
  let R : V → V → Prop := fun δ β ↦ IsOrdinal β ∧ ∀ θ, β ∈ θ → ¬LastPointWitness n α δ θ
  have hR : ℒₛₑₜ-relation[V] R := by unfold R; definability
  obtain ⟨B, hB⟩ := collection γ R hR (fun δ hδ ↦ leastChoiceless_bounded_lastPointWitness hγ hδ)
  refine ⟨rank B, inferInstance, ?_⟩
  intro θ hβθ δ hδγ
  obtain ⟨β, hβB, hβ, hb⟩ := hB δ hδγ
  let := hβ
  have hβrank : β ∈ rank B := by simpa only [rank_of_ordinal] using rank_mem hβB
  exact hb θ (hβθ β hβrank)

theorem leastChoiceless_eventual_lastPoint {n : ℕ} {α γ : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ) :
    ∃ β, IsOrdinal β ∧ ∀ θ η f κ,
      β ⊆ θ → Cn (n + 2) θ → CnCofinal (n + 2) θ → Cn (n + 1) η → γ ∈ θ →
      IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f →
      IsCriticalPoint (hierarchy θ) f κ → α ∈ κ → θ ∈ f ‘ γ → lastPoint θ f = γ := by
  obtain ⟨β, hβ, hb⟩ := leastChoiceless_uniform_lastPointBound hγ
  refine ⟨β, hβ, ?_⟩
  intro θ η f κ hβθ hθ hlim hη hγθ hf hc hακ hmove
  let := hγ.1
  let := hθ.ordinal
  let := lastPoint_ordinal θ f
  have hle := rankEmbedding_lastPoint_subset_moved hθ hη hf hγθ hmove
  rcases IsOrdinal.subset_iff.mp hle with he | hl
  · exact he
  · exact False.elim (hb θ hβθ (lastPoint θ f) hl
      ⟨hθ, hlim, ordinal_mem_of_subset_mem hle hγθ, η, f, κ, hη, hf, hc, hακ, rfl⟩)

end ZFVP
