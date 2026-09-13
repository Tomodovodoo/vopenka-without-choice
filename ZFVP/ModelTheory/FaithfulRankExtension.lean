import ZFVP.ModelTheory.FaithfulExtension
import ZFVP.ModelTheory.RankPowersetExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
  [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Enayat Lemma 4.3: Separation in each induced expansion recovers all
subsets of old sets. -/
theorem IsFaithful.isPowersetPreserving {j : MembershipEndExtension V W}
    (h : j.IsFaithful) : j.IsPowersetPreserving := by
  intro a b hba
  obtain ⟨c, hc⟩ := (h (fun y ↦ y ∈ b) (by definability)).isClass a
  refine ⟨c, ?_⟩
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (j.mem_map_iff c y).mp hy
    exact ((hc x).mp hx).2
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (j.mem_map_iff a y).mp (hba y hy)
    exact (j.mem_iff x c).mpr ((hc x).mpr ⟨hx, hy⟩)

theorem IsFaithful.isRankExtension {j : MembershipEndExtension V W}
    (h : j.IsFaithful) : j.IsRankExtension := h.isPowersetPreserving.isRankExtension

theorem IsPowersetPreserving.map_mem_hierarchy_of_new {j : MembershipEndExtension V W}
    (h : j.IsPowersetPreserving) {δ : W} [IsOrdinal δ]
    (hnew : ∀ α : V, j α ≠ δ) (x : V) : j x ∈ hierarchy δ := by
  rw [mem_hierarchy_iff_rank_mem]
  simpa only [rank_of_ordinal] using h.isRankExtension x δ hnew

theorem IsPowersetPreserving.exists_new_ordinal {j : MembershipEndExtension V W}
    (h : j.IsPowersetPreserving) (hp : j.IsProper) :
    ∃ δ : W, IsOrdinal δ ∧ ∀ α : V, j α ≠ δ := by
  obtain ⟨b, hb⟩ := hp
  refine ⟨rank b, inferInstance, fun α hα ↦ ?_⟩
  have : IsOrdinal α := (j.ordinal_iff α).mp (hα ▸ (inferInstance : IsOrdinal (rank b)))
  have hsub : b ⊆ j (hierarchy α) := by
    rw [h.map_hierarchy α, hα]
    exact subset_hierarchy_rank b
  obtain ⟨c, hc⟩ := h (hierarchy α) b hsub
  exact hb c hc

end MembershipEndExtension
end ZFVP
