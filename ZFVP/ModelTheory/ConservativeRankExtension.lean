import ZFVP.ModelTheory.ConservativeExtension
import ZFVP.ModelTheory.RankPowersetExtension

/-! First steps of Enayat's Theorem 4.4 in "Models of set theory: extensions and dead ends",
in the conservative case.

Enayat's Lemma 4.3 says a faithful end extension of models of ZF is a rank extension. A
conservative end extension is faithful, and in the conservative case the argument is short: the
subset of the smaller model cut out by a set of the larger one is definable there, so Separation
collects it, which is powerset preservation, hence a rank extension by Remark 2.6(e). From that
one gets an ordinal of the larger model that is not old, and one above the rank of any prescribed
old set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
  [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A conservative end extension is powerset-preserving. Given `b ⊆ j a`, conservativity makes
`fun x ↦ j x ∈ b` definable in the smaller model, and Separation turns it into a set. -/
theorem IsConservative.isPowersetPreserving {j : MembershipEndExtension V W}
    (h : j.IsConservative) : j.IsPowersetPreserving := by
  intro a b hba
  have hD : ℒₛₑₜ-predicate[W] (fun y : W ↦ y ∈ b) := by definability
  have hpull : ℒₛₑₜ-predicate[V] (fun x : V ↦ j x ∈ b) := h _ hD
  refine ⟨sep a (fun x : V ↦ j x ∈ b) hpull, ?_⟩
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (j.mem_map_iff _ y).mp hy
    exact (mem_sep_iff.mp hx).2
  · intro hy
    obtain ⟨x, hxa, rfl⟩ := (j.mem_map_iff a y).mp (hba y hy)
    exact (j.mem_iff x _).mpr (mem_sep_iff.mpr ⟨hxa, hy⟩)

/-- A conservative end extension is a rank extension. -/
theorem IsConservative.isRankExtension {j : MembershipEndExtension V W}
    (h : j.IsConservative) : j.IsRankExtension :=
  h.isPowersetPreserving.isRankExtension

/-- The rank of a new element of a conservative end extension is a new ordinal. If that rank
were `j α`, then the element would sit inside `hierarchy (j α) = j (hierarchy α)`, so powerset
preservation would make it old. -/
theorem IsConservative.map_ne_rank {j : MembershipEndExtension V W} (h : j.IsConservative)
    {b : W} (hb : ∀ v : V, j v ≠ b) (α : V) : j α ≠ rank b := by
  intro hα
  have hjord : IsOrdinal (j α) := hα ▸ (inferInstance : IsOrdinal (rank b))
  haveI hord : IsOrdinal α := (j.ordinal_iff α).mp hjord
  have hsub : b ⊆ j (hierarchy α) := by
    rw [h.isPowersetPreserving.map_hierarchy α, hα]
    exact subset_hierarchy_rank b
  obtain ⟨c, hc⟩ := h.isPowersetPreserving (hierarchy α) b hsub
  exact hb c hc

/-- A proper conservative end extension has an ordinal that is not the image of any ordinal of
the smaller model. -/
theorem IsConservative.exists_new_ordinal {j : MembershipEndExtension V W}
    (h : j.IsConservative) (hp : j.IsProper) :
    ∃ δ : W, IsOrdinal δ ∧ ∀ α : V, j α ≠ δ := by
  obtain ⟨b, hb⟩ := hp
  exact ⟨rank b, inferInstance, h.map_ne_rank hb⟩

/-- The same new ordinal lies above the rank of any prescribed old set, because a conservative
end extension is a rank extension. -/
theorem IsConservative.exists_new_ordinal_above {j : MembershipEndExtension V W}
    (h : j.IsConservative) (hp : j.IsProper) (a : V) :
    ∃ δ : W, IsOrdinal δ ∧ (∀ α : V, j α ≠ δ) ∧ rank (j a) ∈ δ := by
  obtain ⟨b, hb⟩ := hp
  exact ⟨rank b, inferInstance, h.map_ne_rank hb, h.isRankExtension a b hb⟩

end MembershipEndExtension
end ZFVP
