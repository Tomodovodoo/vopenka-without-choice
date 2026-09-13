import ZFVP.ModelTheory.RankEmbeddingAction

/-! Least moved ordinals of internal elementary graphs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCriticalPoint (A f κ : V) : Prop :=
  IsLeastOrdinal (fun α ↦ α ∈ A ∧ f ‘ α ≠ α) κ

instance isCriticalPoint_definable : ℒₛₑₜ-relation₃[V] IsCriticalPoint := by
  unfold IsCriticalPoint IsLeastOrdinal
  definability

namespace IsCodedMembershipEmbedding

variable {A B f : V} [IsTransitive A] [IsTransitive B]

theorem value_ordinal (h : IsCodedMembershipEmbedding A B f) {α : V}
    (hα : IsOrdinal α) (hαA : α ∈ A) : IsOrdinal (f ‘ α) :=
  (h.bounded_defined_iff isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
    ![α] (by simp [hαA])).mp hα

theorem ordinal_subset_value (h : IsCodedMembershipEmbedding A B f) {α : V}
    (hα : IsOrdinal α) (hαA : α ∈ A) : α ⊆ f ‘ α := by
  have hall : ∀ α : Ordinal V, (α : V) ∈ A → (α : V) ⊆ f ‘ (α : V) := by
    apply transfinite_induction (P := fun α : V ↦ α ∈ A → α ⊆ f ‘ α) (by definability)
    intro α ih hαA β hβα
    have hβA := (inferInstance : IsTransitive A).mem_trans hβα hαA
    have : IsOrdinal β := IsOrdinal.of_mem hβα
    have : IsOrdinal (f ‘ β) := h.value_ordinal inferInstance hβA
    have : IsOrdinal (f ‘ (α : V)) := h.value_ordinal inferInstance hαA
    have hβ : β ⊆ f ‘ β := ih (IsOrdinal.toOrdinal β) hβα hβA
    have hm := (h.value_mem_iff hβA hαA).mpr hβα
    rcases IsOrdinal.subset_iff.mp hβ with he | hl
    · exact he.symm ▸ hm
    · exact IsOrdinal.toIsTransitive.mem_trans hl hm
  let := hα
  exact hall (IsOrdinal.toOrdinal α) hαA

end IsCodedMembershipEmbedding

namespace IsCriticalPoint

variable {A f κ : V}

theorem ordinal (hκ : IsCriticalPoint A f κ) : IsOrdinal κ := hκ.1

theorem mem_domain (hκ : IsCriticalPoint A f κ) : κ ∈ A := hκ.2.1.1

theorem moved (hκ : IsCriticalPoint A f κ) : f ‘ κ ≠ κ := hκ.2.1.2

theorem fixed_below [IsTransitive A] (hκ : IsCriticalPoint A f κ) {α : V}
    (hα : α ∈ κ) : f ‘ α = α := by
  classical
  let := hκ.ordinal
  by_contra hn
  have ha : IsOrdinal α := IsOrdinal.of_mem hα
  have hle := hκ.2.2 α ha ⟨(inferInstance : IsTransitive A).mem_trans hα hκ.mem_domain, hn⟩
  exact mem_irrefl α (hle α hα)

theorem unique {μ : V} (hκ : IsCriticalPoint A f κ) (hμ : IsCriticalPoint A f μ) : κ = μ :=
  subset_antisymm (hκ.2.2 μ hμ.1 hμ.2.1) (hμ.2.2 κ hκ.1 hκ.2.1)

theorem lt_value {B : V} [IsTransitive A] [IsTransitive B]
    (hκ : IsCriticalPoint A f κ) (h : IsCodedMembershipEmbedding A B f) : κ ∈ f ‘ κ := by
  let := hκ.ordinal
  let := h.value_ordinal hκ.ordinal hκ.mem_domain
  rcases IsOrdinal.subset_iff.mp (h.ordinal_subset_value hκ.ordinal hκ.mem_domain) with he | hl
  · exact False.elim (hκ.moved he.symm)
  · exact hl

theorem omega_lt {B : V} [IsCodingSupport A] [IsTransitive B]
    (hκ : IsCriticalPoint A f κ) (h : IsCodedMembershipEmbedding A B f) : (ω : V) ∈ κ := by
  let := hκ.ordinal
  rcases IsOrdinal.mem_trichotomy κ (ω : V) with hl | he | hg
  · exact False.elim (hκ.moved (h.value_natural hl))
  · exact False.elim (hκ.moved (he ▸ h.value_omega IsCodingSupport.omega_mem))
  · exact hg

end IsCriticalPoint

theorem rankEmbedding_criticalPoint_existsUnique {k l : ℕ} {δ ε f : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hne : ∃ x ∈ hierarchy δ, f ‘ x ≠ x) :
    ∃! κ, IsCriticalPoint (hierarchy δ) f κ :=
  leastOrdinal_existsUnique _ (by definability) (rankEmbedding_nontrivial_moves_ordinal hδ hε h hne)

theorem rankEmbedding_fixed_below_criticalPoint {k l : ℕ} {δ ε f κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) :
    ∀ x ∈ hierarchy κ, f ‘ x = x := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hκ.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  let := hierarchy_transitive κ
  have hVκ := hδ.hierarchy_closed hκ.ordinal hκ.mem_domain
  have hinc : ∀ x ∈ hierarchy κ, x ∈ hierarchy δ :=
    fun _ hx ↦ (hierarchy_transitive δ).mem_trans hx hVκ
  apply projectedRank_induction (hierarchy κ) id (by definability) (fun x ↦ f ‘ x = x) (by definability)
  intro x hx ih
  have hrκ := (mem_hierarchy_iff_rank_mem x κ).mp hx
  have hr : rank (f ‘ x) = rank x :=
    (rankEmbedding_value_rank hδ hε h (hinc x hx)).symm.trans (hκ.fixed_below hrκ)
  have hfx : f ‘ x ∈ hierarchy κ := by
    rw [mem_hierarchy_iff_rank_mem, hr]
    exact hrκ
  apply mem_ext
  intro y
  constructor
  · intro hy
    have hyκ := (hierarchy_transitive κ).mem_trans hy hfx
    have hiy := ih y hyκ (hr ▸ rank_mem hy)
    exact (h.value_mem_iff (hinc y hyκ) (hinc x hx)).mp (by simpa [hiy] using hy)
  · intro hy
    have hyκ := (hierarchy_transitive κ).mem_trans hy hx
    have hiy := ih y hyκ (rank_mem hy)
    simpa [hiy] using (h.value_mem_iff (hinc y hyκ) (hinc x hx)).mpr hy

end ZFVP
