import ZFVP.SetTheory.Collection

/-! A set of bounded definable ordinal fibers has a uniform ordinal bound. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem boundedOrdinalFibers_uniform (P : V) (A : V → V → Prop) (hA : ℒₛₑₜ-relation A) :
    ∃ δ : V, IsOrdinal δ ∧ ∀ p ∈ P,
      (∃ β : V, IsOrdinal β ∧ ∀ α, A p α → α ∈ β) → ∀ α, A p α → α ∈ δ := by
  let B : V → V → Prop := fun p β ↦ IsOrdinal β ∧ ∀ α, A p α → α ∈ β
  have hB : ℒₛₑₜ-relation B := by unfold B; definability
  let D : V := {p ∈ P ; ∃ β, B p β}
  obtain ⟨C, hC, hCr⟩ := strongCollection D B hB (fun p hp ↦ (mem_sep_iff.mp hp).2)
  have hδ : IsOrdinal (⋃ˢ C) := IsOrdinal.sUnion (fun β hβ ↦ by
    obtain ⟨p, _, hpβ⟩ := hCr β hβ
    exact hpβ.1)
  refine ⟨⋃ˢ C, hδ, ?_⟩
  intro p hp hb α hα
  obtain ⟨β, hβC, hβ⟩ := hC p (mem_sep_iff.mpr ⟨hp, hb⟩)
  exact subset_sUnion_of_mem hβC α (hβ.2 α hα)

theorem exists_unbounded_ordinal_fiber (P : V) (G : Set V) (hGP : ∀ p ∈ G, p ∈ P)
    (A : V → V → Prop) (hA : ℒₛₑₜ-relation A)
    (hord : ∀ p ∈ P, ∀ α, A p α → IsOrdinal α)
    (hu : ∀ δ : V, IsOrdinal δ → ∃ p ∈ G, ∃ α, A p α ∧ δ ∈ α) :
    ∃ p ∈ G, ∀ δ : V, IsOrdinal δ → ∃ α, A p α ∧ δ ∈ α := by
  classical
  by_contra hn
  have hb (p : V) (hpG : p ∈ G) : ∃ β : V, IsOrdinal β ∧ ∀ α, A p α → α ∈ β := by
    by_contra hnb
    apply hn
    refine ⟨p, hpG, ?_⟩
    intro δ hδ
    by_contra hnone
    have : IsOrdinal δ := hδ
    apply hnb
    refine ⟨succ δ, inferInstance, ?_⟩
    intro α hα
    have : IsOrdinal α := hord p (hGP p hpG) α hα
    rcases IsOrdinal.mem_trichotomy α δ with hlt | heq | hgt
    · exact mem_succ_iff.mpr (Or.inr hlt)
    · exact mem_succ_iff.mpr (Or.inl heq)
    · exact False.elim (hnone ⟨α, hα, hgt⟩)
  obtain ⟨δ, hδ, hbound⟩ := boundedOrdinalFibers_uniform P A hA
  obtain ⟨p, hpG, α, hα, hδα⟩ := hu δ hδ
  have hαδ := hbound p (hGP p hpG) (hb p hpG) α hα
  have : IsOrdinal δ := hδ
  exact mem_irrefl δ ((inferInstance : IsTransitive δ).mem_trans hδα hαδ)

end ZFVP
