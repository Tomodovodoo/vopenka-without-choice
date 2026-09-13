import ZFVP.SetTheory.Hierarchy

/-! Ordinal addition by internal ZF recursion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def ordinalAddStep (α f : V) : V :=
  α ∪ ⋃ˢ repl succ (by definability) (range f)

instance ordinalAddStep_definable (α : V) : ℒₛₑₜ-function₁[V] (ordinalAddStep α) := by
  unfold ordinalAddStep
  definability

noncomputable def ordinalAdd (α β : V) : V :=
  Replacement.transfiniteRec (ordinalAddStep α) (ordinalAddStep_definable α) β

instance ordinalAdd_right_definable (α : V) : ℒₛₑₜ-function₁[V] (ordinalAdd α) :=
  Replacement.transfiniteRec_definable (ordinalAddStep_definable α)

theorem mem_ordinalAdd_iff (α β x : V) [IsOrdinal β] :
    x ∈ ordinalAdd α β ↔ x ∈ α ∨ ∃ γ ∈ β, x ∈ succ (ordinalAdd α γ) := by
  have hr := Replacement.transfiniteRec_spec (ordinalAddStep α)
    (ordinalAddStep_definable α) (IsOrdinal.toOrdinal β)
  change ordinalAdd α β = ordinalAddStep α
    (definableGraph β (ordinalAdd α) (ordinalAdd_right_definable α)) at hr
  rw [hr]
  simp only [ordinalAddStep, mem_union_iff, mem_sUnion_iff, repl_spec, range_definableGraph]
  constructor
  · rintro (h | ⟨p, ⟨y, ⟨γ, hγ, rfl⟩, rfl⟩, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨γ, hγ, hx⟩
  · rintro (h | ⟨γ, hγ, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨succ (ordinalAdd α γ), ⟨ordinalAdd α γ, ⟨γ, hγ, rfl⟩, rfl⟩, hx⟩

instance ordinalAdd_ordinal (α β : V) [IsOrdinal α] [IsOrdinal β] :
    IsOrdinal (ordinalAdd α β) := by
  apply transfinite_induction (P := fun γ : V ↦ IsOrdinal (ordinalAdd α γ))
    (by definability) ?_ (IsOrdinal.toOrdinal β)
  intro γ ih
  apply IsOrdinal.of_transitive_of_isOrdinal
  · constructor
    intro x hx z hz
    rcases (mem_ordinalAdd_iff α γ x).mp hx with hx | ⟨δ, hδ, hx⟩
    · exact (mem_ordinalAdd_iff α γ z).mpr (Or.inl (IsOrdinal.toIsTransitive.mem_trans hz hx))
    · have : IsOrdinal δ := IsOrdinal.of_mem hδ
      have : IsOrdinal (ordinalAdd α δ) := ih (IsOrdinal.toOrdinal δ) hδ
      exact (mem_ordinalAdd_iff α γ z).mpr
        (Or.inr ⟨δ, hδ, IsOrdinal.toIsTransitive.mem_trans hz hx⟩)
  · intro x hx
    rcases (mem_ordinalAdd_iff α γ x).mp hx with hx | ⟨δ, hδ, hx⟩
    · exact IsOrdinal.of_mem hx
    · have : IsOrdinal δ := IsOrdinal.of_mem hδ
      have : IsOrdinal (ordinalAdd α δ) := ih (IsOrdinal.toOrdinal δ) hδ
      exact IsOrdinal.of_mem hx

theorem ordinalAdd_zero (α : V) : ordinalAdd α ∅ = α := by
  ext x
  simp [mem_ordinalAdd_iff]

theorem subset_ordinalAdd (α β : V) [IsOrdinal β] : α ⊆ ordinalAdd α β :=
  fun x hx ↦ (mem_ordinalAdd_iff α β x).mpr (Or.inl hx)

theorem ordinalAdd_mem {α β γ : V} [IsOrdinal γ] (h : β ∈ γ) :
    ordinalAdd α β ∈ ordinalAdd α γ :=
  (mem_ordinalAdd_iff α γ _).mpr (Or.inr ⟨β, h, by simp⟩)

theorem ordinalAdd_mono_right (α : V) {β γ : V} [IsOrdinal β] [IsOrdinal γ]
    (h : β ⊆ γ) : ordinalAdd α β ⊆ ordinalAdd α γ := by
  intro x hx
  rcases (mem_ordinalAdd_iff α β x).mp hx with hx | ⟨δ, hδ, hx⟩
  · exact (mem_ordinalAdd_iff α γ x).mpr (Or.inl hx)
  · exact (mem_ordinalAdd_iff α γ x).mpr (Or.inr ⟨δ, h δ hδ, hx⟩)

theorem ordinalAdd_succ (α β : V) [IsOrdinal α] [IsOrdinal β] :
    ordinalAdd α (succ β) = succ (ordinalAdd α β) := by
  ext x
  rw [mem_ordinalAdd_iff]
  constructor
  · rintro (hx | ⟨γ, hγ, hx⟩)
    · exact mem_succ_iff.mpr (Or.inr (subset_ordinalAdd α β x hx))
    · rcases mem_succ_iff.mp hγ with rfl | hγ
      · exact hx
      · have hlt : ordinalAdd α γ ∈ ordinalAdd α β := ordinalAdd_mem hγ
        have hm : x ∈ ordinalAdd α β := by
          rcases mem_succ_iff.mp hx with rfl | hx
          · exact hlt
          · exact IsOrdinal.toIsTransitive.mem_trans hx hlt
        exact mem_succ_iff.mpr (Or.inr hm)
  · intro hx
    exact Or.inr ⟨β, by simp, hx⟩

theorem ordinalAdd_limit (α β : V) [IsOrdinal α] [IsOrdinal β] [IsNonempty β]
    (hβ : ∀ γ ∈ β, succ γ ∈ β) (x : V) :
    x ∈ ordinalAdd α β ↔ ∃ γ ∈ β, x ∈ ordinalAdd α γ := by
  rw [mem_ordinalAdd_iff]
  constructor
  · rintro (hx | ⟨γ, hγ, hx⟩)
    · exact ⟨∅, IsOrdinal.empty_mem_iff_nonempty.mpr inferInstance, by
        simpa only [ordinalAdd_zero] using hx⟩
    · have : IsOrdinal γ := IsOrdinal.of_mem hγ
      exact ⟨succ γ, hβ γ hγ, by simpa only [ordinalAdd_succ] using hx⟩
  · rintro ⟨γ, hγ, hx⟩
    have : IsOrdinal γ := IsOrdinal.of_mem hγ
    exact (mem_ordinalAdd_iff α β x).mp
      (ordinalAdd_mono_right α (IsOrdinal.toIsTransitive.transitive γ hγ) x hx)

theorem ordinalAdd_omega_gt (α : V) : α ∈ ordinalAdd α (ω : V) := by
  have h : ordinalAdd α ∅ ∈ ordinalAdd α (ω : V) := ordinalAdd_mem empty_mem_ω
  simpa only [ordinalAdd_zero] using h

theorem ordinalAdd_omega_succ_closed (α : V) [IsOrdinal α] {β : V}
    (hβ : β ∈ ordinalAdd α (ω : V)) : succ β ∈ ordinalAdd α (ω : V) := by
  obtain ⟨n, hn, hβn⟩ := (ordinalAdd_limit α ω (fun _ ↦ ω_succ_closed) β).mp hβ
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have hs : succ β ⊆ ordinalAdd α n := by
    intro x hx
    rcases mem_succ_iff.mp hx with rfl | hx
    · exact hβn
    · exact IsOrdinal.toIsTransitive.mem_trans hx hβn
  exact (mem_ordinalAdd_iff α ω (succ β)).mpr
    (Or.inr ⟨n, hn, mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hs)⟩)

end ZFVP
