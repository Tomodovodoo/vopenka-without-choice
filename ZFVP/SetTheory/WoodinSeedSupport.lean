import ZFVP.SetTheory.WoodinSeedMatrix

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSourceIndex_subset_iff {α β : V} [IsOrdinal α] [IsOrdinal β] :
    woodinSourceIndex α ⊆ woodinSourceIndex β ↔ α ⊆ β := by
  constructor
  · intro h x hx
    let := IsOrdinal.of_mem hx
    exact woodinSourceIndex_mem_iff.mp (h _ (woodinSourceIndex_mem_iff.mpr hx))
  · exact ordinalAdd_mono_right 1

theorem woodinSeed_support_iff {θ E C f a k : V} [IsOrdinal θ] [IsOrdinal k] :
    IsThreadSupport (woodinSourceIndex θ) (woodinSeedMatrix θ E C)
      (woodinInsertSeed θ f a) (woodinSourceIndex k) ↔ IsThreadSupport θ E f k := by
  constructor
  · rintro ⟨hk, hs⟩
    have hk' := woodinSourceIndex_mem_iff.mp hk
    refine ⟨hk', ?_⟩
    intro j hj hkj
    let := IsOrdinal.of_mem hj
    have hh := hs (woodinSourceIndex j) (woodinSourceIndex_mem_iff.mpr hj)
      (woodinSourceIndex_subset_iff.mpr hkj)
    simpa only [woodinSeedMatrix_at_sourceIndex hk' hj,
      woodinInsertSeed_at_sourceIndex hk', woodinInsertSeed_at_sourceIndex hj] using hh
  · rintro ⟨hk, hs⟩
    refine ⟨woodinSourceIndex_mem_iff.mpr hk, ?_⟩
    intro j hj hkj
    let := IsOrdinal.of_mem hj
    have hjn : j ≠ ∅ := by
      intro hz
      have hzero : (∅ : V) ∈ woodinSourceIndex k :=
        subset_ordinalAdd 1 k ∅ (by change (0 : V) ∈ succ 0; simp)
      have hh := hkj ∅ hzero
      rw [hz] at hh
      exact not_mem_empty hh
    have hrj : woodinRecursiveIndex j ∈ θ := (woodinRecursiveIndex_mem_iff hjn).mpr hj
    have hkrec : k ⊆ woodinRecursiveIndex j := woodinSourceIndex_subset_iff.mp
      (by simpa only [woodinSourceIndex_recursiveIndex _ hjn] using hkj)
    rw [← woodinSourceIndex_recursiveIndex j hjn,
      woodinSeedMatrix_at_sourceIndex hk hrj,
      woodinInsertSeed_at_sourceIndex hrj, woodinInsertSeed_at_sourceIndex hk]
    exact hs _ hrj hkrec

theorem woodinSeed_support_nonzero {θ E C f a l : V} [IsOrdinal θ] [IsOrdinal l]
    (hl : l ≠ ∅) :
    IsThreadSupport (woodinSourceIndex θ) (woodinSeedMatrix θ E C)
      (woodinInsertSeed θ f a) l ↔ IsThreadSupport θ E f (woodinRecursiveIndex l) := by
  simpa only [woodinSourceIndex_recursiveIndex l hl] using
    (woodinSeed_support_iff (θ := θ) (E := E) (C := C) (f := f) (a := a)
      (k := woodinRecursiveIndex l))

noncomputable def woodinSeedSectionColumn (θ t : V) : V :=
  definableGraph (woodinSourceIndex θ) (fun j ↦ ({∅} : V) ×ˢ {t ‘ j}) (by definability)

theorem woodinSeedSectionColumn_value {θ t j : V} (hj : j ∈ woodinSourceIndex θ) :
    ((woodinSeedSectionColumn θ t) ‘ j) ‘ ∅ = t ‘ j := by
  rw [woodinSeedSectionColumn, value_definableGraph _ _ _ hj]
  have hf : IsFunction (({∅} : V) ×ˢ {t ‘ j}) := by
    apply IsFunction.of_mem (show ({∅} : V) ×ˢ {t ‘ j} ∈ ({t ‘ j} : V) ^ ({∅} : V) from ?_)
    apply mem_function.intro
    · exact subset_refl _
    · intro x hx
      refine ⟨t ‘ j, kpair_mem_iff.mpr ⟨hx, by simp⟩, ?_⟩
      intro y hy
      exact mem_singleton_iff.mp (kpair_mem_iff.mp hy).2
  let := hf
  exact value_eq_of_kpair_mem (kpair_mem_iff.mpr ⟨by simp, by simp⟩)

noncomputable def woodinSeedSections (θ E t : V) : V :=
  woodinSeedMatrix θ E (woodinSeedSectionColumn θ (woodinInsertSeed θ t ∅))

theorem woodinSeed_support_exists_iff {θ E t f : V} [IsOrdinal θ]
    (hzero : (∅ : V) ∈ θ)
    (ht : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → (E ‘ ⟨i, j⟩ₖ) ‘ (t ‘ i) = t ‘ j) :
    (∃ k, IsThreadSupport (woodinSourceIndex θ) (woodinSeedSections θ E t)
      (woodinInsertSeed θ f ∅) k) ↔ ∃ k, IsThreadSupport θ E f k := by
  constructor
  · rintro ⟨k, hk⟩
    let := IsOrdinal.of_mem hk.1
    by_cases hz : k = ∅
    · subst k
      have hf : ∀ j ∈ θ, f ‘ j = t ‘ j := by
        intro j hj
        let := IsOrdinal.of_mem hj
        have hh := hk.2 (woodinSourceIndex j) (woodinSourceIndex_mem_iff.mpr hj)
          (empty_subset _)
        rw [woodinSeedSections, woodinSeedMatrix_zero (woodinSourceIndex_mem_iff.mpr hj),
          woodinInsertSeed_zero, woodinSeedSectionColumn_value (woodinSourceIndex_mem_iff.mpr hj),
          woodinInsertSeed_at_sourceIndex hj, woodinInsertSeed_at_sourceIndex hj] at hh
        exact hh
      refine ⟨∅, hzero, ?_⟩
      intro j hj h0j
      rw [hf j hj, hf ∅ hzero]
      exact (ht ∅ hzero j hj h0j).symm
    · exact ⟨woodinRecursiveIndex k, (woodinSeed_support_nonzero hz).mp hk⟩
  · rintro ⟨k, hk⟩
    let := IsOrdinal.of_mem hk.1
    exact ⟨woodinSourceIndex k, woodinSeed_support_iff.mpr hk⟩

theorem woodinInsertSeed_mem_directLimit {θ P π E t U f : V} [IsOrdinal θ]
    (hf : f ∈ forcingDirectLimit θ P π E U) (hU : (∅ : V) ∈ U) :
    woodinInsertSeed θ f ∅ ∈ forcingDirectLimit (woodinSourceIndex θ)
      (woodinInsertSeed θ P {∅}) (woodinSeedProjections θ P π) (woodinSeedSections θ E t) U := by
  obtain ⟨hi, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hf
  let := IsOrdinal.of_mem hk.1
  exact (mem_forcingDirectLimit_iff _ _ _ _ _ _).mpr
    ⟨woodinInsertSeed_mem_inverseLimit hi hU, woodinSourceIndex k, woodinSeed_support_iff.mpr hk⟩

theorem woodinRemoveSeed_mem_directLimit {θ P π E t U g : V} [IsOrdinal θ]
    (hzero : (∅ : V) ∈ θ)
    (ht : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → (E ‘ ⟨i, j⟩ₖ) ‘ (t ‘ i) = t ‘ j)
    (hg : g ∈ forcingDirectLimit (woodinSourceIndex θ)
      (woodinInsertSeed θ P {∅}) (woodinSeedProjections θ P π) (woodinSeedSections θ E t) U) :
    woodinRemoveSeed θ g ∈ forcingDirectLimit θ P π E U := by
  obtain ⟨hi, hs⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hg
  have hfun := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hi).1
  let := IsFunction.of_mem hfun
  refine (mem_forcingDirectLimit_iff _ _ _ _ _ _).mpr ⟨woodinRemoveSeed_mem_inverseLimit hi, ?_⟩
  apply (woodinSeed_support_exists_iff hzero ht).mp
  rw [woodinInsertSeed_remove (domain_eq_of_mem_function hfun) (woodinSeed_inverseLimit_zero hi)]
  exact hs

end ZFVP
