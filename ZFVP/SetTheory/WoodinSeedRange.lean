import ZFVP.SetTheory.WoodinSeedInsertion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinInsertSeed_range {θ f a : V} [IsOrdinal θ] [IsFunction f] (hf : domain f = θ) :
    range (woodinInsertSeed θ f a) = {a} ∪ range f := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
    have hi : i ∈ woodinSourceIndex θ := woodinInsertSeed_domain θ f a ▸ mem_domain_of_kpair_mem hiy
    have he := value_eq_of_kpair_mem hiy
    by_cases hz : i = ∅
    · subst i
      rw [woodinInsertSeed_zero] at he
      exact mem_union_iff.mpr (Or.inl (mem_singleton_iff.mpr he.symm))
    · let := IsOrdinal.of_mem hi
      rw [woodinInsertSeed_nonzero hi hz] at he
      have hr := (woodinRecursiveIndex_mem_iff hz).mpr hi
      exact mem_union_iff.mpr (Or.inr (mem_range_iff.mpr
        ⟨woodinRecursiveIndex i, kpair_mem_iff_value.mpr ⟨hf.symm ▸ hr, he⟩⟩))
  · intro hy
    rcases mem_union_iff.mp hy with hy | hy
    · have he := mem_singleton_iff.mp hy
      subst y
      have hz : (∅ : V) ∈ woodinSourceIndex θ :=
        subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
      exact mem_range_iff.mpr ⟨∅, kpair_mem_iff_value.mpr
        ⟨(woodinInsertSeed_domain θ f a).symm ▸ hz, woodinInsertSeed_zero θ f a⟩⟩
    · obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
      have hi : i ∈ θ := hf ▸ mem_domain_of_kpair_mem hiy
      let := IsOrdinal.of_mem hi
      exact mem_range_iff.mpr ⟨woodinSourceIndex i, kpair_mem_iff_value.mpr
        ⟨(woodinInsertSeed_domain θ f a).symm ▸ woodinSourceIndex_mem_iff.mpr hi,
          (woodinInsertSeed_at_sourceIndex hi).trans (value_eq_of_kpair_mem hiy)⟩⟩

theorem woodinInsertSeed_union_range {θ f a : V} [IsOrdinal θ] [IsFunction f] (hf : domain f = θ) :
    ⋃ˢ range (woodinInsertSeed θ f a) = a ∪ ⋃ˢ range f := by
  rw [woodinInsertSeed_range hf]
  apply mem_ext
  intro x
  simp only [mem_sUnion_iff, mem_union_iff, mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl | hy, hxy⟩
    · exact Or.inl hxy
    · exact Or.inr ⟨y, hy, hxy⟩
  · rintro (hx | ⟨y, hy, hxy⟩)
    · exact ⟨a, Or.inl rfl, hx⟩
    · exact ⟨y, Or.inr hy, hxy⟩

end ZFVP
