import ZFVP.SetTheory.CofinalityCardinal

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cofinal_prefix_bounded {α f i : V} [IsOrdinal α]
    (hf : IsCofinalMap α (internalCofinality α) f) (hi : i ∈ internalCofinality α) :
    ∃ ξ ∈ α, ∀ j ∈ i, f ‘ j ∈ ξ := by
  classical
  have : IsFunction f := IsFunction.of_mem hf.1
  have : IsOrdinal i := IsOrdinal.of_mem hi
  have hsub : i ⊆ internalCofinality α := IsOrdinal.toIsTransitive.transitive _ hi
  have hr : f ↾ i ∈ α ^ i := restrict_mem_function_of_values
    (by simpa only [domain_eq_of_mem_function hf.1] using hsub)
    (fun j hj ↦ function_value_mem hf.1 (hsub j hj))
  have hn := no_cofinalMap_below_cofinality hi
  have hbad : ¬∀ ξ ∈ α, ∃ j ∈ i, ξ ⊆ f ‘ j := by
    intro h
    apply hn
    refine ⟨f ↾ i, hr, ?_⟩
    intro ξ hξ
    obtain ⟨j, hj, hle⟩ := h ξ hξ
    refine ⟨j, hj, ?_⟩
    rw [value_restrict (by simpa only [domain_eq_of_mem_function hf.1] using hsub j hj) hj]
    exact hle
  push Not at hbad
  obtain ⟨ξ, hξ, hξj⟩ := hbad
  refine ⟨ξ, hξ, ?_⟩
  intro j hj
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have : IsOrdinal (f ‘ j) := IsOrdinal.of_mem (function_value_mem hf.1 (hsub j hj))
  exact IsOrdinal.mem_iff_subset_and_not_subset.mpr
    ⟨(IsOrdinal.subset_or_supset (f ‘ j) ξ).resolve_right (hξj j hj), hξj j hj⟩

noncomputable def cofinalEnvelope (f i : V) : V := (⋃ˢ range (f ↾ i)) ∪ f ‘ i

instance cofinalEnvelope_definable : ℒₛₑₜ-function₂[V] cofinalEnvelope := by
  unfold cofinalEnvelope
  definability

theorem cofinalEnvelope_mem {α f i : V} [IsOrdinal α]
    (hf : IsCofinalMap α (internalCofinality α) f) (hi : i ∈ internalCofinality α) :
    cofinalEnvelope f i ∈ α := by
  have : IsFunction f := IsFunction.of_mem hf.1
  obtain ⟨ξ, hξ, hbound⟩ := cofinal_prefix_bounded hf hi
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hs : ⋃ˢ range (f ↾ i) ⊆ ξ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨j, hjy⟩ := mem_range_iff.mp hy
    obtain ⟨hjf, hj⟩ := kpair_mem_restrict_iff.mp hjy
    have hv := value_eq_of_kpair_mem hjf
    exact IsOrdinal.toIsTransitive.transitive y (hv ▸ hbound j hj) x hxy
  have hord : IsOrdinal (⋃ˢ range (f ↾ i)) := IsOrdinal.sUnion (by
    intro y hy
    obtain ⟨j, hjy⟩ := mem_range_iff.mp hy
    exact IsOrdinal.of_mem (mem_of_mem_functions hf.1 (kpair_mem_restrict_iff.mp hjy).1).2)
  have hsup : ⋃ˢ range (f ↾ i) ∈ α := by
    rcases IsOrdinal.subset_iff.mp hs with heq | hlt
    · exact heq ▸ hξ
    · exact IsOrdinal.toIsTransitive.transitive ξ hξ _ hlt
  have hv := function_value_mem hf.1 hi
  have : IsOrdinal (f ‘ i) := IsOrdinal.of_mem hv
  rcases IsOrdinal.subset_or_supset (⋃ˢ range (f ↾ i)) (f ‘ i) with h | h
  · simpa only [cofinalEnvelope, union_eq_iff_left.mpr h] using hv
  · simpa only [cofinalEnvelope, union_eq_iff_right.mpr h] using hsup

theorem cofinalEnvelope_mono {α f i j : V} [IsOrdinal α]
    (hf : f ∈ α ^ internalCofinality α) (hi : i ∈ internalCofinality α)
    (hj : j ∈ internalCofinality α) (hij : i ⊆ j) : cofinalEnvelope f i ⊆ cofinalEnvelope f j := by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsOrdinal i := IsOrdinal.of_mem hi
  have : IsOrdinal j := IsOrdinal.of_mem hj
  rcases IsOrdinal.subset_iff.mp hij with rfl | hij'
  · exact subset_refl _
  intro x hx
  apply subset_union_left _ _ x
  rcases mem_union_iff.mp hx with hx | hx
  · obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨k, hky⟩ := mem_range_iff.mp hy
    obtain ⟨hkf, hk⟩ := kpair_mem_restrict_iff.mp hky
    exact mem_sUnion_iff.mpr ⟨y, mem_range_of_kpair_mem
      (kpair_mem_restrict_iff.mpr ⟨hkf, hij k hk⟩), hxy⟩
  · exact mem_sUnion_iff.mpr ⟨f ‘ i, mem_range_of_kpair_mem
      (kpair_mem_restrict_iff.mpr ⟨kpair_value_mem
        (by simpa only [domain_eq_of_mem_function hf] using hi), hij'⟩), hx⟩

theorem monotone_cofinalMap_exists (α : V) [IsOrdinal α] :
    ∃ F, IsCofinalMap α (internalCofinality α) F ∧
      ∀ i ∈ internalCofinality α, ∀ j ∈ internalCofinality α, i ⊆ j → F ‘ i ⊆ F ‘ j := by
  obtain ⟨f, hf⟩ := cofinalMap_exists α
  let F := definableGraph (internalCofinality α) (cofinalEnvelope f) (by definability)
  have hF : F ∈ α ^ internalCofinality α := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun i hi ↦ cofinalEnvelope_mem hf hi)
  have hval (i : V) (hi : i ∈ internalCofinality α) : F ‘ i = cofinalEnvelope f i :=
    value_definableGraph _ _ _ hi
  refine ⟨F, ⟨hF, ?_⟩, ?_⟩
  · intro ξ hξ
    obtain ⟨i, hi, hle⟩ := hf.2 ξ hξ
    refine ⟨i, hi, ?_⟩
    rw [hval i hi]
    exact subset_trans hle (subset_union_right _ _)
  · intro i hi j hj hij
    rw [hval i hi, hval j hj]
    exact cofinalEnvelope_mono hf.1 hi hj hij

theorem monotone_cofinalMap_compose {α β γ F g : V}
    (hF : IsCofinalMap α β F) (hg : IsCofinalMap β γ g)
    (hmono : ∀ i ∈ β, ∀ j ∈ β, i ⊆ j → F ‘ i ⊆ F ‘ j) :
    IsCofinalMap α γ (compose g F) := by
  have hcomp := compose_function hg.1 hF.1
  have : IsFunction g := IsFunction.of_mem hg.1
  have : IsFunction F := IsFunction.of_mem hF.1
  have : IsFunction (compose g F) := IsFunction.of_mem hcomp
  refine ⟨hcomp, ?_⟩
  intro ξ hξ
  obtain ⟨i, hi, hξi⟩ := hF.2 ξ hξ
  obtain ⟨j, hj, hij⟩ := hg.2 i hi
  have hgj := function_value_mem hg.1 hj
  have hval : (compose g F) ‘ j = F ‘ (g ‘ j) := value_eq_of_kpair_mem
    (kpair_mem_compose_iff.mpr ⟨g ‘ j,
      kpair_value_mem (by simpa only [domain_eq_of_mem_function hg.1] using hj),
      kpair_value_mem (by simpa only [domain_eq_of_mem_function hF.1] using hgj)⟩)
  refine ⟨j, hj, ?_⟩
  rw [hval]
  exact subset_trans hξi (hmono i hi (g ‘ j) hgj hij)

theorem internalCofinality_idempotent (α : V) [IsOrdinal α] :
    internalCofinality (internalCofinality α) = internalCofinality α := by
  apply SetTheory.subset_antisymm (internalCofinality_subset _)
  obtain ⟨F, hF, hmono⟩ := monotone_cofinalMap_exists α
  obtain ⟨g, hg⟩ := cofinalMap_exists (internalCofinality α)
  exact internalCofinality_minimal (monotone_cofinalMap_compose hF hg hmono)

theorem map_below_cofinality_bounded {α β f : V} [IsOrdinal α]
    (hβ : β ∈ internalCofinality α) (hf : f ∈ α ^ β) :
    ∃ ξ ∈ α, ∀ i ∈ β, f ‘ i ∈ ξ := by
  classical
  have hn : ¬∀ ξ ∈ α, ∃ i ∈ β, ξ ⊆ f ‘ i :=
    fun h ↦ no_cofinalMap_below_cofinality hβ ⟨f, hf, h⟩
  push Not at hn
  obtain ⟨ξ, hξ, hbound⟩ := hn
  refine ⟨ξ, hξ, ?_⟩
  intro i hi
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have : IsOrdinal (f ‘ i) := IsOrdinal.of_mem (function_value_mem hf hi)
  exact IsOrdinal.mem_iff_subset_and_not_subset.mpr
    ⟨(IsOrdinal.subset_or_supset (f ‘ i) ξ).resolve_right (hbound i hi), hbound i hi⟩

theorem union_range_below_cofinality {α β f : V} [IsOrdinal α]
    (hβ : β ∈ internalCofinality α) (hf : f ∈ α ^ β) : ⋃ˢ range f ∈ α := by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsOrdinal (⋃ˢ range f) := IsOrdinal.sUnion
    (fun x hx ↦ IsOrdinal.of_mem (range_subset_of_mem_function hf x hx))
  obtain ⟨ξ, hξ, hbound⟩ := map_below_cofinality_bounded hβ hf
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hs : ⋃ˢ range f ⊆ ξ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
    have hi : i ∈ β := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hiy
    have hyξ : y ∈ ξ := value_eq_of_kpair_mem hiy ▸ hbound i hi
    exact IsOrdinal.toIsTransitive.transitive y hyξ x hxy
  rcases IsOrdinal.subset_iff.mp hs with heq | hlt
  · exact heq ▸ hξ
  · exact IsOrdinal.toIsTransitive.transitive ξ hξ _ hlt

end ZFVP
