import ZFVP.SetTheory.OrdinalClosureSequence
import ZFVP.SetTheory.RegularSmallRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem increasingSequence_limit_stages {κ δ f : V} (hκ : IsRegularCardinal κ) [IsOrdinal δ]
    (hf : f ∈ δ ^ κ) (hinc : ∀ i ∈ κ, ∀ j ∈ i, f ‘ j ∈ f ‘ i) :
    IsOrdinal (⋃ˢ range f) ∧ (∀ i ∈ κ, f ‘ i ∈ ⋃ˢ range f) ∧
      ∀ y ∈ ⋃ˢ range f, ∃ i ∈ κ, y ∈ f ‘ i := by
  let := hκ.1.1
  let := IsFunction.of_mem hf
  have ho : IsOrdinal (⋃ˢ range f) := IsOrdinal.sUnion
    (fun y hy ↦ IsOrdinal.of_mem (range_subset_of_mem_function hf y hy))
  refine ⟨ho, ?_, ?_⟩
  · intro i hi
    have hs := regularCardinal_succ_closed hκ hi
    exact mem_sUnion_iff.mpr ⟨f ‘ (succ i), mem_range_of_kpair_mem
      (kpair_value_mem (by rw [domain_eq_of_mem_function hf]; exact hs)), hinc _ hs i (mem_succ_self i)⟩
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_sUnion_iff.mp hy
    obtain ⟨i, hiz⟩ := mem_range_iff.mp hz
    exact ⟨i, domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hiz,
      (value_eq_of_kpair_mem hiz).symm ▸ hyz⟩

theorem increasingSequence_limit_maps_bounded {κ δ f γ g : V} (hκ : IsRegularCardinal κ) [IsOrdinal δ]
    (hf : f ∈ δ ^ κ) (hinc : ∀ i ∈ κ, ∀ j ∈ i, f ‘ j ∈ f ‘ i)
    (hγ : γ ∈ κ) (hg : g ∈ (⋃ˢ range f) ^ γ) :
    ∃ β ∈ ⋃ˢ range f, ∀ i ∈ γ, g ‘ i ∈ β := by
  let := hκ.1.1
  have hs := increasingSequence_limit_stages hκ hf hinc
  let := hs.1
  let := IsFunction.of_mem hf
  let F := fun i ↦ ordinalCoverIndex κ f (g ‘ i)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hi (i : V) (hi : i ∈ γ) := ordinalCoverIndex_spec (domain_eq_of_mem_function hf) (function_value_mem hg hi)
  have hI : definableGraph γ F hF ∈ κ ^ γ :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i h ↦ (hi i h).1)
  obtain ⟨j, hj, hb⟩ := regularCardinal_maps_bounded hκ hγ hI
  refine ⟨f ‘ j, hs.2.1 j hj, ?_⟩
  intro i hiγ
  have hij : ordinalCoverIndex κ f (g ‘ i) ∈ j := by
    simpa only [value_definableGraph _ _ _ hiγ, F] using hb i hiγ
  let := IsOrdinal.of_mem (function_value_mem hf hj)
  exact IsOrdinal.toIsTransitive.mem_trans (hi i hiγ).2 (hinc j hj _ hij)

theorem increasingSequence_limit_successor_closed {κ δ f : V} (hκ : IsRegularCardinal κ) [IsOrdinal δ]
    (hf : f ∈ δ ^ κ) (hinc : ∀ i ∈ κ, ∀ j ∈ i, f ‘ j ∈ f ‘ i) :
    ∀ y ∈ ⋃ˢ range f, succ y ∈ ⋃ˢ range f := by
  have hs := increasingSequence_limit_stages hκ hf hinc
  let := hs.1
  intro y hy
  obtain ⟨i, hi, hyi⟩ := hs.2.2 y hy
  let := IsOrdinal.of_mem hy
  let := IsOrdinal.of_mem (function_value_mem hf hi)
  apply ordinal_mem_of_subset_mem ?_ (hs.2.1 i hi)
  intro z hz
  rcases mem_succ_iff.mp hz with rfl | hzy
  · exact hyi
  · exact IsOrdinal.toIsTransitive.mem_trans hzy hyi

end ZFVP
