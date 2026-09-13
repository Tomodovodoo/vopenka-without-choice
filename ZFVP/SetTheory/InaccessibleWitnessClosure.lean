import ZFVP.SetTheory.InaccessibleWitnessStep
import ZFVP.SetTheory.RegularSequenceLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def BoundsShortOrdinalMaps (κ β : V) : Prop :=
  ∀ γ ∈ κ, ∀ g ∈ β ^ γ, ∃ ξ ∈ β, ∀ i ∈ γ, g ‘ i ∈ ξ

instance boundsShortOrdinalMaps_definable : ℒₛₑₜ-relation[V] BoundsShortOrdinalMaps := by
  unfold BoundsShortOrdinalMaps
  definability

theorem IsChoicelessInaccessible.witnessClosed_above_regular {δ κ a : V}
    (hδ : IsChoicelessInaccessible δ) (hκ : IsRegularCardinal κ) (hκδ : κ ∈ δ) (ha : a ∈ δ)
    (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (hex : ∀ x ∈ hierarchy δ, (∃ y, R x y) → ∃ y ∈ hierarchy δ, R x y) :
    ∃ β ∈ δ, IsOrdinal β ∧ a ∈ β ∧ κ ∈ β ∧ (∀ ξ ∈ β, succ ξ ∈ β) ∧
      BoundsShortOrdinalMaps κ β ∧ IsWitnessClosed R β := by
  let := hδ.1
  let := hκ.1.1
  let := IsOrdinal.of_mem ha
  let start := a ∪ κ
  have hstart : start ∈ δ := ordinal_union_mem ha hκδ
  let := IsOrdinal.of_mem hstart
  let F := witnessBoundingStep R hR
  have hF : ℒₛₑₜ-function₁ F := witnessBoundingStep_definable R hR
  have hstep : ∀ x ∈ δ, F x ∈ δ ∧ x ∈ F x := by
    intro x hx
    let := IsOrdinal.of_mem hx
    exact ⟨witnessBoundingStep_mem_inaccessible hδ R hR hx
      (fun y hy ↦ hex y (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hx) y hy)),
      witnessBoundingStep_gt R hR x⟩
  let seq := ordinalClosureSequence F hF start
  let f := definableGraph κ seq (by unfold seq; definability)
  have hf : f ∈ δ ^ κ := definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦
    ordinalClosureSequence_mem hδ.regular F hF hstart (fun x hx ↦ (hstep x hx).1)
      (IsOrdinal.toIsTransitive.mem_trans hi hκδ))
  have hv (i : V) (hi : i ∈ κ) : f ‘ i = seq i := value_definableGraph _ _ _ hi
  have hinc : ∀ i ∈ κ, ∀ j ∈ i, f ‘ j ∈ f ‘ i := by
    intro i hi j hj
    rw [hv i hi, hv j (IsOrdinal.toIsTransitive.mem_trans hj hi)]
    exact ordinalClosureSequence_increasing hδ.regular F hF hstart hstep
      (IsOrdinal.toIsTransitive.mem_trans hi hκδ) hj
  let β := ⋃ˢ range f
  have hβ : β ∈ δ := union_range_below_cofinality (hδ.regular.2.2.symm ▸ hκδ) hf
  have hs := increasingSequence_limit_stages hκ hf hinc
  let := hs.1
  have h0 : (0 : V) ∈ κ := hκ.2.1 0 (by simp)
  have hseq0 : seq 0 = F start := by
    change ordinalClosureSequence F hF start 0 = F start
    rw [ordinalClosureSequence_eq]
    have hr : repl (ordinalClosureSequence F hF start) (by definability) (0 : V) = ∅ := by
      apply mem_ext
      intro z
      rw [repl_spec]
      simp [zero_def]
    rw [hr]
    simp
  have hstartβ : start ∈ β := IsOrdinal.toIsTransitive.mem_trans
    ((hseq0.symm ▸ (hstep start hstart).2) : start ∈ seq 0) (hv 0 h0 ▸ hs.2.1 0 h0)
  refine ⟨β, hβ, hs.1, ordinal_mem_of_subset_mem (subset_union_left _ _) hstartβ,
    ordinal_mem_of_subset_mem (subset_union_right _ _) hstartβ,
    increasingSequence_limit_successor_closed hκ hf hinc,
    fun γ hγ g hg ↦ increasingSequence_limit_maps_bounded hκ hf hinc hγ hg, ?_⟩
  intro x hx hxy
  obtain ⟨i, hi, hri⟩ := hs.2.2 (rank x) ((mem_hierarchy_iff_rank_mem x β).mp hx)
  have hj := regularCardinal_succ_closed hκ hi
  let j := succ i
  have hjδ := IsOrdinal.toIsTransitive.mem_trans hj hκδ
  let := IsOrdinal.of_mem hjδ
  let b := start ∪ ⋃ˢ repl seq (by unfold seq; definability) j
  have hg : definableGraph j seq (by unfold seq; definability) ∈ δ ^ j :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun k hk ↦
      ordinalClosureSequence_mem hδ.regular F hF hstart (fun x hx ↦ (hstep x hx).1)
        (IsOrdinal.toIsTransitive.mem_trans hk hjδ))
  have hub := union_range_below_cofinality (hδ.regular.2.2.symm ▸ hjδ) hg
  rw [range_definableGraph] at hub
  have hb : b ∈ δ := ordinal_union_mem hstart hub
  let := IsOrdinal.of_mem hb
  let := IsOrdinal.of_mem (function_value_mem hf hi)
  have hisub : f ‘ i ⊆ b := by
    rw [hv i hi]
    exact subset_trans (subset_sUnion_of_mem ((repl_spec (ordinalClosureSequence_definable F hF start)).mpr
      ⟨i, mem_succ_self i, rfl⟩)) (subset_union_right _ _)
  have hxB : x ∈ hierarchy b := hierarchy_mono hisub x ((mem_hierarchy_iff_rank_mem _ _).mpr hri)
  obtain ⟨y, hy, hxy⟩ := witnessBoundingStep_spec R hR b hxB hxy
  have hbj : F b = f ‘ j := (ordinalClosureSequence_eq F hF start j).symm.trans (hv j hj).symm
  let := IsOrdinal.of_mem (function_value_mem hf hj)
  rw [show witnessBoundingStep R hR b = f ‘ j from hbj] at hy
  exact ⟨y, hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ (hs.2.1 j hj)) y hy, hxy⟩

end ZFVP
