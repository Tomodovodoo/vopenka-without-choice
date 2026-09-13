import ZFVP.SetTheory.Cofinality
import ZFVP.SetTheory.WitnessClosure
import ZFVP.SetTheory.CodingUniverse

/-! No cofinal maps from low-rank sets gives Collection within the rank segment. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def NoLowRankCofinalMaps (θ : V) : Prop :=
  ∀ a ∈ hierarchy θ, ∀ f, ¬IsCofinalMap θ a f

instance noLowRankCofinalMaps_definable : ℒₛₑₜ-predicate[V] NoLowRankCofinalMaps := by
  unfold NoLowRankCofinalMaps
  definability

theorem NoLowRankCofinalMaps.map_bounded {θ a f : V} [IsOrdinal θ]
    (hθ : NoLowRankCofinalMaps θ) (ha : a ∈ hierarchy θ) (hf : f ∈ θ ^ a) :
    ∃ β ∈ θ, ∀ x ∈ a, f ‘ x ∈ β := by
  classical
  have hn : ¬∀ β ∈ θ, ∃ x ∈ a, β ⊆ f ‘ x := fun hb ↦ hθ a ha f ⟨hf, hb⟩
  push Not at hn
  obtain ⟨β, hβ, hb⟩ := hn
  let := IsOrdinal.of_mem hβ
  refine ⟨β, hβ, ?_⟩
  intro x hx
  let := IsOrdinal.of_mem (function_value_mem hf hx)
  rcases IsOrdinal.mem_trichotomy (f ‘ x) β with hl | he | hg
  · exact hl
  · exact False.elim (hb x hx (he.symm ▸ subset_refl β))
  · exact False.elim (hb x hx (IsOrdinal.toIsTransitive.transitive β hg))

theorem NoLowRankCofinalMaps.definable_map_bounded {θ a : V} [IsOrdinal θ]
    (hθ : NoLowRankCofinalMaps θ) (ha : a ∈ hierarchy θ)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hf : ∀ x ∈ a, F x ∈ θ) :
    ∃ β ∈ θ, ∀ x ∈ a, F x ∈ β := by
  have hg : definableGraph a F hF ∈ θ ^ a := definableGraph_mem_function_of_mapsTo _ _ _ _ hf
  obtain ⟨β, hβ, hb⟩ := hθ.map_bounded ha hg
  exact ⟨β, hβ, fun x hx ↦ by simpa [value_definableGraph _ _ _ hx] using hb x hx⟩

theorem NoLowRankCofinalMaps.range_mem {θ a f : V} [IsOrdinal θ]
    (hθ : NoLowRankCofinalMaps θ) (hs : ∀ β ∈ θ, succ β ∈ θ)
    (ha : a ∈ hierarchy θ) (hf : f ∈ (hierarchy θ) ^ a) : range f ∈ hierarchy θ := by
  obtain ⟨β, hβ, hb⟩ := hθ.definable_map_bounded ha (fun x ↦ rank (f ‘ x)) (by definability)
    (fun x hx ↦ (mem_hierarchy_iff_rank_mem _ _).mp (function_value_mem hf hx))
  let := IsOrdinal.of_mem hβ
  have hr : range f ⊆ hierarchy β := by
    intro y hy
    obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
    let := IsFunction.of_mem hf
    have hx := (mem_of_mem_functions hf hxy).1
    rw [mem_hierarchy_iff_rank_mem, ← value_eq_of_kpair_mem hxy]
    exact hb x hx
  exact subset_mem_hierarchy_limit hs (hierarchy_mem hβ) hr

theorem NoLowRankCofinalMaps.collection {θ a : V} [IsOrdinal θ]
    (hθ : NoLowRankCofinalMaps θ) (hs : ∀ β ∈ θ, succ β ∈ θ)
    (ha : a ∈ hierarchy θ) (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (hex : ∀ x ∈ a, ∃ y ∈ hierarchy θ, R x y) :
    ∃ b ∈ hierarchy θ, ∀ x ∈ a, ∃ y ∈ b, R x y := by
  let S := fun x y ↦ y ∈ hierarchy θ ∧ R x y
  have hS : ℒₛₑₜ-relation S := by unfold S; definability
  let F := leastWitnessStageOrZero S hS
  have hF : ℒₛₑₜ-function₁ F := leastWitnessStageOrZero_definable S hS
  have hw (x : V) (hx : x ∈ a) : IsLeastWitnessStage S x (F x) :=
    leastWitnessStageOrZero_spec S hS x (hex x hx)
  have hbound : ∀ x ∈ a, F x ∈ θ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hex x hx
    have hr := (mem_hierarchy_iff_rank_mem y θ).mp hy
    let := (hw x hx).1
    have hmin : F x ⊆ succ (rank y) :=
      (hw x hx).2.2 _ inferInstance ⟨y, by
        rw [hierarchy_succ, mem_power_iff]
        exact subset_hierarchy_rank y, hy, hxy⟩
    rcases IsOrdinal.subset_iff.mp hmin with he | hl
    · exact he.symm ▸ hs _ hr
    · exact IsOrdinal.toIsTransitive.mem_trans hl (hs _ hr)
  obtain ⟨β, hβ, hb⟩ := hθ.definable_map_bounded ha F hF hbound
  refine ⟨hierarchy β, hierarchy_mem hβ, ?_⟩
  intro x hx
  obtain ⟨y, hy, _, hxy⟩ := (hw x hx).2.1
  let := IsOrdinal.of_mem hβ
  let := (hw x hx).1
  exact ⟨y, hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ (hb x hx)) y hy, hxy⟩

theorem NoLowRankCofinalMaps.replacement {θ a : V} [IsOrdinal θ]
    (hθ : NoLowRankCofinalMaps θ) (hs : ∀ β ∈ θ, succ β ∈ θ)
    (ha : a ∈ hierarchy θ) (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (hex : ∀ x ∈ a, ∃! y, y ∈ hierarchy θ ∧ R x y) :
    ∃ b ∈ hierarchy θ, ∀ y ∈ hierarchy θ, (y ∈ b ↔ ∃ x ∈ a, R x y) := by
  obtain ⟨c, hc, hw⟩ := hθ.collection hs ha R hR (fun x hx ↦ (hex x hx).exists)
  let b := {y ∈ c ; ∃ x ∈ a, R x y}
  have hb : b ⊆ c := sep_subset
  refine ⟨b, subset_mem_hierarchy_limit hs hc hb, ?_⟩
  intro y hy
  constructor
  · intro hyb
    exact (mem_sep_iff.mp hyb).2
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨z, hz, hxz⟩ := hw x hx
    have hzy : z = y := (hex x hx).unique ⟨(hierarchy_transitive θ).mem_trans hz hc, hxz⟩ ⟨hy, hxy⟩
    exact mem_sep_iff.mpr ⟨hzy ▸ hz, x, hx, hxy⟩

end ZFVP
