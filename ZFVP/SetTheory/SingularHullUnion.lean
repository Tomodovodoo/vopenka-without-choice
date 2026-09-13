import ZFVP.SetTheory.WeaklyLSHullFamily
import ZFVP.SetTheory.SmallCollapseUnionSurjection
import ZFVP.SetTheory.Cofinality
import ZFVP.ModelTheory.ElementaryDirectedFamily
import ZFVP.ModelTheory.DirectedElementaryAmbientUnion

/-! Union of the small weakly LS hulls contained in an elementary submodel. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWeaklyLSCardinal.singular_hull_union {κ α β x c Y : V}
    (hκ : IsWeaklyLSCardinal κ) [IsOrdinal α] [IsOrdinal β]
    (hκα : κ ⊆ α) (hx : x ∈ hierarchy α)
    (hc : IsCofinalMap κ (internalCofinality κ) c)
    (hY : IsElementaryInclusion Y (hierarchy β))
    (hFY : weaklyLSHullFamily κ α x ∈ Y) (hcY : c ∈ Y)
    (hrY : definableGraph κ hierarchy (by definability) ∈ Y)
    (hcfY : hierarchy (internalCofinality κ) ⊆ Y)
    (hsmallY : HasSmallTransitiveCollapse κ Y) :
    IsElementaryInclusion (⋃ˢ (weaklyLSHullFamily κ α x ∩ Y)) (hierarchy α) ∧
      hierarchy κ ⊆ ⋃ˢ (weaklyLSHullFamily κ α x ∩ Y) ∧
      x ∈ ⋃ˢ (weaklyLSHullFamily κ α x ∩ Y) ∧
      ∃ e ∈ (⋃ˢ (weaklyLSHullFamily κ α x ∩ Y)) ^ (hierarchy κ),
        range e = ⋃ˢ (weaklyLSHullFamily κ α x ∩ Y) := by
  let := hκ.1.1
  let := hierarchy_transitive β
  let := IsFunction.of_mem hc.1
  let F := weaklyLSHullFamily κ α x
  let r := definableGraph κ hierarchy (by definability)
  have hr := definableGraph_mem_function κ hierarchy (by definability)
  let := IsFunction.of_mem hr
  have hFne : IsNonempty F := hκ.hullFamily_nonempty hκα hx
  have hIne : IsNonempty (F ∩ Y) := hY.nonempty_inter_member hFY hFne
  have hdir := hY.inter_directed_family hFY (hκ.hullFamily_directed hκα hx)
  let X := ⋃ˢ (F ∩ Y)
  have he : IsElementaryInclusion X (hierarchy α) := by
    apply directedUnion_elementary_ambient (fun Z : V ↦ Z) (by definability) hIne
    · intro Z hZ
      exact ((mem_weaklyLSHullFamily _ _ _ _).mp (mem_inter_iff.mp hZ).1).1
    · exact hdir
    · intro z
      exact mem_sUnion_iff
  have hsucc (δ : V) (hδ : δ ∈ κ) : succ δ ∈ κ :=
    initial_succ_mem hκ.1 (IsOrdinal.toIsTransitive.transitive _ hκ.2.1) hδ
  have hcover : ∀ δ ∈ κ, ∃ Z ∈ F ∩ Y, hierarchy δ ⊆ Z := by
    intro δ hδ
    let := IsOrdinal.of_mem hδ
    obtain ⟨i, hi, hbound⟩ := hc.2 (succ δ) (hsucc δ hδ)
    have hciκ := function_value_mem hc.1 hi
    let := IsOrdinal.of_mem hciκ
    have hiY := hcfY i (ordinal_subset_hierarchy (internalCofinality κ) i hi)
    have hciY := hY.function_value_mem hcY hiY
      (domain_eq_of_mem_function hc.1 |>.symm ▸ hi)
    have hrciY := hY.function_value_mem hrY hciY
      (domain_eq_of_mem_function hr |>.symm ▸ hciκ)
    have hrval : r ‘ (c ‘ i) = hierarchy (c ‘ i) := value_definableGraph _ _ _ hciκ
    have hVciY : hierarchy (c ‘ i) ∈ Y := hrval ▸ hrciY
    obtain ⟨Z, hZ, hVZ⟩ := hY.containing_member hFY hVciY
      (hκ.hullFamily_covers hκα hx hciκ)
    exact ⟨Z, hZ, subset_trans (hierarchy_mono
      (subset_trans (show δ ⊆ succ δ from fun z hz ↦ mem_succ_iff.mpr (Or.inr hz)) hbound)) hVZ⟩
  have hκX : hierarchy κ ⊆ X := by
    intro z hz
    have hzκ : rank z ∈ κ := (mem_hierarchy_iff_rank_mem _ _).mp hz
    obtain ⟨Z, hZ, hVZ⟩ := hcover (succ (rank z)) (hsucc _ hzκ)
    exact mem_sUnion_iff.mpr ⟨Z, hZ, hVZ z ((mem_hierarchy_iff_rank_mem _ _).mpr (by simp))⟩
  have hxall : ∀ Z ∈ F ∩ Y, x ∈ Z := by
    intro Z hZ
    exact ((mem_weaklyLSHullFamily _ _ _ _).mp (mem_inter_iff.mp hZ).1).2.1
  have hxX : x ∈ X := by
    obtain ⟨Z, hZ⟩ := hIne.nonempty
    exact mem_sUnion_iff.mpr ⟨Z, hZ, hxall Z hZ⟩
  obtain ⟨e, heX, hre⟩ := smallCollapse_union_surjection hsucc hsmallY hIne
    (fun Z hZ ↦ ((mem_weaklyLSHullFamily _ _ _ _).mp (mem_inter_iff.mp hZ).1).2.2) hxall
  exact ⟨he, hκX, hxX, e, heX, hre⟩

end ZFVP
