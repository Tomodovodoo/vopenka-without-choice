import ZFVP.SetTheory.WeaklyLSHullFamily
import ZFVP.SetTheory.SmallCollapseUnionSurjection
import ZFVP.SetTheory.Cofinality
import ZFVP.ModelTheory.ElementaryDirectedFamily
import ZFVP.ModelTheory.DirectedElementaryAmbientUnion

/-! The elementary-hull and surjection clauses of Usuba Lemma 3.1.
These are the clauses used to prove DC after collapsing the singular weakly
LS cardinal. The successor-cardinal intersection clause is separate. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWeaklyLSCardinal.singular_hull {κ α x : V}
    (hκ : IsWeaklyLSCardinal κ) (hsing : internalCofinality κ ∈ κ)
    [IsOrdinal α] (hκα : κ ⊆ α) (hx : x ∈ hierarchy α) :
    ∃ X, IsElementaryInclusion X (hierarchy α) ∧ hierarchy κ ⊆ X ∧ x ∈ X ∧
      ∃ e ∈ X ^ (hierarchy κ), range e = X := by
  let := hκ.1.1
  obtain ⟨c, hc⟩ := cofinalMap_exists κ
  let := IsFunction.of_mem hc.1
  let F := weaklyLSHullFamily κ α x
  let r := definableGraph κ hierarchy (by definability)
  have hr := definableGraph_mem_function κ hierarchy (by definability)
  let := IsFunction.of_mem hr
  let p := ⟨⟨F, c⟩ₖ, ⟨r, x⟩ₖ⟩ₖ
  let β := rank ({p, κ} : V)
  let := hierarchy_transitive β
  have hpβ : p ∈ hierarchy β := (mem_hierarchy_iff_rank_mem _ _).mpr
    (rank_mem (show p ∈ ({p, κ} : V) by simp))
  have hκβ : κ ∈ β := by
    simpa only [rank_of_ordinal] using rank_mem (show κ ∈ ({p, κ} : V) by simp)
  obtain ⟨Y, hY, hcfY, hpY, hsmallY⟩ := hκ.2.2 (internalCofinality κ) hsing β
    inferInstance (IsOrdinal.toIsTransitive.transitive _ hκβ) p hpβ
  have hparts := hY.kpair_components_mem hpY
  have hFc := hY.kpair_components_mem hparts.1
  have hrx := hY.kpair_components_mem hparts.2
  have hFne : IsNonempty F := hκ.hullFamily_nonempty hκα hx
  have hIne : IsNonempty (F ∩ Y) := hY.nonempty_inter_member hFc.1 hFne
  have hdir := hY.inter_directed_family hFc.1 (hκ.hullFamily_directed hκα hx)
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
    have hciY := hY.function_value_mem hFc.2 hiY
      (domain_eq_of_mem_function hc.1 |>.symm ▸ hi)
    have hrciY := hY.function_value_mem hrx.1 hciY
      (domain_eq_of_mem_function hr |>.symm ▸ hciκ)
    have hrval : r ‘ (c ‘ i) = hierarchy (c ‘ i) := value_definableGraph _ _ _ hciκ
    have hVciY : hierarchy (c ‘ i) ∈ Y := hrval ▸ hrciY
    obtain ⟨Z, hZ, hVZ⟩ := hY.containing_member hFc.1 hVciY
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
  exact ⟨X, he, hκX, hxX, e, heX, hre⟩

end ZFVP
