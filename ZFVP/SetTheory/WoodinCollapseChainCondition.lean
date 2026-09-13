import ZFVP.SetTheory.InaccessibleHartogs
import ZFVP.SetTheory.CardinalSmallComplements
import ZFVP.SetTheory.Hessenberg
import ZFVP.SetTheory.WoodinCollapseRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def ordinalRankSlice (θ f β : V) : V :=
  {i ∈ θ ; f ‘ i ∈ hierarchy β}

instance ordinalRankSlice_definable : ℒₛₑₜ-function₃[V] ordinalRankSlice := by
  have h : ℒₛₑₜ-relation₄[V] (fun D θ f β ↦ ∀ i, i ∈ D ↔ i ∈ θ ∧ f ‘ i ∈ hierarchy β) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [ordinalRankSlice]

theorem ordinalRankSlice_cardLE {θ f β B : V} (hf : f ∈ B ^ θ) (hinj : Injective f) :
    ordinalRankSlice θ f β ≤# hierarchy β := by
  have hF : ℒₛₑₜ-function₁ (fun i ↦ f ‘ i) := by definability
  refine ⟨definableGraph (ordinalRankSlice θ f β) (fun i ↦ f ‘ i) hF,
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦ (mem_sep_iff.mp hi).2), ?_⟩
  intro x y z hx hy
  obtain ⟨hx, hzx⟩ := (pair_mem_definableGraph_iff _ _ hF x z).mp hx
  obtain ⟨hy, hzy⟩ := (pair_mem_definableGraph_iff _ _ hF y z).mp hy
  exact injective_value_eq hf hinj (mem_sep_iff.mp hx).1 (mem_sep_iff.mp hy).1 (hzx.symm.trans hzy)

theorem ordinalRankSlice_collapse {δ θ f β : V} [IsOrdinal θ]
    (hδ : IsChoicelessInaccessible δ) (hβ : β ∈ δ)
    (hf : f ∈ (hierarchy δ) ^ θ) (hinj : Injective f) :
    mostowskiMap (membershipRelation (ordinalRankSlice θ f β)) (ordinalRankSlice θ f β)
      ∈ δ ^ (ordinalRankSlice θ f β) ∧
    Injective (mostowskiMap (membershipRelation (ordinalRankSlice θ f β)) (ordinalRankSlice θ f β)) := by
  let := hδ.1
  let := IsOrdinal.of_mem hβ
  have hw := ordinalSubset_membership_wellOrder (show ordinalRankSlice θ f β ⊆ θ from sep_subset)
  let := internalOrderType_ordinal hw
  have hot : internalOrderType (membershipRelation (ordinalRankSlice θ f β)) (ordinalRankSlice θ f β) ∈ δ :=
    IsOrdinal.toIsTransitive.mem_trans
      (ordinal_cardLE_iff_mem_hartogsNumber.mp ((orderType_cardLE hw).trans (ordinalRankSlice_cardLE hf hinj)))
      (hδ.hartogsNumber_mem (hierarchy_mem hβ))
  have hc := mostowskiMap_isTransitiveCollapse hw.2.1 (internalWellOrder_extensional hw)
  have hm := hc.2.1
  change mostowskiMap _ _ ∈ (internalOrderType _ _) ^ _ at hm
  refine ⟨mem_function_of_mem_function_of_subset hm (IsOrdinal.toIsTransitive.transitive _ hot), ?_⟩
  have : IsFunction (mostowskiMap (membershipRelation (ordinalRankSlice θ f β)) (ordinalRankSlice θ f β)) := IsFunction.of_mem hm
  intro x y z hx hy
  have hxD := domain_eq_of_mem_function hm ▸ mem_domain_of_kpair_mem hx
  have hyD := domain_eq_of_mem_function hm ▸ mem_domain_of_kpair_mem hy
  exact hc.2.2.2.1 x hxD y hyD ((value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm)

/-- Every ordinal that injects into an inaccessible rank injects into its height.
The rank slices are enumerated by their inherited ordinal order, so no family
of arbitrary choices is used. -/
theorem IsChoicelessInaccessible.ordinal_cardLE_of_hierarchy {δ θ : V} [IsOrdinal θ]
    (hδ : IsChoicelessInaccessible δ) (hθ : θ ≤# hierarchy δ) : θ ≤# δ := by
  let := hδ.1
  obtain ⟨f, hf, hinj⟩ := hθ
  let β : V → V := fun i ↦ succ (rank (f ‘ i))
  let F : V → V := fun i ↦ ⟨β i,
    (mostowskiMap (membershipRelation (ordinalRankSlice θ f (β i))) (ordinalRankSlice θ f (β i))) ‘ i⟩ₖ
  have hF : ℒₛₑₜ-function₁ F := by unfold F β; definability
  have hb : ∀ i ∈ θ, β i ∈ δ := fun i hi ↦
    regularCardinal_succ_closed hδ.regular ((mem_hierarchy_iff_rank_mem _ _).mp (function_value_mem hf hi))
  have hiD : ∀ i ∈ θ, i ∈ ordinalRankSlice θ f (β i) := by
    intro i hi
    exact mem_sep_iff.mpr ⟨hi, (mem_hierarchy_iff_rank_mem _ _).mpr (mem_succ_self _)⟩
  have hmap := fun i hi ↦ ordinalRankSlice_collapse hδ (hb i hi) hf hinj
  have hgraph : definableGraph θ F hF ∈ (δ ×ˢ δ) ^ θ :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦
      kpair_mem_iff.mpr ⟨hb i hi, function_value_mem (hmap i hi).1 (hiD i hi)⟩)
  apply CardLE.trans (Y := δ ×ˢ δ) ?_ (initial_prod_cardEQ hδ.regular.1 hδ.regular.2.1).1
  refine ⟨_, hgraph, ?_⟩
  intro x y z hx hy
  obtain ⟨hx, hzx⟩ := (pair_mem_definableGraph_iff _ _ hF x z).mp hx
  obtain ⟨hy, hzy⟩ := (pair_mem_definableGraph_iff _ _ hF y z).mp hy
  have hp := kpair_iff.mp (hzx.symm.trans hzy)
  have hxyD : y ∈ ordinalRankSlice θ f (β x) := hp.1.symm ▸ hiD y hy
  have he := hp.2
  rw [← hp.1] at he
  exact injective_value_eq (hmap x hx).1 (hmap x hx).2 (hiD x hx) hxyD he

/-- The ordinal-indexed successor chain bound is stronger than an antichain
bound: there is no successor-length injection into the entire carrier. -/
theorem woodinCollapse_no_successor_injection {δ κ : V}
    (hδ : IsChoicelessInaccessible δ) (hκδ : κ ⊆ δ) :
    ¬hartogsNumber δ ≤# woodinCollapse κ δ := by
  intro hi
  have hsub : woodinCollapse κ δ ⊆ hierarchy δ := fun p hp ↦
    woodinCollapse_condition_mem_hierarchy hδ.regular hκδ hp
  exact not_hartogsNumber_cardLE δ
    (hδ.ordinal_cardLE_of_hierarchy (hi.trans (cardLE_of_subset hsub)))

end ZFVP
