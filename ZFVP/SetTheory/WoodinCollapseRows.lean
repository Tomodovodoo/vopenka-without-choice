import ZFVP.SetTheory.CardinalSmallComplements
import ZFVP.SetTheory.WoodinCollapseDense

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def occupiedCollapseRow (κ p η : V) : V := {α ∈ κ ; ⟨α, η⟩ₖ ∈ domain p}

instance occupiedCollapseRow_definable : ℒₛₑₜ-function₃[V] occupiedCollapseRow := by
  have h : ℒₛₑₜ-relation₄[V] (fun A κ p η ↦ ∀ α, α ∈ A ↔ α ∈ κ ∧ ⟨α, η⟩ₖ ∈ domain p) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [occupiedCollapseRow]

theorem occupiedCollapseRow_small {κ δ p : V} (hp : p ∈ woodinCollapse κ δ) (η : V) :
    IsCardinalSmall κ (occupiedCollapseRow κ p η) := by
  let F : V → V := fun α ↦ ⟨α, η⟩ₖ
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let f := definableGraph (occupiedCollapseRow κ p η) F hF
  have hf : f ∈ (domain p) ^ (occupiedCollapseRow κ p η) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun α hα ↦ (mem_sep_iff.mp hα).2)
  have hinj : Injective f := by
    intro α β z hα hβ
    have ha := ((pair_mem_definableGraph_iff _ F hF α z).mp hα).2
    have hb := ((pair_mem_definableGraph_iff _ F hF β z).mp hβ).2
    exact (kpair_iff.mp (ha.symm.trans hb)).1
  exact ((mem_woodinCollapse _ _ _).mp hp).2.2.1.of_cardLE ⟨f, hf, hinj⟩

noncomputable def freeCollapseRow (κ p η : V) : V := κ \ occupiedCollapseRow κ p η

instance freeCollapseRow_definable : ℒₛₑₜ-function₃[V] freeCollapseRow := by
  unfold freeCollapseRow
  definability

theorem mem_freeCollapseRow (κ p η α : V) :
    α ∈ freeCollapseRow κ p η ↔ α ∈ κ ∧ ⟨α, η⟩ₖ ∉ domain p := by
  simp [freeCollapseRow, occupiedCollapseRow]
  tauto

noncomputable def collapseRowMap (κ p η : V) : V :=
  mostowskiMap (membershipRelation (freeCollapseRow κ p η)) (freeCollapseRow κ p η)

instance collapseRowMap_definable : ℒₛₑₜ-function₃[V] collapseRowMap := by
  unfold collapseRowMap
  definability

theorem collapseRowMap_bijection {κ δ p : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (η : V) :
    collapseRowMap κ p η ∈ κ ^ (freeCollapseRow κ p η) ∧
      Injective (collapseRowMap κ p η) ∧ range (collapseRowMap κ p η) = κ := by
  let := hκ.1.1
  have hsub : freeCollapseRow κ p η ⊆ κ := fun α hα ↦ ((mem_freeCollapseRow _ _ _ _).mp hα).1
  have hw := ordinalSubset_membership_wellOrder hsub
  have hc := mostowskiMap_isTransitiveCollapse hw.2.1 (internalWellOrder_extensional hw)
  have he := smallComplement_orderType hκ (occupiedCollapseRow_small hp η)
  change range (collapseRowMap κ p η) = κ at he
  have hf : collapseRowMap κ p η ∈ κ ^ (freeCollapseRow κ p η) := by
    have hfunc := hc.2.1
    change collapseRowMap κ p η ∈ (range (collapseRowMap κ p η)) ^ (freeCollapseRow κ p η) at hfunc
    rwa [he] at hfunc
  refine ⟨hf, ?_, he⟩
  let := IsFunction.of_mem hf
  intro α β z hα hβ
  exact hc.2.2.2.1 α ((mem_of_mem_functions hf hα).1) β ((mem_of_mem_functions hf hβ).1)
    ((value_eq_of_kpair_mem hα).trans (value_eq_of_kpair_mem hβ).symm)

noncomputable def freeCollapseCoordinates (κ δ p : V) : V := (κ ×ˢ δ) \ domain p

instance freeCollapseCoordinates_definable : ℒₛₑₜ-function₃[V] freeCollapseCoordinates := by
  unfold freeCollapseCoordinates
  definability

theorem pair_mem_freeCollapseCoordinates (κ δ p α η : V) :
    ⟨α, η⟩ₖ ∈ freeCollapseCoordinates κ δ p ↔ α ∈ freeCollapseRow κ p η ∧ η ∈ δ := by
  simp [freeCollapseCoordinates, mem_freeCollapseRow, and_assoc]
  tauto

noncomputable def collapseCoordinateValue (κ p z : V) : V :=
  ⟨(collapseRowMap κ p (kpair.π₂ z)) ‘ (kpair.π₁ z), kpair.π₂ z⟩ₖ

instance collapseCoordinateValue_definable : ℒₛₑₜ-function₃[V] collapseCoordinateValue := by
  unfold collapseCoordinateValue
  definability

noncomputable def collapseCoordinateMap (κ δ p : V) : V :=
  definableGraph (freeCollapseCoordinates κ δ p) (collapseCoordinateValue κ p) (by definability)

instance collapseCoordinateMap_definable : ℒₛₑₜ-function₃[V] collapseCoordinateMap := by
  have h : ℒₛₑₜ-relation₄[V] (fun f κ δ p ↦ ∀ z, z ∈ f ↔
      ∃ x ∈ freeCollapseCoordinates κ δ p, z = ⟨x, collapseCoordinateValue κ p x⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [collapseCoordinateMap, mem_definableGraph_iff]
  rfl

theorem collapseCoordinateMap_value {κ δ p z : V} (hz : z ∈ freeCollapseCoordinates κ δ p) :
    (collapseCoordinateMap κ δ p) ‘ z = collapseCoordinateValue κ p z := value_definableGraph _ _ _ hz

theorem collapseCoordinateMap_function {κ δ p : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) :
    collapseCoordinateMap κ δ p ∈ (κ ×ˢ δ) ^ (freeCollapseCoordinates κ δ p) := by
  apply definableGraph_mem_function_of_mapsTo
  intro z hz
  have hzd : z ∈ κ ×ˢ δ := (show z ∈ κ ×ˢ δ ∧ z ∉ domain p by simpa [freeCollapseCoordinates] using hz).1
  obtain ⟨α, _, η, _, rfl⟩ := mem_prod_iff.mp hzd
  have hr := (pair_mem_freeCollapseCoordinates _ _ _ _ _).mp hz
  simpa only [collapseCoordinateValue, kpair.π₁_kpair, kpair.π₂_kpair] using
    kpair_mem_iff.mpr ⟨function_value_mem (collapseRowMap_bijection hκ hp η).1 hr.1, hr.2⟩

theorem collapseCoordinateMap_injective {κ δ p : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) : Injective (collapseCoordinateMap κ δ p) := by
  intro z w t hz hw
  obtain ⟨hzD, htz⟩ := (pair_mem_definableGraph_iff _ _ (by definability) z t).mp hz
  obtain ⟨hwD, htw⟩ := (pair_mem_definableGraph_iff _ _ (by definability) w t).mp hw
  have hzP : z ∈ κ ×ˢ δ := (show z ∈ κ ×ˢ δ ∧ z ∉ domain p by simpa [freeCollapseCoordinates] using hzD).1
  have hwP : w ∈ κ ×ˢ δ := (show w ∈ κ ×ˢ δ ∧ w ∉ domain p by simpa [freeCollapseCoordinates] using hwD).1
  obtain ⟨α, _, η, _, rfl⟩ := mem_prod_iff.mp hzP
  obtain ⟨β, _, ξ, _, rfl⟩ := mem_prod_iff.mp hwP
  have he : (collapseRowMap κ p η) ‘ α = (collapseRowMap κ p ξ) ‘ β ∧ η = ξ := by
    simpa only [collapseCoordinateValue, kpair.π₁_kpair, kpair.π₂_kpair, kpair_iff] using htz.symm.trans htw
  obtain ⟨hval, rfl⟩ := he
  have hm := collapseRowMap_bijection hκ hp η
  have ha := ((pair_mem_freeCollapseCoordinates _ _ _ _ _).mp hzD).1
  have hb := ((pair_mem_freeCollapseCoordinates _ _ _ _ _).mp hwD).1
  exact kpair_iff.mpr ⟨injective_value_eq hm.1 hm.2.1 ha hb hval, rfl⟩

theorem collapseCoordinateMap_range {κ δ p : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) : range (collapseCoordinateMap κ δ p) = κ ×ˢ δ := by
  have hf := collapseCoordinateMap_function hκ hp
  let := IsFunction.of_mem hf
  apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
  intro z hz
  obtain ⟨α, hα, η, hη, rfl⟩ := mem_prod_iff.mp hz
  have hm := collapseRowMap_bijection hκ hp η
  let := IsFunction.of_mem hm.1
  obtain ⟨β, hβα⟩ := mem_range_iff.mp (hm.2.2.symm ▸ hα)
  have hβ := (mem_of_mem_functions hm.1 hβα).1
  have hbD := (pair_mem_freeCollapseCoordinates _ _ _ _ _).mpr ⟨hβ, hη⟩
  have hv : (collapseCoordinateMap κ δ p) ‘ ⟨β, η⟩ₖ = ⟨α, η⟩ₖ := by
    rw [collapseCoordinateMap_value hbD]
    simp only [collapseCoordinateValue, kpair.π₁_kpair, kpair.π₂_kpair, value_eq_of_kpair_mem hβα]
  exact hv ▸ value_mem_range hf hbD

theorem collapseCoordinateMap_preserves_row {κ δ p z : V} (hz : z ∈ freeCollapseCoordinates κ δ p) :
    kpair.π₂ ((collapseCoordinateMap κ δ p) ‘ z) = kpair.π₂ z := by
  rw [collapseCoordinateMap_value hz]
  simp [collapseCoordinateValue]

end ZFVP
