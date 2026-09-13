import ZFVP.SetTheory.WoodinCollapseDense
import ZFVP.ModelTheory.ForcingQuotientGeneric
import ZFVP.ModelTheory.ForcingModelChecks
import ZFVP.SetTheory.EndExtensionWellOrdering
import ZFVP.SetTheory.RegularOrdinalAddition

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinCollapseContext {κ : V} (hκ : IsRegularCardinal κ) (δ : V) (G : Set V)
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    ForcingContext V :=
  ⟨woodinCollapse κ δ, woodinCollapseOrder κ δ, ∅, G, (woodinCollapse_poset κ δ).1,
    woodinCollapse_top (hκ.2.1 ∅ (by simp)) δ, hG⟩

namespace WoodinCollapseModel

variable {κ δ : V} (hκ : IsRegularCardinal κ) {G : Set V}
  (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)

noncomputable def genericSet : (woodinCollapseContext hκ δ G hG).Model :=
  forcingGenericSet _ _ G (woodinCollapse_poset κ δ).1 hG.1 ∅
    (woodinCollapse_top (hκ.2.1 ∅ (by simp)) δ)

theorem mem_genericSet (x : (woodinCollapseContext hκ δ G hG).Model) :
    x ∈ genericSet hκ hG ↔ ∃ p ∈ G, x = (woodinCollapseContext hκ δ G hG).check p :=
  forcingGenericSet_mem_iff _ _ G (woodinCollapse_poset κ δ).1 hG ∅
    (woodinCollapse_top (hκ.2.1 ∅ (by simp)) δ) x

noncomputable def genericFunction : (woodinCollapseContext hκ δ G hG).Model := ⋃ˢ genericSet hκ hG

theorem mem_genericFunction (x : (woodinCollapseContext hκ δ G hG).Model) :
    x ∈ genericFunction hκ hG ↔ ∃ p ∈ G, x ∈ (woodinCollapseContext hκ δ G hG).check p := by
  simp only [genericFunction, mem_sUnion_iff, mem_genericSet]
  constructor
  · rintro ⟨y, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨_, ⟨p, hp, rfl⟩, hx⟩

instance genericFunction_isFunction : IsFunction (genericFunction hκ hG) := by
  let S := woodinCollapseContext hκ δ G hG
  have hfun (p : V) (hp : p ∈ G) : IsFunction (S.check p) := by
    have : IsFunction p := ((mem_woodinCollapse κ δ p).mp (hG.1.1 p hp)).2.1
    exact S.check_isFunction p
  apply isFunction_sUnion
  · intro f hf
    obtain ⟨p, hp, rfl⟩ := (mem_genericSet hκ hG f).mp hf
    exact hfun p hp
  · intro f hf g hg x y z hxy hxz
    obtain ⟨p, hp, rfl⟩ := (mem_genericSet hκ hG f).mp hf
    obtain ⟨q, hq, rfl⟩ := (mem_genericSet hκ hG g).mp hg
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hp q hq
    have hpr : p ⊆ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2
    have hqr : q ⊆ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2
    have : IsFunction (S.check r) := hfun r hr
    exact IsFunction.unique (f := S.check r) ((S.checkEmbedding.subset_iff p r).mpr hpr _ hxy)
      ((S.checkEmbedding.subset_iff q r).mpr hqr _ hxz)

theorem genericFunction_mem_function [IsOrdinal δ] :
    genericFunction hκ hG ∈ (woodinCollapseContext hκ δ G hG).check (hierarchy δ) ^
      (woodinCollapseContext hκ δ G hG).check (κ ×ˢ δ) := by
  let S := woodinCollapseContext hκ δ G hG
  apply mem_function.intro
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := (mem_genericFunction hκ hG z).mp hz
    have hpsub := ((mem_woodinCollapse κ δ p).mp (hG.1.1 p hp)).1
    have hh := (S.checkEmbedding.subset_iff p ((κ ×ˢ δ) ×ˢ hierarchy δ)).mpr hpsub z hzp
    change z ∈ S.check ((κ ×ˢ δ) ×ˢ hierarchy δ) at hh
    rwa [show S.check ((κ ×ˢ δ) ×ˢ hierarchy δ) = S.check (κ ×ˢ δ) ×ˢ S.check (hierarchy δ) from
      S.checkEmbedding.map_prod (κ ×ˢ δ) (hierarchy δ)] at hh
  · intro z hz
    obtain ⟨c, hc, rfl⟩ := (S.mem_check_iff (κ ×ˢ δ) z).mp hz
    obtain ⟨α, hα, η, hη, rfl⟩ := mem_prod_iff.mp hc
    obtain ⟨p, hpG, hp⟩ := hG.2 _ (woodinCollapse_coordinate_dense hκ hα hη)
    obtain ⟨x, hx⟩ := mem_domain_iff.mp (mem_sep_iff.mp hp).2
    have hpair : ⟨S.check ⟨α, η⟩ₖ, S.check x⟩ₖ ∈ genericFunction hκ hG := by
      apply (mem_genericFunction hκ hG _).mpr
      refine ⟨p, hpG, ?_⟩
      rw [← S.check_kpair, S.check_mem_iff]
      exact hx
    exact ⟨S.check x, hpair, fun _ h ↦ IsFunction.unique h hpair⟩

theorem genericFunction_row_value {α η : V} (hα : α ∈ κ) (hη : η ∈ δ) [IsOrdinal δ] :
    (genericFunction hκ hG) ‘ ((woodinCollapseContext hκ δ G hG).check ⟨α, η⟩ₖ) ∈
      (woodinCollapseContext hκ δ G hG).check (hierarchy (ordinalAdd (1 : V) η)) := by
  let S := woodinCollapseContext hκ δ G hG
  have hdom : S.check ⟨α, η⟩ₖ ∈ domain (genericFunction hκ hG) := by
    rw [domain_eq_of_mem_function (genericFunction_mem_function hκ hG), S.check_mem_iff]
    exact kpair_mem_iff.mpr ⟨hα, hη⟩
  obtain ⟨p, hp, hh⟩ := (mem_genericFunction hκ hG _).mp (kpair_value_mem hdom)
  obtain ⟨c, hc, he⟩ := (S.mem_check_iff p _).mp hh
  have hpc := ((mem_woodinCollapse κ δ p).mp (hG.1.1 p hp)).1 _ hc
  obtain ⟨a, ha, x, _, rfl⟩ := mem_prod_iff.mp hpc
  rw [S.check_kpair a x] at he
  have he' := kpair_iff.mp he
  have hae : a = ⟨α, η⟩ₖ := (S.check_eq_iff _ _).mp he'.1.symm
  subst a
  rw [he'.2, S.check_mem_iff]
  exact ((mem_woodinCollapse κ δ p).mp (hG.1.1 p hp)).2.2.2 α η x hc

theorem genericFunction_hits_row {η x : V} (hη : η ∈ δ) (hxδ : x ∈ hierarchy δ)
    (hxη : x ∈ hierarchy (ordinalAdd (1 : V) η)) :
    ∃ α ∈ κ, (genericFunction hκ hG) ‘
      ((woodinCollapseContext hκ δ G hG).check ⟨α, η⟩ₖ) =
      (woodinCollapseContext hκ δ G hG).check x := by
  let S := woodinCollapseContext hκ δ G hG
  obtain ⟨p, hpG, hp⟩ := hG.2 _ (woodinCollapse_value_dense hκ hη hxδ hxη)
  obtain ⟨α, hα, hx⟩ := (mem_sep_iff.mp hp).2
  refine ⟨α, hα, value_eq_of_kpair_mem ?_⟩
  apply (mem_genericFunction hκ hG _).mpr
  refine ⟨p, hpG, ?_⟩
  rw [← S.check_kpair, S.check_mem_iff]
  exact hx

noncomputable def rowFunction (η : V) : (woodinCollapseContext hκ δ G hG).Model :=
  definableGraph ((woodinCollapseContext hκ δ G hG).check κ)
    (fun a ↦ (genericFunction hκ hG) ‘ ⟨a, (woodinCollapseContext hκ δ G hG).check η⟩ₖ)
    (by definability)

theorem rowFunction_value {η α : V} (hα : α ∈ κ) :
    (rowFunction hκ hG η) ‘ ((woodinCollapseContext hκ δ G hG).check α) =
      (genericFunction hκ hG) ‘ ((woodinCollapseContext hκ δ G hG).check ⟨α, η⟩ₖ) := by
  let S := woodinCollapseContext hκ δ G hG
  rw [rowFunction, value_definableGraph _ _ _ ((S.check_mem_iff _ _).mpr hα), S.check_kpair]

theorem rowFunction_mem_function [IsOrdinal δ] {η : V} (hη : η ∈ δ) :
    rowFunction hκ hG η ∈
      (woodinCollapseContext hκ δ G hG).check (hierarchy (ordinalAdd (1 : V) η)) ^
      (woodinCollapseContext hκ δ G hG).check κ := by
  let S := woodinCollapseContext hκ δ G hG
  apply definableGraph_mem_function_of_mapsTo
  intro a ha
  obtain ⟨α, hα, rfl⟩ := (S.mem_check_iff κ a).mp ha
  rw [← S.check_kpair]
  exact genericFunction_row_value hκ hG hα hη

theorem rowFunction_range [IsOrdinal δ] {η : V} (hη : η ∈ δ)
    (hsub : hierarchy (ordinalAdd (1 : V) η) ⊆ hierarchy δ) :
    range (rowFunction hκ hG η) =
      (woodinCollapseContext hκ δ G hG).check (hierarchy (ordinalAdd (1 : V) η)) := by
  let S := woodinCollapseContext hκ δ G hG
  apply SetTheory.subset_antisymm (range_subset_of_mem_function (rowFunction_mem_function hκ hG hη))
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (S.mem_check_iff _ x).mp hx
  obtain ⟨α, hα, hv⟩ := genericFunction_hits_row hκ hG hη (hsub a ha) ha
  have hval := (rowFunction_value hκ hG (η := η) hα).trans hv
  have := IsFunction.of_mem (rowFunction_mem_function hκ hG hη)
  exact mem_range_of_kpair_mem (kpair_mem_iff_value.mpr ⟨by
    rw [domain_eq_of_mem_function (rowFunction_mem_function hκ hG hη), S.check_mem_iff]
    exact hα, hval⟩)

theorem check_row_wellOrderable [IsOrdinal δ] {η : V} (hη : η ∈ δ)
    (hsub : hierarchy (ordinalAdd (1 : V) η) ⊆ hierarchy δ) :
    IsWellOrderable ((woodinCollapseContext hκ δ G hG).check
      (hierarchy (ordinalAdd (1 : V) η))) := by
  let := hκ.1.1
  exact wellOrderable_of_surjective_function (ordinal_wellOrderable _)
    (rowFunction_mem_function hκ hG hη) (rowFunction_range hκ hG hη hsub)

theorem rowFunction_surjective_of_regular (hδ : IsRegularCardinal δ) {η : V} (hη : η ∈ δ) :
    rowFunction hκ hG η ∈
      (woodinCollapseContext hκ δ G hG).check (hierarchy (ordinalAdd (1 : V) η)) ^
      (woodinCollapseContext hκ δ G hG).check κ ∧
    range (rowFunction hκ hG η) =
      (woodinCollapseContext hκ δ G hG).check (hierarchy (ordinalAdd (1 : V) η)) := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hη
  let : IsOrdinal (1 : V) := IsOrdinal.of_mem (show (1 : V) ∈ (ω : V) by simp)
  have hηδ := regularCardinal_ordinalAdd_closed hδ (hδ.2.1 1 (by simp)) hη
  exact ⟨rowFunction_mem_function hκ hG hη,
    rowFunction_range hκ hG hη (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hηδ))⟩

end WoodinCollapseModel
end ZFVP
