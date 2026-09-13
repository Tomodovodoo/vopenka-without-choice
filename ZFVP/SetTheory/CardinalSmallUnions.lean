import ZFVP.SetTheory.OrdinalProductBound
import ZFVP.SetTheory.OrdinalIndexedChoice
import ZFVP.SetTheory.WellOrderedCardinal

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCardinalSmall.wellOrderable {κ A : V} [IsOrdinal κ] (h : IsCardinalSmall κ A) :
    IsWellOrderable A := by
  obtain ⟨α, hα, hA⟩ := h
  exact (wellOrderable_iff_cardLE_ordinal A).mpr ⟨α, IsOrdinal.of_mem hα, hA⟩

theorem IsCardinalSmall.cardinal_mem {κ A : V} [IsOrdinal κ] (h : IsCardinalSmall κ A) :
    wellOrderedCardinal A ∈ κ := by
  have hA := h.wellOrderable
  obtain ⟨α, hα, hinj⟩ := h
  let := IsOrdinal.of_mem hα
  let := (wellOrderedCardinal_initial hA).1
  have hsub := (initialOrdinal_cardLE_iff (wellOrderedCardinal_initial hA)).mp
    ((wellOrderedCardinal_cardEQ hA).1.trans hinj)
  exact ordinal_mem_of_subset_mem hsub hα

noncomputable def ordinalCoverIndex (γ C x : V) : V := ⋂ˢ {i ∈ γ ; x ∈ C ‘ i}

instance ordinalCoverIndex_definable : ℒₛₑₜ-function₃[V] ordinalCoverIndex := by
  have h : ℒₛₑₜ-function₃[V] (fun γ C x ↦ {i ∈ γ ; x ∈ C ‘ i}) := by
    have hrel : ℒₛₑₜ-relation₄[V] (fun S γ C x ↦ ∀ i, i ∈ S ↔ i ∈ γ ∧ x ∈ C ‘ i) := by
      definability
    apply Language.Definable.of_iff hrel
    intro v
    rw [mem_ext_iff]
    simp
  unfold ordinalCoverIndex
  definability

theorem ordinalCoverIndex_spec {γ C x : V} [IsOrdinal γ] [IsFunction C]
    (hd : domain C = γ) (hx : x ∈ ⋃ˢ range C) :
    ordinalCoverIndex γ C x ∈ γ ∧ x ∈ C ‘ (ordinalCoverIndex γ C x) := by
  obtain ⟨X, hX, hxX⟩ := mem_sUnion_iff.mp hx
  obtain ⟨i, hiX⟩ := mem_range_iff.mp hX
  have hi : i ∈ γ := hd ▸ mem_domain_of_kpair_mem hiX
  have hxCi : x ∈ C ‘ i := (value_eq_of_kpair_mem hiX).symm ▸ hxX
  let S : V := {i ∈ γ ; x ∈ C ‘ i}
  have : IsNonempty S := ⟨i, mem_sep_iff.mpr ⟨hi, hxCi⟩⟩
  have hm := IsOrdinal.sInter_mem (X := S) (fun i hi ↦ IsOrdinal.of_mem (mem_sep_iff.mp hi).1)
  exact mem_sep_iff.mp hm

theorem union_cardLE_ordinal_prod_of_injection_family {γ α C g : V} [IsOrdinal γ]
    [IsFunction C] (hd : domain C = γ)
    (hg : ∀ i ∈ γ, g ‘ i ∈ α ^ (C ‘ i) ∧ Injective (g ‘ i)) :
    (⋃ˢ range C) ≤# (γ ×ˢ α) := by
  let F : V → V := fun x ↦ ⟨ordinalCoverIndex γ C x, (g ‘ (ordinalCoverIndex γ C x)) ‘ x⟩ₖ
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let f := definableGraph (⋃ˢ range C) F hF
  have hf : f ∈ (γ ×ˢ α) ^ (⋃ˢ range C) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (by
      intro x hx
      have hs := ordinalCoverIndex_spec hd hx
      exact kpair_mem_iff.mpr ⟨hs.1, function_value_mem (hg _ hs.1).1 hs.2⟩)
  refine ⟨f, hf, ?_⟩
  intro x y z hx hy
  obtain ⟨hxU, hzx⟩ := (pair_mem_definableGraph_iff _ F hF x z).mp hx
  obtain ⟨hyU, hzy⟩ := (pair_mem_definableGraph_iff _ F hF y z).mp hy
  have heq : F x = F y := hzx.symm.trans hzy
  have hpair := kpair_iff.mp heq
  have hx' := ordinalCoverIndex_spec hd hxU
  have hy' := ordinalCoverIndex_spec hd hyU
  have hxy : y ∈ C ‘ (ordinalCoverIndex γ C x) := hpair.1.symm ▸ hy'.2
  have hval : (g ‘ (ordinalCoverIndex γ C x)) ‘ x = (g ‘ (ordinalCoverIndex γ C x)) ‘ y := by
    simpa only [← hpair.1] using hpair.2
  exact injective_value_eq (hg _ hx'.1).1 (hg _ hx'.1).2 hx'.2 hxy hval

theorem ordinal_family_injections {γ α C : V} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ) (hcount : ∀ i ∈ γ, (C ‘ i) ≤# α) :
    ∃ g, ∀ i ∈ γ, g ‘ i ∈ α ^ (C ‘ i) ∧ Injective (g ‘ i) := by
  let B : V → V := fun i ↦ {f ∈ α ^ (C ‘ i) ; Injective f}
  have hB : ℒₛₑₜ-function₁ B := by
    have h : ℒₛₑₜ-relation (fun S i : V ↦ ∀ f, f ∈ S ↔ f ∈ α ^ (C ‘ i) ∧ Injective f) := by
      definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp [B]
  obtain ⟨g, _, _, hg⟩ := ordinal_choice_for_definable_family hDC B hB (by
    intro i hi
    obtain ⟨f, hf, hinj⟩ := hcount i hi
    exact ⟨f, mem_sep_iff.mpr ⟨hf, hinj⟩⟩)
  exact ⟨g, fun i hi ↦ mem_sep_iff.mp (hg i hi)⟩

theorem regularCardinal_small_union {κ γ C : V} (hκ : IsRegularCardinal κ)
    (hγ : γ ∈ κ) (hDC : InternalDependentChoiceAt γ) [IsFunction C]
    (hd : domain C = γ) (hsmall : ∀ i ∈ γ, IsCardinalSmall κ (C ‘ i)) :
    IsCardinalSmall κ (⋃ˢ range C) := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  let F := definableGraph γ (fun i ↦ wellOrderedCardinal (C ‘ i)) (by definability)
  have hF : F ∈ κ ^ γ := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
    intro i hi
    exact (hsmall i hi).cardinal_mem)
  obtain ⟨α, hα, hb⟩ := regularCardinal_maps_bounded hκ hγ hF
  let := IsOrdinal.of_mem hα
  have hinj : ∀ i ∈ γ, (C ‘ i) ≤# α := by
    intro i hi
    have hci := hb i hi
    rw [show F ‘ i = wellOrderedCardinal (C ‘ i) from value_definableGraph _ _ _ hi] at hci
    exact (wellOrderedCardinal_cardEQ (hsmall i hi).wellOrderable).2.trans
      (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hci))
  obtain ⟨g, hg⟩ := ordinal_family_injections hDC hinj
  exact (regularCardinal_ordinal_prod_small hκ hα hγ).of_cardLE
    (union_cardLE_ordinal_prod_of_injection_family hd hg)

end ZFVP
