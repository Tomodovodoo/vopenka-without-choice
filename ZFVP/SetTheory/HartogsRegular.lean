import ZFVP.SetTheory.CardinalSmallUnions
import ZFVP.SetTheory.DependentChoiceCardinal
import ZFVP.SetTheory.NaturalPairing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem succ_cardLE_of_square {κ α : V} [IsOrdinal α]
    (hzero : (∅ : V) ∈ κ) (hone : (1 : V) ∈ κ)
    (hprod : (κ ×ˢ κ) ≤# κ) (hα : α ≤# κ) : succ α ≤# κ := by
  classical
  obtain ⟨g, hg, hginj⟩ := hα
  let F : V → V := fun x ↦ if x = α then ⟨1, (∅ : V)⟩ₖ else ⟨(∅ : V), g ‘ x⟩ₖ
  have hF : ℒₛₑₜ-function₁ F := by
    have hh : ℒₛₑₜ-relation (fun y x : V ↦
        (x = α ∧ y = ⟨1, (∅ : V)⟩ₖ) ∨ (x ≠ α ∧ y = ⟨(∅ : V), g ‘ x⟩ₖ)) := by definability
    apply Language.Definable.of_iff hh
    intro v
    by_cases hx : v 1 = α <;> simp [F, hx]
  let f := definableGraph (succ α) F hF
  have hf : f ∈ (κ ×ˢ κ) ^ (succ α) := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
    intro x hx
    rcases mem_succ_iff.mp hx with rfl | hx
    · simp only [F, ite_eq_left rfl]
      exact kpair_mem_iff.mpr ⟨hone, hzero⟩
    · have hn : x ≠ α := fun he ↦ mem_irrefl α (he ▸ hx)
      simp only [F, ite_eq_right hn]
      exact kpair_mem_iff.mpr ⟨hzero, function_value_mem hg hx⟩)
  apply CardLE.trans (Y := κ ×ˢ κ) ?_ hprod
  refine ⟨f, hf, ?_⟩
  intro x y z hx hy
  obtain ⟨hxD, hzx⟩ := (pair_mem_definableGraph_iff _ F hF x z).mp hx
  obtain ⟨hyD, hzy⟩ := (pair_mem_definableGraph_iff _ F hF y z).mp hy
  have he : F x = F y := hzx.symm.trans hzy
  by_cases hxα : x = α
  · by_cases hyα : y = α
    · exact hxα.trans hyα.symm
    · have hh := (kpair_iff.mp (show ⟨(1 : V), (∅ : V)⟩ₖ = ⟨(∅ : V), g ‘ y⟩ₖ by simpa [F, hxα, hyα] using he)).1
      exact False.elim (not_mem_empty (hh ▸ (show (∅ : V) ∈ (1 : V) by simp [one_def, zero_def])))
  · by_cases hyα : y = α
    · have hh := (kpair_iff.mp (show ⟨(∅ : V), g ‘ x⟩ₖ = ⟨(1 : V), (∅ : V)⟩ₖ by simpa [F, hxα, hyα] using he)).1
      exact False.elim (not_mem_empty (hh.symm ▸ (show (∅ : V) ∈ (1 : V) by simp [one_def, zero_def])))
    · have hxA := (mem_succ_iff.mp hxD).resolve_left hxα
      have hyA := (mem_succ_iff.mp hyD).resolve_left hyα
      have hv : g ‘ x = g ‘ y := by simpa [F, hxα, hyα] using he
      exact injective_value_eq hg hginj hxA hyA hv

theorem hartogsNumber_regular_of_square {κ : V} [IsOrdinal κ]
    (hω : (ω : V) ⊆ κ) (hprod : (κ ×ˢ κ) ≤# κ)
    (hDC : InternalDependentChoiceAt κ) : IsRegularCardinal (hartogsNumber κ) := by
  have hκH : κ ∈ hartogsNumber κ := ordinal_cardLE_iff_mem_hartogsNumber.mp (CardLE.refl κ)
  have hκsub : κ ⊆ hartogsNumber κ := IsOrdinal.toIsTransitive.transitive _ hκH
  refine ⟨hartogsNumber_initial κ, (fun x hx ↦ hκsub x (hω x hx)), ?_⟩
  apply SetTheory.subset_antisymm (internalCofinality_subset _) ?_
  rcases IsOrdinal.subset_iff.mp (internalCofinality_subset (hartogsNumber κ)) with heq | hlt
  · intro x hx
    exact (congrArg (fun y : V ↦ x ∈ y) heq).mpr hx
  have hβκ : internalCofinality (hartogsNumber κ) ⊆ κ :=
    (initialOrdinal_cardLE_iff (internalCofinality_initial _)).mp (cardLE_of_mem_hartogsNumber hlt)
  obtain ⟨f, hf⟩ := cofinalMap_exists (hartogsNumber κ)
  let β := internalCofinality (hartogsNumber κ)
  let C := definableGraph β (fun i ↦ succ (f ‘ i)) (by definability)
  have hC : IsFunction C := definableGraph_isFunction _ _ _
  let := hC
  have hd : domain C = β := domain_definableGraph _ _ _
  have hz : (∅ : V) ∈ κ := hω _ (by simp)
  have h1 : (1 : V) ∈ κ := hω _ (by simp)
  have hcount : ∀ i ∈ β, (C ‘ i) ≤# κ := by
    intro i hi
    rw [show C ‘ i = succ (f ‘ i) from value_definableGraph _ _ _ hi]
    have hv := function_value_mem hf.1 hi
    let := IsOrdinal.of_mem hv
    exact succ_cardLE_of_square hz h1 hprod (cardLE_of_mem_hartogsNumber hv)
  obtain ⟨g, hg⟩ := ordinal_family_injections (hDC.downward hβκ) hcount
  have hu := union_cardLE_ordinal_prod_of_injection_family hd hg
  have hs : (β ×ˢ κ) ⊆ (κ ×ˢ κ) := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    exact kpair_mem_iff.mpr ⟨hβκ _ ha, hb⟩
  have hcover : hartogsNumber κ ⊆ ⋃ˢ range C := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hf.2 x hx
    have hv := function_value_mem hf.1 hi
    let := IsOrdinal.of_mem hx
    let := IsOrdinal.of_mem hv
    have hxc : x ∈ C ‘ i := by
      rw [show C ‘ i = succ (f ‘ i) from value_definableGraph _ _ _ hi]
      exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hxi)
    have hCr : C ‘ i ∈ range C := mem_range_of_kpair_mem (kpair_value_mem (hd.symm ▸ hi))
    exact mem_sUnion_iff.mpr ⟨C ‘ i, hCr, hxc⟩
  exact False.elim (not_hartogsNumber_cardLE κ
    ((cardLE_of_subset hcover).trans (hu.trans ((cardLE_of_subset hs).trans hprod))))

theorem hartogsNumber_omega_regular (hDC : InternalDependentChoiceAt (ω : V)) :
    IsRegularCardinal (hartogsNumber (ω : V)) :=
  hartogsNumber_regular_of_square (subset_refl _) omega_prod_cardLE_omega hDC

end ZFVP







