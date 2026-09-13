import ZFVP.SetTheory.RegularCofinalSurjection
import ZFVP.SetTheory.Hessenberg
import ZFVP.SetTheory.WellOrderedSurjection

/-! A set which cannot surject onto κ cannot gain a successor-cardinal surjection by multiplying by lam ≥ κ. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem orderType_range_lt_of_no_surjection {κ θ Y f : V} [IsOrdinal κ] [IsOrdinal θ]
    (hne : IsNonempty κ) (hno : ∀ g ∈ κ ^ Y, range g ≠ κ) (hf : f ∈ θ ^ Y) :
    internalOrderType (membershipRelation (range f)) (range f) ∈ κ := by
  have hw := ordinalSubset_membership_wellOrder (range_subset_of_mem_function hf)
  let η := internalOrderType (membershipRelation (range f)) (range f)
  let := internalOrderType_ordinal hw
  by_contra hlt
  have hκη : κ ⊆ η := by
    rcases IsOrdinal.mem_trichotomy η κ with h | h | h
    · exact (hlt h).elim
    · exact h ▸ subset_refl η
    · exact IsOrdinal.toIsTransitive.transitive _ h
  have hinj : κ ≤# range f := (cardLE_of_subset hκη).trans (internalOrderType_cardEQ hw).1
  obtain ⟨g, hg, hgr⟩ := surjection_of_injection hinj hne
  have hfr := mem_function_range_of_mem_function hf
  exact hno (compose f g) (compose_function hfr hg) (range_compose_surjective hfr hg rfl hgr)

noncomputable def ordinalMapColumn (θ Y g β : V) : V :=
  {z ∈ θ ; ∃ a ∈ Y, z = g ‘ ⟨a, β⟩ₖ}

instance ordinalMapColumn_definable : ℒₛₑₜ-function₄[V] ordinalMapColumn := by
  have h : ℒₛₑₜ-relation₅[V] (fun C θ Y g β ↦ ∀ z, z ∈ C ↔
      z ∈ θ ∧ ∃ a ∈ Y, z = g ‘ ⟨a, β⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [ordinalMapColumn, mem_sep_iff]
  rfl

theorem no_surjection_prod_hartogs {κ lam Y g : V} [IsOrdinal κ]
    (hκne : IsNonempty κ) (hκlam : κ ⊆ lam) (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam)
    (hno : ∀ f ∈ κ ^ Y, range f ≠ κ) (hg : g ∈ (hartogsNumber lam) ^ (Y ×ˢ lam)) :
    range g ≠ hartogsNumber lam := by
  intro hgr
  let θ := hartogsNumber lam
  let := hlam.1
  let C : V → V := ordinalMapColumn θ Y g
  have hC : ℒₛₑₜ-function₁ C := by
    have hrel : ℒₛₑₜ-relation[V] (fun c β ↦ ∀ z, z ∈ c ↔
        z ∈ θ ∧ ∃ a ∈ Y, z = g ‘ ⟨a, β⟩ₖ) := by definability
    apply Language.Definable.of_iff hrel
    intro v
    rw [mem_ext_iff]
    simp only [C, ordinalMapColumn, mem_sep_iff]
    rfl
  have hcsub (β : V) : C β ⊆ θ := fun _ hz ↦ (mem_sep_iff.mp hz).1
  have hcwo (β : V) : IsInternalWellOrder (membershipRelation (C β)) (C β) :=
    ordinalSubset_membership_wellOrder (hcsub β)
  have hct (β : V) (hβ : β ∈ lam) : internalOrderType (membershipRelation (C β)) (C β) ∈ κ := by
    let F : V → V := fun a ↦ g ‘ ⟨a, β⟩ₖ
    have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
    let f := definableGraph Y F hF
    have hf : f ∈ θ ^ Y := definableGraph_mem_function_of_mapsTo _ _ _ _
      (fun a ha ↦ function_value_mem hg (kpair_mem_iff.mpr ⟨ha, hβ⟩))
    have hfr : range f = C β := by
      apply mem_ext
      intro z
      rw [range_definableGraph, repl_spec]
      simp only [C, ordinalMapColumn, mem_sep_iff]
      change (∃ a ∈ Y, z = F a) ↔ z ∈ θ ∧ ∃ a ∈ Y, z = g ‘ ⟨a, β⟩ₖ
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨function_value_mem hg (kpair_mem_iff.mpr ⟨ha, hβ⟩), a, ha, rfl⟩
      · exact fun hz ↦ hz.2
    simpa only [hfr] using orderType_range_lt_of_no_surjection hκne hno hf
  let E : V → V := fun β ↦ mostowskiMap (membershipRelation (C β)) (C β)
  have hE : ℒₛₑₜ-function₁ E := by unfold E; definability
  have hefun (β : V) (hβ : β ∈ lam) : E β ∈ κ ^ (C β) :=
    mem_function_of_mem_function_of_subset
      (mostowskiMap_isTransitiveCollapse (hcwo β).2.1 (internalWellOrder_extensional (hcwo β))).2.1
      (IsOrdinal.toIsTransitive.transitive _ (hct β hβ))
  have hprod : lam ×ˢ κ ≤# lam := prod_cardLE_of_cardLE_initial hlam hω
    (CardLE.refl lam) (cardLE_of_subset hκlam)
  apply not_hartogsNumber_cardLE lam
  apply CardLE.trans (Y := lam ×ˢ κ) ?_ hprod
  apply cardLE_of_separating_relation (wellOrderable_of_cardLE hprod (ordinal_wellOrderable lam))
    (fun z t ↦ z ∈ C (kpair.π₁ t) ∧ (E (kpair.π₁ t)) ‘ z = kpair.π₂ t) (by definability)
  · intro z hz
    obtain ⟨aβ, hp⟩ := mem_range_iff.mp (hgr.symm ▸ hz)
    have haβ := (mem_of_mem_functions hg hp).1
    obtain ⟨a, ha, β, hβ, rfl⟩ := mem_prod_iff.mp haβ
    have : IsFunction g := IsFunction.of_mem hg
    have hzC : z ∈ C β := mem_sep_iff.mpr ⟨hz, a, ha, (value_eq_of_kpair_mem hp).symm⟩
    exact ⟨⟨β, (E β) ‘ z⟩ₖ, kpair_mem_iff.mpr ⟨hβ, function_value_mem (hefun β hβ) hzC⟩,
      by simp only [kpair.π₁_kpair, kpair.π₂_kpair, and_true, hzC]⟩
  · intro z _ w _ t ht hz hw
    obtain ⟨β, hβ, i, _, rfl⟩ := mem_prod_iff.mp ht
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hz hw
    exact (mostowskiMap_isTransitiveCollapse (hcwo β).2.1
      (internalWellOrder_extensional (hcwo β))).2.2.2.1 z hz.1 w hw.1 (hz.2.trans hw.2.symm)

end ZFVP

