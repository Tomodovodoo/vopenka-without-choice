import ZFVP.SetTheory.CardinalSmallUnions
import ZFVP.SetTheory.LeastDependentChoiceFailure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCardinalSmall.union {κ A B : V} (hκ : IsRegularCardinal κ)
    (hA : IsCardinalSmall κ A) (hB : IsCardinalSmall κ B) : IsCardinalSmall κ (A ∪ B) := by
  classical
  let F : V → V := fun i ↦ if i = (0 : V) then A else B
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation (fun x i : V ↦ (i = 0 ∧ x = A) ∨ (i ≠ 0 ∧ x = B)) := by definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = F (v 1) ↔ _
    unfold F
    split <;> simp_all
  let C := definableGraph (2 : V) F hF
  have hd : domain C = (2 : V) := domain_definableGraph _ _ _
  have hsmall : ∀ i ∈ (2 : V), IsCardinalSmall κ (C ‘ i) := by
    intro i hi
    rw [show C ‘ i = F i from value_definableGraph _ _ _ hi]
    dsimp [F]
    split_ifs <;> assumption
  have hu := regularCardinal_small_union hκ (hκ.2.1 _ (by simp))
    (dependentChoiceAt_finite (2 : V) (by simp)) hd hsmall
  have hr : range C = ({A, B} : V) := by
    apply mem_ext
    intro x
    rw [range_definableGraph, repl_spec]
    constructor
    · rintro ⟨i, _, rfl⟩
      dsimp [F]
      split_ifs <;> simp
    · intro hx
      rcases show x = A ∨ x = B from by simpa using hx with rfl | rfl
      · exact ⟨0, by simp, by simp [F]⟩
      · exact ⟨1, by simp, by simp [F]⟩
  simpa [hr] using hu

theorem not_cardinalSmall_self {κ : V} (hκ : IsInitialOrdinal κ) : ¬IsCardinalSmall κ κ := by
  rintro ⟨α, hα, hinj⟩
  exact hκ.2 α hα hinj

theorem ordinalSubset_membership_wellOrder {κ D : V} [IsOrdinal κ] (hD : D ⊆ κ) :
    IsInternalWellOrder (membershipRelation D) D := by
  refine ⟨fun z hz ↦ (mem_sep_iff.mp hz).1, membershipRelation_wellFounded D, ?_, ?_⟩
  · intro x hx y _ z hz hxy hyz
    let := IsOrdinal.of_mem (hD z hz)
    exact (pair_mem_membershipRelation D x z).mpr ⟨hx, hz,
      IsOrdinal.toIsTransitive.mem_trans ((pair_mem_membershipRelation D x y).mp hxy).2.2
        ((pair_mem_membershipRelation D y z).mp hyz).2.2⟩
  · intro x hx y hy
    let := IsOrdinal.of_mem (hD x hx)
    let := IsOrdinal.of_mem (hD y hy)
    rcases IsOrdinal.mem_trichotomy x y with h | h | h
    · exact Or.inl ((pair_mem_membershipRelation D x y).mpr ⟨hx, hy, h⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((pair_mem_membershipRelation D y x).mpr ⟨hy, hx, h⟩))

theorem ordinalSubset_collapse_value_subset {κ D : V} [IsOrdinal κ] (hD : D ⊆ κ) :
    ∀ x ∈ D, (mostowskiMap (membershipRelation D) D) ‘ x ⊆ x := by
  rw [mostowskiMap_of_wellFounded (membershipRelation_wellFounded D)]
  apply internalWellFounded_induction (membershipRelation_wellFounded D)
    (fun x ↦ (collapseGraph (membershipRelation_wellFounded D)) ‘ x ⊆ x) (by definability)
  intro x hx ih z hz
  obtain ⟨y, hy, hyx, hval⟩ := (mem_collapseGraph_value _ hx).mp hz
  have hyx' := ((pair_mem_membershipRelation D y x).mp hyx).2.2
  let := IsOrdinal.of_mem (hD x hx)
  let := IsOrdinal.of_mem (hD y hy)
  have hw := ordinalSubset_membership_wellOrder hD
  have ho := internalOrderType_ordinal hw
  let : IsOrdinal (internalOrderType (membershipRelation D) D) := ho
  have hc := mostowskiMap_isTransitiveCollapse hw.2.1 (internalWellOrder_extensional hw)
  have hym : (mostowskiMap (membershipRelation D) D) ‘ y ∈ internalOrderType (membershipRelation D) D :=
    function_value_mem hc.2.1 hy
  rw [mostowskiMap_of_wellFounded (membershipRelation_wellFounded D)] at hym
  let := IsOrdinal.of_mem hym
  exact hval ▸ ordinal_mem_of_subset_mem (ih y hy hyx) hyx'

theorem ordinalSubset_orderType_subset {κ D : V} [IsOrdinal κ] (hD : D ⊆ κ) :
    internalOrderType (membershipRelation D) D ⊆ κ := by
  have hw := ordinalSubset_membership_wellOrder hD
  let := internalOrderType_ordinal hw
  have hc := mostowskiMap_isTransitiveCollapse hw.2.1 (internalWellOrder_extensional hw)
  let := IsFunction.of_mem hc.2.1
  intro z hz
  obtain ⟨x, hxz⟩ := mem_range_iff.mp hz
  have hx : x ∈ D := domain_eq_of_mem_function hc.2.1 ▸ mem_domain_of_kpair_mem hxz
  have hv := value_eq_of_kpair_mem hxz
  have hm := function_value_mem hc.2.1 hx
  change _ ∈ internalOrderType (membershipRelation D) D at hm
  let := IsOrdinal.of_mem hm
  let := IsOrdinal.of_mem (hD x hx)
  exact hv ▸ ordinal_mem_of_subset_mem (ordinalSubset_collapse_value_subset hD x hx) (hD x hx)

theorem smallComplement_orderType {κ A : V} (hκ : IsRegularCardinal κ)
    (hA : IsCardinalSmall κ A) :
    internalOrderType (membershipRelation (κ \ A)) (κ \ A) = κ := by
  let := hκ.1.1
  have hD : κ \ A ⊆ κ := by
    intro x hx
    exact (show x ∈ κ ∧ x ∉ A by simpa using hx).1
  have hw := ordinalSubset_membership_wellOrder hD
  let := internalOrderType_ordinal hw
  rcases IsOrdinal.subset_iff.mp (ordinalSubset_orderType_subset hD) with h | h
  · exact h
  · have hs : IsCardinalSmall κ (κ \ A) :=
      ⟨internalOrderType (membershipRelation (κ \ A)) (κ \ A), h, (internalOrderType_cardEQ hw).2⟩
    have hu := hA.union hκ hs
    have hsub : κ ⊆ A ∪ (κ \ A) := by
      intro x hx
      by_cases ha : x ∈ A
      · exact mem_union_iff.mpr (Or.inl ha)
      · exact mem_union_iff.mpr (Or.inr (by simp [hx, ha]))
    exact False.elim (not_cardinalSmall_self hκ.1 (hu.subset hsub))

end ZFVP
