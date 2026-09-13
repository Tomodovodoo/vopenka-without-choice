import ZFVP.ModelTheory.LevyRelativeConeHomogeneity
import ZFVP.ModelTheory.LevyHighCoordinateTrace
import ZFVP.ModelTheory.LevyTraceMatching

/-! Isomorphism of the two complementary cones for Boolean conditions inside a high cone.

Take two nonzero Boolean conditions `b` and `c` of the completion of `Coll(ω, <κ)`, each inside
the regular cone of a condition that gives a value at a coordinate in a column at or above `ξ`
with infinitely many admissible values. The complements `¬b` and `¬c` are then nonzero and both
have trace the whole poset (ZFVP/ModelTheory/LevyHighCoordinateTrace.lean), so the relative
homogeneity theorem of ZFVP/ModelTheory/LevyRelativeConeHomogeneity.lean gives an isomorphism of
the cone of `¬b` onto the cone of `¬c` that commutes with meeting any set determined below `ξ`.

`coneImage_eq_of_equivariant` rewrites the pointwise equivariance clause
`g ‘ (z ∩ a) = (g ‘ z) ∩ a` into the form `coneImage P R u g (a ∩ u) = a ∩ v` that the Solovay
corollary chain uses: on the top `u` of the cone the extended map is the map, and the map takes
the top to the top; when `a ∩ u` is empty both sides are empty.

`levy_exists_complement_cone_isomorphism_highCoordinate` puts the two together, and
`levy_exists_complement_cone_isomorphism_supportValues` restates it with the clause over the base
support values of a family, which lie in the determined algebra once they are determined
below `ξ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### From pointwise equivariance to the support clause -/

/-- The support clause of a cone isomorphism follows from equivariance at the top of the cone.

For nonzero `a ∩ u` the meet is a condition of the cone of `u`, so `coneImage` is the value of
`g` there, and equivariance at `z := u` together with `g ‘ u = v` computes that value as `a ∩ v`.
For `a ∩ u` empty both sides are empty, which is the hypothesis `hempty`. -/
theorem coneImage_eq_of_equivariant {P R u v a g : V} (hR : IsForcingPreorder P R)
    (hu : u ∈ booleanConditions P R) (hv : v ∈ booleanConditions P R)
    (hg : IsForcingIsomorphism (forcingCone (booleanConditions P R) (booleanOrder P R) u)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) u))
      (forcingCone (booleanConditions P R) (booleanOrder P R) v)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) v)) g)
    (ha : IsForcingRegular P R a)
    (hequi : ∀ z, z ∈ forcingCone (booleanConditions P R) (booleanOrder P R) u →
      z ∩ a ≠ (∅ : V) → g ‘ (z ∩ a) = (g ‘ z) ∩ a)
    (hempty : a ∩ u = (∅ : V) → a ∩ v = (∅ : V)) :
    coneImage P R u g (a ∩ u) = a ∩ v := by
  by_cases hne : a ∩ u = (∅ : V)
  · rw [hne, coneImage_empty]
    exact (hempty hne).symm
  · have hua : u ∩ a ≠ (∅ : V) := by rw [glue_inter_comm u a]; exact hne
    have hucone : u ∈ forcingCone (booleanConditions P R) (booleanOrder P R) u :=
      (mem_forcingCone_booleanOrder_iff hu).mpr ⟨hu, subset_refl u⟩
    have hcone : u ∩ a ∈ forcingCone (booleanConditions P R) (booleanOrder P R) u :=
      inter_mem_cone_of_ne_empty hu hucone ha hua
    have htop : g ‘ u = v := glue_iso_top hu hv hg
    rw [glue_inter_comm a u, coneImage_value hg hcone, hequi u hucone hua, htop,
      glue_inter_comm v a]

/-! ### The complementary cones of two conditions in high cones -/

/-- The complement of a nonzero Boolean condition inside the regular cone of a condition that uses
a coordinate in a column at or above `ξ` with infinitely many admissible values is nonzero.

If the complement were empty the condition would be the whole poset, which is determined below
`ξ`, so the cone would contain a nonzero determined set, and
`levy_determined_subset_coneRegular_empty` makes the poset empty. -/
theorem levy_forcingNegation_ne_empty_of_highCoordinate {κ ξ r n α β b : V} [IsOrdinal κ]
    (hξ : ξ ⊆ κ) (hr : r ∈ levyCollapse κ) (hn : n ∈ (ω : V)) (hα : α ∈ κ) (hξα : ξ ⊆ α)
    (hωα : (ω : V) ⊆ α) (hmem : ⟨⟨n, α⟩ₖ, β⟩ₖ ∈ r)
    (hb : b ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hbr : b ⊆ coneRegular (levyCollapse κ) (levyOrder κ) r) :
    forcingNegation (levyCollapse κ) (levyOrder κ) b ≠ (∅ : V) := by
  intro h
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hbreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) b := booleanConditions_regular hb
  have hbtop : b = levyCollapse κ :=
    forcingRegular_eq_poset_of_forcingNegation_empty hR hbreg h
  have htopdet : levyCollapse κ ∈ levyDeterminedAlgebra κ ξ :=
    (levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.1
  have hsub : levyCollapse κ ⊆ coneRegular (levyCollapse κ) (levyOrder κ) r := by
    intro z hz
    refine hbr z ?_
    rw [hbtop]
    exact hz
  have hzero : levyCollapse κ = (∅ : V) :=
    levy_determined_subset_coneRegular_empty hξ hr hn hα hξα hωα hmem htopdet hsub
  obtain ⟨p, hp⟩ := ((mem_booleanConditions_iff _ _ _).mp hb).2
  have hpP : p ∈ levyCollapse κ := hbreg.1 p hp
  rw [hzero] at hpP
  exact not_mem_empty hpP

/-- The complementary cone isomorphism. Two nonzero Boolean conditions of the completion of
`Coll(ω, <κ)`, each inside the regular cone of a condition that uses a coordinate in a column at
or above `ξ` with infinitely many admissible values, have isomorphic complementary cones, by an
isomorphism carrying the part of every set determined below `ξ` that lies below the first
complement to the part below the second. -/
theorem levy_exists_complement_cone_isomorphism_highCoordinate {κ ξ r n α β b r' n' α' β' c : V}
    [IsOrdinal κ] (hAC : InternalChoice V) (hξ : ξ ⊆ κ)
    (hr : r ∈ levyCollapse κ) (hn : n ∈ (ω : V)) (hα : α ∈ κ) (hξα : ξ ⊆ α) (hωα : (ω : V) ⊆ α)
    (hmem : ⟨⟨n, α⟩ₖ, β⟩ₖ ∈ r)
    (hb : b ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hbr : b ⊆ coneRegular (levyCollapse κ) (levyOrder κ) r)
    (hr' : r' ∈ levyCollapse κ) (hn' : n' ∈ (ω : V)) (hα' : α' ∈ κ) (hξα' : ξ ⊆ α')
    (hωα' : (ω : V) ⊆ α') (hmem' : ⟨⟨n', α'⟩ₖ, β'⟩ₖ ∈ r')
    (hc : c ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hcr : c ⊆ coneRegular (levyCollapse κ) (levyOrder κ) r') :
    ∃ g, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ) b))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ) b)))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ) c))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ) c))) g ∧
      ∀ a, a ∈ levyDeterminedAlgebra κ ξ →
        coneImage (levyCollapse κ) (levyOrder κ) (forcingNegation (levyCollapse κ) (levyOrder κ) b)
            g (a ∩ forcingNegation (levyCollapse κ) (levyOrder κ) b) =
          a ∩ forcingNegation (levyCollapse κ) (levyOrder κ) c := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hbreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) b := booleanConditions_regular hb
  have hcreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) c := booleanConditions_regular hc
  have hNbreg : IsForcingRegular (levyCollapse κ) (levyOrder κ)
      (forcingNegation (levyCollapse κ) (levyOrder κ) b) :=
    forcingNegation_regular hR hbreg.2.1
  have hNcreg : IsForcingRegular (levyCollapse κ) (levyOrder κ)
      (forcingNegation (levyCollapse κ) (levyOrder κ) c) :=
    forcingNegation_regular hR hcreg.2.1
  have hNbB : forcingNegation (levyCollapse κ) (levyOrder κ) b ∈
      booleanConditions (levyCollapse κ) (levyOrder κ) :=
    (mem_booleanConditions_iff _ _ _).mpr ⟨hNbreg, glue_exists_mem_of_ne_empty
      (levy_forcingNegation_ne_empty_of_highCoordinate hξ hr hn hα hξα hωα hmem hb hbr)⟩
  have hNcB : forcingNegation (levyCollapse κ) (levyOrder κ) c ∈
      booleanConditions (levyCollapse κ) (levyOrder κ) :=
    (mem_booleanConditions_iff _ _ _).mpr ⟨hNcreg, glue_exists_mem_of_ne_empty
      (levy_forcingNegation_ne_empty_of_highCoordinate hξ hr' hn' hα' hξα' hωα' hmem' hc hcr)⟩
  have htr : levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b) =
      levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) c) :=
    levyTrace_forcingNegation_eq_of_highCoordinate hξ hr hn hα hξα hωα hmem hb hbr
      hr' hn' hα' hξα' hωα' hmem' hc hcr
  obtain ⟨H, hH, hHequi⟩ :=
    levy_relative_cone_isomorphism_of_levyTrace_eq hAC hξ hNbB hNcB htr
  refine ⟨H, hH, fun a ha ↦ ?_⟩
  refine coneImage_eq_of_equivariant hR hNbB hNcB hH
    ((mem_levyDeterminedAlgebra_iff _ _ _).mp ha).1
    (fun z hz hzn ↦ hHequi a ha z hz hzn) (fun h0 ↦ ?_)
  exact (inter_eq_empty_iff_of_levyTrace_eq hξ hNbreg hNcreg ha htr).mp h0

/-- The same statement with the support clause over the base support values of a family, which is
the form the Solovay corollary chain uses. The base support values are determined below `ξ`, hence
members of the algebra of determined sets. -/
theorem levy_exists_complement_cone_isomorphism_supportValues
    {κ ξ r n α β b r' n' α' β' c K E : V}
    [IsOrdinal κ] (hAC : InternalChoice V) (hξ : ξ ⊆ κ)
    (hr : r ∈ levyCollapse κ) (hn : n ∈ (ω : V)) (hα : α ∈ κ) (hξα : ξ ⊆ α) (hωα : (ω : V) ⊆ α)
    (hmem : ⟨⟨n, α⟩ₖ, β⟩ₖ ∈ r)
    (hb : b ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hbr : b ⊆ coneRegular (levyCollapse κ) (levyOrder κ) r)
    (hr' : r' ∈ levyCollapse κ) (hn' : n' ∈ (ω : V)) (hα' : α' ∈ κ) (hξα' : ξ ⊆ α')
    (hωα' : (ω : V) ⊆ α') (hmem' : ⟨⟨n', α'⟩ₖ, β'⟩ₖ ∈ r')
    (hc : c ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hcr : c ⊆ coneRegular (levyCollapse κ) (levyOrder κ) r')
    (hdet : ∀ a, a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E →
      IsLevyDeterminedBelow κ ξ a) :
    ∃ g, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ) b))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ) b)))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ) c))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ) c))) g ∧
      ∀ a, a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E →
        coneImage (levyCollapse κ) (levyOrder κ) (forcingNegation (levyCollapse κ) (levyOrder κ) b)
            g (a ∩ forcingNegation (levyCollapse κ) (levyOrder κ) b) =
          a ∩ forcingNegation (levyCollapse κ) (levyOrder κ) c := by
  obtain ⟨g, hg, hclause⟩ :=
    levy_exists_complement_cone_isomorphism_highCoordinate hAC hξ hr hn hα hξα hωα hmem hb hbr
      hr' hn' hα' hξα' hωα' hmem' hc hcr
  exact ⟨g, hg, fun a ha ↦ hclause a (supportValuesBase_subset_levyDeterminedAlgebra hdet a ha)⟩

end ZFVP
