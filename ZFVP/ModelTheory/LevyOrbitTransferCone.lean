import ZFVP.ModelTheory.BooleanOrbitConeIsomorphism
import ZFVP.ModelTheory.LevyComplementCone
import ZFVP.ModelTheory.LevyOrbitTransferReduction

/-! The cone hypothesis of the Solovay corollary, reduced to an alignment statement about regular
cones of the Levy collapse.

`ForcingContext.ConeOrbitTransfer` asks, for every orbit filter `H`, for two conditions of the
Boolean completion, one met by the generic and one in `H`, and two isomorphisms of cones matching
them and fixing the base support values. `exists_orbit_cone_isomorphism_support` produces such a
pair, with the condition on the side of the generic already a regular cone `coneRegular r` of a
condition `r` of the generic filter, and `exists_trace_coneRegular_below` shrinks the condition on
the side of `H` to a regular cone as well. What is not available is that the two can be taken to be
regular cones at the same time: an isomorphism of the cone below `q₀` onto the cone below `p₀`
sends `q₀` to `p₀`, so once one side is prescribed the other is its image, and the image of a
regular cone need not be a regular cone.

`ForcingContext.IsConeAligned` is that missing statement, in the shape the rest of the chain
consumes. This module proves the bookkeeping around it.

* Direction. `exists_orbit_cone_isomorphism_support` gives the isomorphism from the side of `H`
  onto the side of the generic; `ConeOrbitTransfer` wants it the other way. `coneImage_inverse`
  and `filterTransfer_inverse` restate the support clause and the filter clause for the inverse
  map. The support clause is kept in `coneImage` form on both sides, which is what makes the
  translation exact. In the plain form `ψ ‘ (a ∩ q₀) = a ∩ p₀` the zero case is a gap: that form
  says nothing when `a ∩ q₀` is empty, and then the inverse clause `a ∩ p₀ = ∅` does not follow.
  `coneImage` closes it, because `coneImage` of the empty set is the empty set, so the hypothesis
  in `coneImage` form says `a ∩ q₀ = ∅ → a ∩ p₀ = ∅` as well.

* Restriction. `coneIsomorphism_restrict` and `coneIsomorphism_restrict_coneImage`: an isomorphism
  `ψ` of the cone below `q₀` onto the cone below `p₀` restricts, along any condition `q₁ ⊆ q₀`, to
  an isomorphism of the cone below `q₁` onto the cone below `ψ ‘ q₁`, and the support clause
  survives the restriction because an order isomorphism of cones preserves meets
  (`coneIsomorphism_value_inter`). With the filter clause this says that the condition on the side
  of `H` may be shrunk freely, in particular to the regular cone supplied by
  `exists_trace_coneRegular_below`.

* Assembly. `coneOrbitTransfer_of_isConeAligned` turns the alignment statement into
  `ConeOrbitTransfer`, and `levy_orbitTransfer_of_aligned` and `solovay_corollary_of_aligned`
  export it through `levy_orbitTransfer_of_cone` and `solovay_corollary_of_cone_transfer`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Meets, restriction and inverse of a cone isomorphism -/

section Cones

variable {P R p0 q0 q1 ψ : V}

/-- A regular set meets a condition in a condition of the cone below it, or not at all. -/
theorem inter_mem_forcingCone_or_empty {a b : V} (ha : IsForcingRegular P R a)
    (hb : b ∈ booleanConditions P R) :
    a ∩ b ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b ∨ a ∩ b = (∅ : V) := by
  by_cases hne : ∃ z : V, z ∈ a ∩ b
  · obtain ⟨z, hz⟩ := hne
    have hab : a ∩ b ∈ booleanConditions P R :=
      (mem_booleanConditions_iff _ _ _).mpr
        ⟨forcingRegular_inter ha (booleanConditions_regular hb), z, hz⟩
    exact Or.inl ((mem_forcingCone_iff _ _ _ _).mpr ⟨hab,
      (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨hab, hb, fun w hw ↦ (mem_inter_iff.mp hw).2⟩⟩)
  · exact Or.inr (mem_ext
      (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hne, fun hz ↦ absurd hz not_mem_empty⟩))

/-- A condition is a member of the cone below itself. -/
theorem self_mem_forcingCone_boolean (hb : q0 ∈ booleanConditions P R) :
    q0 ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q0 :=
  (mem_forcingCone_iff _ _ _ _).mpr
    ⟨hb, (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hb, hb, subset_refl _⟩⟩

/-- A condition below a condition is a member of its cone. -/
theorem mem_forcingCone_of_subset {b c : V} (hb : b ∈ booleanConditions P R)
    (hc : c ∈ booleanConditions P R) (hbc : b ⊆ c) :
    b ∈ forcingCone (booleanConditions P R) (booleanOrder P R) c :=
  (mem_forcingCone_iff _ _ _ _).mpr
    ⟨hb, (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hb, hc, hbc⟩⟩

/-- A member of a cone is a condition below its top. -/
theorem forcingCone_boolean_subset {b c : V}
    (hb : b ∈ forcingCone (booleanConditions P R) (booleanOrder P R) c) : b ⊆ c :=
  ((kpair_mem_booleanOrder_iff _ _ _ _).mp ((mem_forcingCone_iff _ _ _ _).mp hb).2).2.2

/-- The restriction of a map of cones to a smaller cone. -/
noncomputable def coneRestrictMap (P R q1 ψ : V) : V :=
  definableGraph (forcingCone (booleanConditions P R) (booleanOrder P R) q1)
    (fun x ↦ ψ ‘ x) (by definability)

theorem coneRestrictMap_value {x : V}
    (hx : x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q1) :
    (coneRestrictMap P R q1 ψ) ‘ x = ψ ‘ x :=
  value_definableGraph _ _ _ hx

variable
  (hψ : IsForcingIsomorphism
    (forcingCone (booleanConditions P R) (booleanOrder P R) q0)
    (restrictedOrder (booleanOrder P R)
      (forcingCone (booleanConditions P R) (booleanOrder P R) q0))
    (forcingCone (booleanConditions P R) (booleanOrder P R) p0)
    (restrictedOrder (booleanOrder P R)
      (forcingCone (booleanConditions P R) (booleanOrder P R) p0)) ψ)

include hψ

/-- A cone isomorphism reflects inclusion. -/
theorem coneIsomorphism_subset_of_value_subset {x y : V}
    (hx : x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q0)
    (hy : y ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q0)
    (hxy : ψ ‘ x ⊆ ψ ‘ y) : x ⊆ y := by
  have hfx := function_value_mem hψ.1 hx
  have hfy := function_value_mem hψ.1 hy
  have hord : ⟨ψ ‘ x, ψ ‘ y⟩ₖ ∈ restrictedOrder (booleanOrder P R)
      (forcingCone (booleanConditions P R) (booleanOrder P R) p0) :=
    (kpair_mem_restrictedOrder_iff _ _ _ _).mpr
      ⟨(kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨((mem_forcingCone_iff _ _ _ _).mp hfx).1,
          ((mem_forcingCone_iff _ _ _ _).mp hfy).1, hxy⟩, hfx, hfy⟩
  have h := (hψ.2.2.2 x hx y hy).mpr hord
  exact ((kpair_mem_booleanOrder_iff _ _ _ _).mp
    ((kpair_mem_restrictedOrder_iff _ _ _ _).mp h).1).2.2

/-- A cone isomorphism preserves meets. The meet of the Boolean completion is intersection, so
this is the statement that `ψ (x ∩ y) = ψ x ∩ ψ y` whenever `x ∩ y` is again a condition. -/
theorem coneIsomorphism_value_inter (hp0 : p0 ∈ booleanConditions P R) {x y : V}
    (hx : x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q0)
    (hy : y ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q0)
    (hxy : x ∩ y ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q0) :
    ψ ‘ (x ∩ y) = ψ ‘ x ∩ ψ ‘ y := by
  apply SetTheory.subset_antisymm
  · intro z hz
    exact mem_inter_iff.mpr
      ⟨coneIsomorphism_mono hψ hxy hx (fun w hw ↦ (mem_inter_iff.mp hw).1) z hz,
        coneIsomorphism_mono hψ hxy hy (fun w hw ↦ (mem_inter_iff.mp hw).2) z hz⟩
  · intro z hz
    have hfx := function_value_mem hψ.1 hx
    have hfy := function_value_mem hψ.1 hy
    have hfxB := ((mem_forcingCone_iff _ _ _ _).mp hfx).1
    have hfyB := ((mem_forcingCone_iff _ _ _ _).mp hfy).1
    have hfxp : ψ ‘ x ⊆ p0 := forcingCone_boolean_subset hfx
    have hwB : ψ ‘ x ∩ ψ ‘ y ∈ booleanConditions P R :=
      inter_mem_booleanConditions hfxB hfyB hz
    have hwc : ψ ‘ x ∩ ψ ‘ y ∈ forcingCone (booleanConditions P R) (booleanOrder P R) p0 :=
      mem_forcingCone_of_subset hwB hp0 (fun w hw ↦ hfxp w (mem_inter_iff.mp hw).1)
    obtain ⟨u, hu, huv⟩ := isForcingIsomorphism_surjective hψ _ hwc
    have hux : u ⊆ x := coneIsomorphism_subset_of_value_subset hψ hu hx
      (by rw [huv]; exact fun w hw ↦ (mem_inter_iff.mp hw).1)
    have huy : u ⊆ y := coneIsomorphism_subset_of_value_subset hψ hu hy
      (by rw [huv]; exact fun w hw ↦ (mem_inter_iff.mp hw).2)
    have hmono := coneIsomorphism_mono hψ hu hxy
      (fun w hw ↦ mem_inter_iff.mpr ⟨hux w hw, huy w hw⟩)
    rw [huv] at hmono
    exact hmono z hz

/-! #### The inverse isomorphism -/

/-- The support clause of the cone construction, transported to the inverse isomorphism. Both
sides are in `coneImage` form, so the case of an empty intersection is covered. -/
theorem coneImage_inverse (hq0 : q0 ∈ booleanConditions P R) {a : V}
    (ha : IsForcingRegular P R a) (hcone : coneImage P R q0 ψ (a ∩ q0) = a ∩ p0) :
    coneImage P R p0 (converseGraph ψ) (a ∩ p0) = a ∩ q0 := by
  have hinv := isForcingIsomorphism_inverse hψ
  rcases inter_mem_forcingCone_or_empty ha hq0 with hc | hc
  · have hval : ψ ‘ (a ∩ q0) = a ∩ p0 := by rw [← coneImage_value hψ hc]; exact hcone
    have hmem : a ∩ p0 ∈ forcingCone (booleanConditions P R) (booleanOrder P R) p0 := by
      rw [← hval]; exact function_value_mem hψ.1 hc
    rw [coneImage_value hinv hmem, ← hval, converseGraph_value_value hψ.1 hψ.2.1 hc]
  · have h0 : a ∩ p0 = (∅ : V) := by
      rw [← hcone, hc]; exact coneImage_empty _ _ _ _
    rw [h0, hc, coneImage_empty]

/-! #### Restricting to a smaller condition -/

/-- A cone isomorphism restricts along a shrinking of its source: for a condition `q₁ ⊆ q₀` the
map restricts to an isomorphism of the cone below `q₁` with the cone below `ψ ‘ q₁`. -/
theorem coneIsomorphism_restrict (hp0 : p0 ∈ booleanConditions P R)
    (hq0 : q0 ∈ booleanConditions P R) (hq1 : q1 ∈ booleanConditions P R) (hq1q0 : q1 ⊆ q0) :
    IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) q1)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) q1))
      (forcingCone (booleanConditions P R) (booleanOrder P R) (ψ ‘ q1))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (ψ ‘ q1)))
      (coneRestrictMap P R q1 ψ) := by
  have hq1c : q1 ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q0 :=
    mem_forcingCone_of_subset hq1 hq0 hq1q0
  have hpq1 := function_value_mem hψ.1 hq1c
  have hpq1B := ((mem_forcingCone_iff _ _ _ _).mp hpq1).1
  have hpq1p : ψ ‘ q1 ⊆ p0 := forcingCone_boolean_subset hpq1
  have hsub : ∀ x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q1,
      x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q0 := by
    intro x hx
    exact mem_forcingCone_of_subset ((mem_forcingCone_iff _ _ _ _).mp hx).1 hq0
      (subset_trans (forcingCone_boolean_subset hx) hq1q0)
  have hFP : ∀ x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q1,
      ψ ‘ x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) (ψ ‘ q1) := by
    intro x hx
    refine mem_forcingCone_of_subset
      ((mem_forcingCone_iff _ _ _ _).mp (function_value_mem hψ.1 (hsub x hx))).1 hpq1B ?_
    exact coneIsomorphism_mono hψ (hsub x hx) hq1c (forcingCone_boolean_subset hx)
  have hGQ : ∀ y ∈ forcingCone (booleanConditions P R) (booleanOrder P R) (ψ ‘ q1),
      (converseGraph ψ) ‘ y ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q1 := by
    intro y hy
    have hyB := ((mem_forcingCone_iff _ _ _ _).mp hy).1
    have hyp : y ∈ forcingCone (booleanConditions P R) (booleanOrder P R) p0 :=
      mem_forcingCone_of_subset hyB hp0
        (subset_trans (forcingCone_boolean_subset hy) hpq1p)
    have hu := function_value_mem (isForcingIsomorphism_inverse hψ).1 hyp
    have hval : ψ ‘ ((converseGraph ψ) ‘ y) = y :=
      value_converseGraph_value hψ.1 hψ.2.1 (hψ.2.2.1.symm ▸ hyp)
    refine mem_forcingCone_of_subset ((mem_forcingCone_iff _ _ _ _).mp hu).1 hq1 ?_
    refine coneIsomorphism_subset_of_value_subset hψ hu hq1c ?_
    rw [hval]
    exact forcingCone_boolean_subset hy
  refine isForcingIsomorphism_of_inverse (fun x ↦ ψ ‘ x) (fun y ↦ (converseGraph ψ) ‘ y)
    (by definability) hFP hGQ ?_ ?_ ?_
  · intro x hx
    exact converseGraph_value_value hψ.1 hψ.2.1 (hsub x hx)
  · intro y hy
    have hyB := ((mem_forcingCone_iff _ _ _ _).mp hy).1
    have hyp : y ∈ forcingCone (booleanConditions P R) (booleanOrder P R) p0 :=
      mem_forcingCone_of_subset hyB hp0
        (subset_trans (forcingCone_boolean_subset hy) hpq1p)
    exact value_converseGraph_value hψ.1 hψ.2.1 (hψ.2.2.1.symm ▸ hyp)
  · intro x hx y hy
    rw [kpair_mem_restrictedOrder_iff, kpair_mem_restrictedOrder_iff]
    simp only [hx, hy, hFP x hx, hFP y hy, and_true]
    have h := hψ.2.2.2 x (hsub x hx) y (hsub y hy)
    rw [kpair_mem_restrictedOrder_iff, kpair_mem_restrictedOrder_iff] at h
    simp only [hsub x hx, hsub y hy, function_value_mem hψ.1 (hsub x hx),
      function_value_mem hψ.1 (hsub y hy), and_true] at h
    exact h

/-- The support clause survives the restriction of a cone isomorphism to a smaller condition. -/
theorem coneIsomorphism_restrict_coneImage (hp0 : p0 ∈ booleanConditions P R)
    (hq0 : q0 ∈ booleanConditions P R) (hq1 : q1 ∈ booleanConditions P R) (hq1q0 : q1 ⊆ q0)
    {a : V} (ha : IsForcingRegular P R a) (hcone : coneImage P R q0 ψ (a ∩ q0) = a ∩ p0) :
    coneImage P R q1 (coneRestrictMap P R q1 ψ) (a ∩ q1) = a ∩ ψ ‘ q1 := by
  have hq1c : q1 ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q0 :=
    mem_forcingCone_of_subset hq1 hq0 hq1q0
  have hpq1 := function_value_mem hψ.1 hq1c
  have hpq1B := ((mem_forcingCone_iff _ _ _ _).mp hpq1).1
  have hpq1p : ψ ‘ q1 ⊆ p0 := forcingCone_boolean_subset hpq1
  have hres := coneIsomorphism_restrict hψ hp0 hq0 hq1 hq1q0
  have heq : a ∩ q1 = (a ∩ q0) ∩ q1 := by
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨hza, hzq⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr ⟨mem_inter_iff.mpr ⟨hza, hq1q0 z hzq⟩, hzq⟩
    · intro hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp (mem_inter_iff.mp hz).1).1, (mem_inter_iff.mp hz).2⟩
  rcases inter_mem_forcingCone_or_empty ha hq1 with hc1 | hc1
  · -- the intersection with `q₁` is a condition, so the meet formula applies
    have hne : ∃ z : V, z ∈ a ∩ q0 := by
      obtain ⟨z, hz⟩ := booleanConditions_nonempty ((mem_forcingCone_iff _ _ _ _).mp hc1).1
      exact ⟨z, mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp hz).1, hq1q0 z (mem_inter_iff.mp hz).2⟩⟩
    have hc0 : a ∩ q0 ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q0 := by
      rcases inter_mem_forcingCone_or_empty ha hq0 with h | h
      · exact h
      · obtain ⟨z, hz⟩ := hne
        rw [h] at hz
        exact absurd hz not_mem_empty
    have hval0 : ψ ‘ (a ∩ q0) = a ∩ p0 := by rw [← coneImage_value hψ hc0]; exact hcone
    have hc1' : (a ∩ q0) ∩ q1 ∈ forcingCone (booleanConditions P R) (booleanOrder P R) q0 := by
      rw [← heq]
      exact mem_forcingCone_of_subset ((mem_forcingCone_iff _ _ _ _).mp hc1).1 hq0
        (subset_trans (forcingCone_boolean_subset hc1) hq1q0)
    rw [coneImage_value hres hc1, coneRestrictMap_value hc1, heq,
      coneIsomorphism_value_inter hψ hp0 hc0 hq1c hc1', hval0]
    apply mem_ext
    intro z
    constructor
    · intro hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp (mem_inter_iff.mp hz).1).1, (mem_inter_iff.mp hz).2⟩
    · intro hz
      obtain ⟨hza, hzq⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr ⟨mem_inter_iff.mpr ⟨hza, hpq1p z hzq⟩, hzq⟩
  · -- the intersection with `q₁` is empty, and then so is the intersection with `ψ ‘ q₁`
    rw [hc1, coneImage_empty]
    refine mem_ext (fun z ↦ ⟨fun hz ↦ absurd hz not_mem_empty, fun hz ↦ ?_⟩)
    exfalso
    have hwB : a ∩ ψ ‘ q1 ∈ booleanConditions P R :=
      (mem_booleanConditions_iff _ _ _).mpr
        ⟨forcingRegular_inter ha (booleanConditions_regular hpq1B), z, hz⟩
    have hwc : a ∩ ψ ‘ q1 ∈ forcingCone (booleanConditions P R) (booleanOrder P R) p0 :=
      mem_forcingCone_of_subset hwB hp0 (fun w hw ↦ hpq1p w (mem_inter_iff.mp hw).2)
    obtain ⟨u, hu, huv⟩ := isForcingIsomorphism_surjective hψ _ hwc
    have huq1 : u ⊆ q1 := coneIsomorphism_subset_of_value_subset hψ hu hq1c
      (by rw [huv]; exact fun w hw ↦ (mem_inter_iff.mp hw).2)
    have hua : u ⊆ a ∩ q0 := by
      rcases inter_mem_forcingCone_or_empty ha hq0 with hc0 | hc0
      · have hval0 : ψ ‘ (a ∩ q0) = a ∩ p0 := by rw [← coneImage_value hψ hc0]; exact hcone
        refine coneIsomorphism_subset_of_value_subset hψ hu hc0 ?_
        rw [huv, hval0]
        exact fun w hw ↦ mem_inter_iff.mpr
          ⟨(mem_inter_iff.mp hw).1, hpq1p w (mem_inter_iff.mp hw).2⟩
      · have h0 : a ∩ p0 = (∅ : V) := by rw [← hcone, hc0]; exact coneImage_empty _ _ _ _
        exfalso
        have : z ∈ a ∩ p0 := mem_inter_iff.mpr
          ⟨(mem_inter_iff.mp hz).1, hpq1p z (mem_inter_iff.mp hz).2⟩
        rw [h0] at this
        exact not_mem_empty this
    obtain ⟨w, hw⟩ := booleanConditions_nonempty ((mem_forcingCone_iff _ _ _ _).mp hu).1
    have hwa : w ∈ a ∩ q1 := mem_inter_iff.mpr
      ⟨(mem_inter_iff.mp (hua w hw)).1, huq1 w hw⟩
    rw [hc1] at hwa
    exact not_mem_empty hwa

end Cones

namespace ForcingContext

/-! ### The filter clause under inversion and restriction -/

variable {A : ForcingContext V} {p0 q0 q1 ψ : V} {H : A.Model}

/-- The filter clause of the cone construction, transported to the inverse isomorphism. The cone
construction states it from the side of `H`; `ConeOrbitTransfer` asks for it from the side of the
generic. -/
theorem filterTransfer_inverse (hp0 : p0 ∈ booleanConditions A.P A.R)
    (hψ : IsForcingIsomorphism
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q0)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q0))
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p0)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p0)) ψ)
    (hfilter : ∀ c ∈ booleanConditions A.P A.R, c ⊆ q0 →
      (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet)) :
    ∀ b ∈ booleanConditions A.P A.R, b ⊆ p0 →
      (A.check ((converseGraph ψ) ‘ b) ∈ H ↔ A.check b ∈ A.boolGenericSet) := by
  intro b hb hbp
  have hbc : b ∈ forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p0 :=
    mem_forcingCone_of_subset hb hp0 hbp
  have hu := function_value_mem (isForcingIsomorphism_inverse hψ).1 hbc
  have hval : ψ ‘ ((converseGraph ψ) ‘ b) = b :=
    value_converseGraph_value hψ.1 hψ.2.1 (hψ.2.2.1.symm ▸ hbc)
  rw [hfilter _ ((mem_forcingCone_iff _ _ _ _).mp hu).1 (forcingCone_boolean_subset hu), hval]

/-- The restriction of the cone data to a smaller condition of the filter: the image condition is
met by the generic, the restricted map is an isomorphism of the two smaller cones, and the filter
clause holds below the smaller condition. The support clause is
`coneIsomorphism_restrict_coneImage`. -/
theorem coneRestrict_filterTransfer (hp0 : p0 ∈ booleanConditions A.P A.R)
    (hq0 : q0 ∈ booleanConditions A.P A.R)
    (hψ : IsForcingIsomorphism
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q0)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q0))
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p0)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p0)) ψ)
    (hq1 : q1 ∈ booleanConditions A.P A.R) (hq1q0 : q1 ⊆ q0) (hq1H : A.check q1 ∈ H)
    (hfilter : ∀ c ∈ booleanConditions A.P A.R, c ⊆ q0 →
      (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet)) :
    ψ ‘ q1 ∈ booleanConditions A.P A.R ∧ (∃ t ∈ A.G, t ∈ ψ ‘ q1) ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q1)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q1))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) (ψ ‘ q1))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) (ψ ‘ q1)))
        (coneRestrictMap A.P A.R q1 ψ) ∧
      (∀ c ∈ booleanConditions A.P A.R, c ⊆ q1 →
        (A.check c ∈ H ↔ A.check ((coneRestrictMap A.P A.R q1 ψ) ‘ c) ∈ A.boolGenericSet)) := by
  have hq1c : q1 ∈ forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q0 :=
    mem_forcingCone_of_subset hq1 hq0 hq1q0
  have hpq1 := function_value_mem hψ.1 hq1c
  have hpq1B := ((mem_forcingCone_iff _ _ _ _).mp hpq1).1
  refine ⟨hpq1B, ?_, coneIsomorphism_restrict hψ hp0 hq0 hq1 hq1q0, fun c hc hcq ↦ ?_⟩
  · exact ((A.check_mem_boolGenericSet_iff _).mp ((hfilter q1 hq1 hq1q0).mp hq1H)).2
  · rw [coneRestrictMap_value (mem_forcingCone_of_subset hc hq1 hcq)]
    exact hfilter c hc (subset_trans hcq hq1q0)

/-! ### The alignment hypothesis -/

/-- The cone hypothesis with both conditions regular cones of conditions of the base poset. For
every orbit filter `H` over a support of saturated nice names there are a condition `r` of the
generic filter and a condition `r'` of the poset with the check of `coneRegular r'` in `H`, an
isomorphism `ψ` of the cone below `coneRegular r'` onto the cone below `coneRegular r` carrying
`H` to the generic pointwise and fixing the base support values, and an isomorphism `g` of the two
complementary cones fixing the base support values as well.

What is already proved of this, for the Levy collapse:

* `exists_orbit_cone_isomorphism_support` gives all of it except that the condition on the side of
  `H` is a regular cone: it gives some condition `q₀` of `H`, an isomorphism of the cone below
  `q₀` onto the cone below `coneRegular r` for an `r` of the generic, the filter clause, and the
  support clause on the base support algebra.
* `exists_trace_coneRegular_below` gives a condition `r'` of the poset with `coneRegular r' ⊆ q₀`
  and the check of `coneRegular r'` in `H`, and `coneIsomorphism_restrict`,
  `coneIsomorphism_restrict_coneImage` and `coneRestrict_filterTransfer` above carry the
  isomorphism, the filter clause and the support clause down to it.

The open part is that the two can be arranged together. Restricting to `coneRegular r'` replaces
the condition on the side of the generic by the image `ψ ‘ (coneRegular r')`, and that image need
not be a regular cone of a condition of the poset. So the clause asks for a pair of regular cones
matched by the isomorphism.

The complementary isomorphism `g` is asked for with its support clause. Its existence alone is
free once the two conditions of the collapse have the same domain
(`levy_complement_cone_isomorphism_of_domain_eq`, applicable after
`exists_common_domain_extensions`), but that lemma builds `g` from a value-swapping automorphism
of the collapse, which has no reason to fix the base support values, so the support clause on the
complementary cone is asked for here rather than derived. -/
def IsConeAligned (A : ForcingContext V) (Pf : SetTheorySemisentence 2) (s k : V) (p : A.Model) :
    Prop :=
  (∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) σ) →
  ∀ H : A.Model, IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H →
    ∃ r ∈ A.G, ∃ r' ∈ A.P, ∃ ψ : V, ∃ g : V,
      A.check (coneRegular A.P A.R r') ∈ H ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R r'))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r')))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R r))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r))) ψ ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (forcingNegation A.P A.R (coneRegular A.P A.R r)))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (forcingNegation A.P A.R (coneRegular A.P A.R r))))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (forcingNegation A.P A.R (coneRegular A.P A.R r')))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (forcingNegation A.P A.R (coneRegular A.P A.R r')))) g ∧
      (∀ c ∈ booleanConditions A.P A.R, c ⊆ coneRegular A.P A.R r' →
        (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet)) ∧
      (∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
        coneImage A.P A.R (coneRegular A.P A.R r') ψ (a ∩ coneRegular A.P A.R r') =
            a ∩ coneRegular A.P A.R r ∧
          coneImage A.P A.R (forcingNegation A.P A.R (coneRegular A.P A.R r)) g
              (a ∩ forcingNegation A.P A.R (coneRegular A.P A.R r)) =
            a ∩ forcingNegation A.P A.R (coneRegular A.P A.R r'))

/-- The cone hypothesis from the alignment hypothesis. The two conditions are the two regular
cones, the isomorphism of the positive cones is the inverse of the given one, and the isomorphism
of the complementary cones is the given one. -/
theorem coneOrbitTransfer_of_isConeAligned {Pf : SetTheorySemisentence 2} {s k : V} {p : A.Model}
    (h : A.IsConeAligned Pf s k p) : A.ConeOrbitTransfer Pf s k p := by
  intro hE H hH
  obtain ⟨r, hrG, r', hr'P, ψ, g, hq0H, hψ, hg, hfilter, hsupp⟩ := h hE H hH
  have hrP : r ∈ A.P := A.generic.1.1 r hrG
  have hp0 : coneRegular A.P A.R r ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hrP
  have hq0 : coneRegular A.P A.R r' ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hr'P
  refine ⟨coneRegular A.P A.R r, hp0, coneRegular A.P A.R r', hq0, converseGraph ψ, g,
    isForcingIsomorphism_inverse hψ, hg,
    ⟨r, hrG, self_mem_coneRegular A.order hrP⟩, hq0H,
    filterTransfer_inverse hp0 hψ hfilter, fun a ha ↦ ⟨?_, (hsupp a ha).2⟩⟩
  have hareg : IsForcingRegular A.P A.R a :=
    (mem_regularSets_iff _ _ _).mp (supportValuesBase_subset_regularSets A.order _ _ _ a ha)
  exact coneImage_inverse hψ hq0 hareg (hsupp a ha).1

end ForcingContext

/-! ### The Levy export -/

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

omit [IsOrdinal κ] in
/-- The transfer statement of Karagila and Schilhan, Lemma 9.3, for the Levy collapse, from the
alignment hypothesis. -/
theorem levy_orbitTransfer_of_aligned
    (haligned : ∀ s k : V,
      (levyContext κ hG).IsConeAligned groundFormula s k (solovayParam κ hG)) :
    ∀ s k : V, (∀ σ ∈ range s, IsSaturatedNiceName
        (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ) →
      (levyContext κ hG).OrbitTransfer groundFormula s k (solovayParam κ hG) :=
  levy_orbitTransfer_of_cone hG
    (fun s k ↦ ForcingContext.coneOrbitTransfer_of_isConeAligned (haligned s k))

include hAC hU hc hω hκ in
/-- `cor:Solovay` with the alignment hypothesis as its only open assumption. The clauses are those
of `solovay_corollary_of_transfer`. -/
theorem solovay_corollary_of_aligned [Countable V]
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (haligned : ∀ s k : V,
      (levyContext κ hG).IsConeAligned groundFormula s k (solovayParam κ hG)) :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    (SolovayHOD κ hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 ∧
    (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := SolovayHOD κ hG) φ) ∧
    InternalDependentChoice (SolovayHOD κ hG) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → IsLebesgueMeasurable X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → BaireProperty X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → PerfectSetProperty X) ∧
    ¬ InternalChoice (SolovayHOD κ hG) ∧
    hartogsNumber (ω : SolovayHOD κ hG) = solovayCheck hAC hU hc hω hκ hG κ ∧
    IsNonprincipalSetUltrafilter (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) ∧
    IsOrdinalComplete (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) :=
  solovay_corollary_of_cone_transfer hAC hU hc hω hκ hG hVP
    (fun s k ↦ ForcingContext.coneOrbitTransfer_of_isConeAligned (haligned s k))

end

end ZFVP
