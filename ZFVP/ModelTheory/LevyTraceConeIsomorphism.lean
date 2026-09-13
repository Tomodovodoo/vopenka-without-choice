import ZFVP.ModelTheory.LevyConeIsomorphism
import ZFVP.ModelTheory.LevyDeterminedSubalgebra
import ZFVP.ModelTheory.LevyBooleanHomogeneity
import ZFVP.SetTheory.LevyCollapseUpper

/-! Cone isomorphisms of the Levy collapse that leave the part below `ξ` alone.

For a condition `r` of `Coll(ω, <κ)` write `q₀ = levyCut ξ r` for its part on the columns below
`ξ` and `u = levyUpper ξ r` for its part on the columns outside `ξ`. Renaming the coordinates
that `u` leaves free, column by column, identifies the cone of `r` with the cone of `q₀`. The
renaming is the identity on `ω × ξ`, because `u` occupies no row of a column below `ξ`, so the
enumeration of the free rows of such a column is the identity on `ω`. Hence the isomorphism does
not move the part of a condition below `ξ`.

In the Boolean completion this says that the cone below `coneRegular r` is isomorphic to the cone
below `coneRegular (levyCut ξ r)`, and the isomorphism commutes with meets by members of
`levyDeterminedAlgebra κ ξ`: membership in a set determined below `ξ` only depends on the part of
a condition below `ξ`, which the poset isomorphism leaves fixed.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The Mostowski collapse of a transitive set is the identity -/

/-- On a transitive set the membership relation collapses by the identity. -/
theorem mostowskiMap_membershipRelation_of_transitive (D : V) [IsTransitive D] :
    mostowskiMap (membershipRelation D) D = identity D := by
  have hR := membershipRelation_wellFounded D
  have hrange : range (identity D : V) = D := by
    apply mem_ext
    intro x
    rw [mem_range_iff]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨hyD, rfl⟩ := kpair_mem_identity_iff.mp hy
      exact hyD
    · intro hx
      exact ⟨x, kpair_mem_identity_iff.mpr ⟨hx, rfl⟩⟩
  have hcol : IsTransitiveCollapse (membershipRelation D) D D (identity D : V) := by
    refine ⟨inferInstance, identity_mem_function D, hrange, ?_, ?_⟩
    · intro x hx y hy h
      rwa [identity_value hx, identity_value hy] at h
    · intro x hx y hy
      rw [identity_value hx, identity_value hy, pair_mem_membershipRelation]
      exact ⟨fun h ↦ ⟨hx, hy, h⟩, fun h ↦ h.2.2⟩
  rw [mostowskiMap_of_wellFounded hR]
  exact (transitiveCollapse_unique hR hcol).1.symm

/-! ### The renaming attached to the upper part of a condition -/

/-- A condition supported on the columns outside `ξ` leaves every row of every column below `ξ`
free. -/
theorem freeLevyRow_of_above {κ ξ u α : V} (hu : u ∈ levyCollapseAbove κ ξ) (hα : α ∈ ξ) :
    freeLevyRow u α = (ω : V) := by
  apply mem_ext
  intro n
  rw [mem_freeLevyRow]
  refine ⟨fun h ↦ h.1, fun hn ↦ ⟨hn, fun hd ↦ ?_⟩⟩
  obtain ⟨y, hy⟩ := mem_domain_iff.mp hd
  exact coordinate_not_mem_of_above hu hy (kpair_mem_iff.mpr ⟨hn, hα⟩)

/-- Hence the enumeration of its free rows in such a column is the identity of `ω`. -/
theorem levyRowMap_of_above {κ ξ u α : V} (hu : u ∈ levyCollapseAbove κ ξ) (hα : α ∈ ξ) :
    levyRowMap u α = identity (ω : V) := by
  unfold levyRowMap
  rw [freeLevyRow_of_above hu hα]
  exact mostowskiMap_membershipRelation_of_transitive _

/-- All coordinates below `ξ` are free for a condition supported outside `ξ`. -/
theorem prod_omega_subset_freeLevyCoordinates {κ ξ u : V} (hu : u ∈ levyCollapseAbove κ ξ)
    (hξ : ξ ⊆ κ) : ((ω : V) ×ˢ ξ) ⊆ freeLevyCoordinates κ u := by
  intro z hz
  obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hz
  refine (mem_freeLevyCoordinates _ _ _).mpr ⟨kpair_mem_iff.mpr ⟨hn, hξ α hα⟩, fun hd ↦ ?_⟩
  obtain ⟨y, hy⟩ := mem_domain_iff.mp hd
  exact coordinate_not_mem_of_above hu hy hz

/-- The coordinate renaming attached to a condition supported outside `ξ` fixes every coordinate
below `ξ`. -/
theorem levyCoordinateMap_value_below {κ ξ u z : V} (hu : u ∈ levyCollapseAbove κ ξ)
    (hξ : ξ ⊆ κ) (hz : z ∈ (ω : V) ×ˢ ξ) : (levyCoordinateMap κ u) ‘ z = z := by
  obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hz
  rw [levyCoordinateMap_value (prod_omega_subset_freeLevyCoordinates hu hξ _ hz)]
  simp only [levyCoordinateValue, kpair.π₁_kpair, kpair.π₂_kpair,
    levyRowMap_of_above hu hα, identity_value hn]

/-- The inverse renaming fixes every coordinate below `ξ` too. -/
theorem inverse_levyCoordinateMap_value_below {κ ξ u z : V} (hu : u ∈ levyCollapseAbove κ ξ)
    (hξ : ξ ⊆ κ) (hz : z ∈ (ω : V) ×ˢ ξ) :
    (converseGraph (levyCoordinateMap κ u)) ‘ z = z := by
  have huP : u ∈ levyCollapse κ := levyCollapseAbove_subset κ ξ u hu
  have h := converseGraph_value_value (levyCoordinateMap_function huP)
    (levyCoordinateMap_injective huP) (prod_omega_subset_freeLevyCoordinates hu hξ _ hz)
  rwa [levyCoordinateMap_value_below hu hξ hz] at h

/-! ### The cut is not moved -/

/-- Decoding along the renaming of the upper part of `r` does not change the part of a condition
below `ξ`. -/
theorem levyCut_levyConeDecode {κ ξ r p : V} (hr : r ∈ levyCollapse κ) (hξ : ξ ⊆ κ)
    (hp : p ∈ levyCollapse κ) :
    levyCut ξ (levyConeDecode κ (levyUpper ξ r) p) = levyCut ξ p := by
  have hu : levyUpper ξ r ∈ levyCollapseAbove κ ξ := levyUpper_mem_above hr
  have huP : levyUpper ξ r ∈ levyCollapse κ := levyCollapseAbove_subset κ ξ _ hu
  have hpf : IsFunction p := levyCollapse_isFunction hp
  have hrf : IsFunction (p ↾ (freeLevyCoordinates κ (levyUpper ξ r))) :=
    IsFunction.ofSubset p _ (fun z hz ↦ (mem_restrict_iff.mp hz).1)
  apply mem_ext
  intro z
  unfold levyConeDecode
  constructor
  · intro hz
    obtain ⟨hzp, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
    obtain ⟨w, hw, hxw⟩ := (pair_mem_permutedGraph _ _ x y).mp hzp
    have hwD : w ∈ freeLevyCoordinates κ (levyUpper ξ r) := (kpair_mem_restrict_iff.mp hw).2
    have hcol := levyCoordinateMap_preserves_column hwD
    obtain ⟨n, hn, α, hα, hxe⟩ := mem_prod_iff.mp hx
    obtain ⟨m, hm, β, hβ, hwe⟩ := mem_prod_iff.mp ((mem_freeLevyCoordinates _ _ _).mp hwD).1
    have hαβ : α = β := by
      rw [← hxw, hxe, hwe] at hcol
      simpa only [kpair.π₂_kpair] using hcol
    have hwξ : w ∈ (ω : V) ×ˢ ξ := by
      rw [hwe]
      exact kpair_mem_iff.mpr ⟨hm, hαβ ▸ hα⟩
    have hxw' : x = w := by
      rw [hxw, levyCoordinateMap_value_below hu hξ hwξ]
    subst hxw'
    exact kpair_mem_restrict_iff.mpr ⟨(mem_restrict_iff.mp hw).1, hx⟩
  · intro hz
    obtain ⟨hzp, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
    have hxD : x ∈ freeLevyCoordinates κ (levyUpper ξ r) :=
      prod_omega_subset_freeLevyCoordinates hu hξ _ hx
    refine kpair_mem_restrict_iff.mpr ⟨?_, hx⟩
    exact (pair_mem_permutedGraph _ _ x y).mpr
      ⟨x, kpair_mem_restrict_iff.mpr ⟨hzp, hxD⟩,
        (levyCoordinateMap_value_below hu hξ hx).symm⟩

/-! ### The cone isomorphism -/

/-- The cone of a condition `r` of `Coll(ω, <κ)` is forcing isomorphic to the cone of its part
below `ξ`, by an isomorphism that leaves the part below `ξ` of every condition fixed. -/
theorem levyCollapse_cone_isomorphic_cut {κ ξ r : V} [IsOrdinal κ] (hr : r ∈ levyCollapse κ)
    (hξ : ξ ⊆ κ) :
    ∃ F, IsForcingIsomorphism (levyCollapseCone κ r)
      (restrictedOrder (levyOrder κ) (levyCollapseCone κ r))
      (levyCollapseCone κ (levyCut ξ r))
      (restrictedOrder (levyOrder κ) (levyCollapseCone κ (levyCut ξ r))) F ∧
      ∀ p, p ∈ levyCollapseCone κ r → levyCut ξ (F ‘ p) = levyCut ξ p := by
  have hu : levyUpper ξ r ∈ levyCollapseAbove κ ξ := levyUpper_mem_above hr
  have huP : levyUpper ξ r ∈ levyCollapse κ := levyCollapseAbove_subset κ ξ _ hu
  have hq0 : levyCut ξ r ∈ levyCollapse κ := levyCollapse_subset hr (levyCut_subset ξ r)
  let F : V → V := fun p ↦ levyConeDecode κ (levyUpper ξ r) p
  let G : V → V := fun p ↦ levyConeEncode κ (levyUpper ξ r) p
  have hF : ℒₛₑₜ-function₁ F := by
    unfold F levyConeDecode
    definability
  -- the encoded condition extends the cut of `r`
  have hFP : ∀ p ∈ levyCollapseCone κ r, F p ∈ levyCollapseCone κ (levyCut ξ r) := by
    intro p hp
    obtain ⟨hpP, hrp⟩ := (mem_levyCollapseCone _ _ _).mp hp
    have hpf : IsFunction p := levyCollapse_isFunction hpP
    have hrf : IsFunction (p ↾ (freeLevyCoordinates κ (levyUpper ξ r))) :=
      IsFunction.ofSubset p _ (fun z hz ↦ (mem_restrict_iff.mp hz).1)
    refine (mem_levyCollapseCone _ _ _).mpr ⟨levyConeDecode_condition huP hpP, fun z hz ↦ ?_⟩
    obtain ⟨hzr, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
    have hxD : x ∈ freeLevyCoordinates κ (levyUpper ξ r) :=
      prod_omega_subset_freeLevyCoordinates hu hξ _ hx
    exact (pair_mem_permutedGraph _ _ x y).mpr
      ⟨x, kpair_mem_restrict_iff.mpr ⟨hrp _ hzr, hxD⟩,
        (levyCoordinateMap_value_below hu hξ hx).symm⟩
  -- the decoded condition extends `r`
  have hGQ : ∀ p ∈ levyCollapseCone κ (levyCut ξ r), G p ∈ levyCollapseCone κ r := by
    intro p hp
    obtain ⟨hpP, hqp⟩ := (mem_levyCollapseCone _ _ _).mp hp
    have hpf : IsFunction p := levyCollapse_isFunction hpP
    refine (mem_levyCollapseCone _ _ _).mpr ⟨levyConeEncode_condition huP hpP, fun z hz ↦ ?_⟩
    rw [← levyCut_union_levyUpper ξ r] at hz
    rcases mem_union_iff.mp hz with hz | hz
    · obtain ⟨hzr, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
      refine mem_union_iff.mpr (Or.inr ((pair_mem_permutedGraph _ _ x y).mpr ⟨x, ?_, ?_⟩))
      · exact hqp _ (kpair_mem_restrict_iff.mpr ⟨hzr, hx⟩)
      · exact (inverse_levyCoordinateMap_value_below hu hξ hx).symm
    · exact mem_union_iff.mpr (Or.inl hz)
  have hGF : ∀ p ∈ levyCollapseCone κ r, G (F p) = p := by
    intro p hp
    obtain ⟨hpP, hrp⟩ := (mem_levyCollapseCone _ _ _).mp hp
    exact levyConeEncode_decode huP hpP (subset_trans (levyUpper_subset ξ r) hrp)
  have hFG : ∀ p ∈ levyCollapseCone κ (levyCut ξ r), F (G p) = p := by
    intro p hp
    exact levyConeDecode_encode huP ((mem_levyCollapseCone _ _ _).mp hp).1
  have hiso := reverseInclusion_isomorphism_of_inverse F G hF hFP hGQ hGF hFG
    (fun _ _ _ _ h ↦ levyConeDecode_mono h) (fun _ _ _ _ h ↦ levyConeEncode_mono h)
  rw [← restrictedOrder_levyOrder_cone κ r, ← restrictedOrder_levyOrder_cone κ (levyCut ξ r)]
    at hiso
  refine ⟨definableGraph (levyCollapseCone κ r) F hF, hiso, fun p hp ↦ ?_⟩
  rw [value_definableGraph _ _ _ hp]
  exact levyCut_levyConeDecode hr hξ ((mem_levyCollapseCone _ _ _).mp hp).1

/-! ### Passing to the Boolean completion -/

/-- Cutting a condition of the Boolean cone of `p` down to the cone of conditions gives a
condition of the completion of that cone. -/
theorem inter_forcingCone_mem_booleanConditions {P R p b : V} (hR : IsForcingPreorder P R)
    (hp : p ∈ P) (hb : b ∈ booleanCone P R p) :
    b ∩ forcingCone P R p ∈
      booleanConditions (forcingCone P R p) (restrictedOrder R (forcingCone P R p)) := by
  obtain ⟨hbB, hbc⟩ := (mem_booleanCone_iff _ _ _ _).mp hb
  obtain ⟨hbreg, q, hq⟩ := (mem_booleanConditions_iff P R b).mp hbB
  refine (mem_booleanConditions_iff _ _ _).mpr ⟨inter_forcingCone_regular hR hp hbreg, ?_⟩
  obtain ⟨s, hs, hsq⟩ := exists_forcingCone_below (hbc q hq) (hbreg.1 q hq)
    (hR.2.1 q (hbreg.1 q hq))
  exact ⟨s, mem_inter_iff.mpr ⟨hbreg.2.1 q hq s (forcingCone_subset P R p s hs) hsq, hs⟩⟩

/-- Closing a condition of the completion of the cone gives a condition of the Boolean cone. -/
theorem forcingClosure_mem_booleanCone {P R p A : V} (hR : IsForcingPreorder P R) (hp : p ∈ P)
    (hA : A ∈ booleanConditions (forcingCone P R p) (restrictedOrder R (forcingCone P R p))) :
    forcingClosure P R A ∈ booleanCone P R p := by
  obtain ⟨hAreg, a, ha⟩ := (mem_booleanConditions_iff _ _ A).mp hA
  refine (mem_booleanCone_iff _ _ _ _).mpr ⟨(mem_booleanConditions_iff P R _).mpr
    ⟨forcingClosure_regular hR (subset_trans hAreg.1 (forcingCone_subset P R p)),
      a, coneRegularSet_subset_forcingClosure hR hp hAreg a ha⟩, ?_⟩
  exact forcingClosure_mono hAreg.1

/-- Closure commutes with meeting a regular set: this is the statement that intersecting with
the cone of conditions is an isomorphism of Boolean algebras. -/
theorem forcingClosure_inter_regular {P R p C d : V} (hR : IsForcingPreorder P R) (hp : p ∈ P)
    (hC : IsForcingRegular (forcingCone P R p) (restrictedOrder R (forcingCone P R p)) C)
    (hd : IsForcingRegular P R d) :
    forcingClosure P R (C ∩ d) = forcingClosure P R C ∩ d := by
  have hbreg : IsForcingRegular P R (forcingClosure P R C) :=
    forcingClosure_regular hR (subset_trans hC.1 (forcingCone_subset P R p))
  have hbc : forcingClosure P R C ⊆ coneRegular P R p := forcingClosure_mono hC.1
  have hCb : forcingClosure P R C ∩ forcingCone P R p = C := forcingClosure_inter_eq hR hp hC
  have hCb' : ∀ z : V, z ∈ C ↔ z ∈ forcingClosure P R C ∩ forcingCone P R p := by
    intro z
    rw [hCb]
  have h1 : (forcingClosure P R C ∩ d) ∩ forcingCone P R p = C ∩ d := by
    apply mem_ext
    intro z
    simp only [hCb' z, mem_inter_iff]
    tauto
  rw [← h1, forcingClosure_inter_forcingCone hR (forcingRegular_inter hbreg hd)
    (subset_trans (fun z hz ↦ (mem_inter_iff.mp hz).1) hbc)]

/-- The Boolean form: the cone of the completion of `Coll(ω, <κ)` below the regular cone of `r`
is forcing isomorphic to the cone below the regular cone of `levyCut ξ r`, by an isomorphism
that commutes with meets by sets determined below `ξ`. -/
theorem levy_cone_isomorphic_traceCone {κ ξ r : V} [IsOrdinal κ] (hr : r ∈ levyCollapse κ)
    (hξ : ξ ⊆ κ) :
    ∃ G, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) r))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) r)))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r)))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r)))) G ∧
      ∀ d, d ∈ levyDeterminedAlgebra κ ξ → ∀ x, x ∈ forcingCone (booleanConditions (levyCollapse κ)
        (levyOrder κ)) (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) r) → x ∩ d ≠ (∅ : V) →
        G ‘ (x ∩ d) = (G ‘ x) ∩ d := by
  classical
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hq0 : levyCut ξ r ∈ levyCollapse κ := levyCollapse_subset hr (levyCut_subset ξ r)
  rw [← booleanCone_eq_forcingCone hR hr, ← booleanCone_eq_forcingCone hR hq0]
  obtain ⟨f, hf, hcut⟩ := levyCollapse_cone_isomorphic_cut hr hξ
  have hfc : IsForcingIsomorphism
      (forcingCone (levyCollapse κ) (levyOrder κ) r)
      (restrictedOrder (levyOrder κ) (forcingCone (levyCollapse κ) (levyOrder κ) r))
      (forcingCone (levyCollapse κ) (levyOrder κ) (levyCut ξ r))
      (restrictedOrder (levyOrder κ)
        (forcingCone (levyCollapse κ) (levyOrder κ) (levyCut ξ r))) f := by
    rw [forcingCone_levy hr, forcingCone_levy hq0]
    exact hf
  have hcut' : ∀ p ∈ forcingCone (levyCollapse κ) (levyOrder κ) r,
      levyCut ξ (f ‘ p) = levyCut ξ p := by
    intro p hp
    exact hcut p (forcingCone_levy hr ▸ hp)
  have hfi := isForcingIsomorphism_inverse hfc
  let H : V → V := fun b ↦ forcingClosure (levyCollapse κ) (levyOrder κ)
    (imageAction f (b ∩ forcingCone (levyCollapse κ) (levyOrder κ) r))
  let H' : V → V := fun c ↦ forcingClosure (levyCollapse κ) (levyOrder κ)
    (imageAction (converseGraph f)
      (c ∩ forcingCone (levyCollapse κ) (levyOrder κ) (levyCut ξ r)))
  have hHdef : ℒₛₑₜ-function₁ H := by
    unfold H
    definability
  have hH'def : ℒₛₑₜ-function₁ H' := by
    unfold H'
    definability
  have hHP : ∀ b ∈ booleanCone (levyCollapse κ) (levyOrder κ) r,
      H b ∈ booleanCone (levyCollapse κ) (levyOrder κ) (levyCut ξ r) := fun b hb ↦
    forcingClosure_mem_booleanCone hR hq0
      (imageAction_mem_booleanConditions_of_isomorphism hfc
        (inter_forcingCone_mem_booleanConditions hR hr hb))
  have hH'Q : ∀ c ∈ booleanCone (levyCollapse κ) (levyOrder κ) (levyCut ξ r),
      H' c ∈ booleanCone (levyCollapse κ) (levyOrder κ) r := fun c hc ↦
    forcingClosure_mem_booleanCone hR hr
      (imageAction_mem_booleanConditions_of_isomorphism hfi
        (inter_forcingCone_mem_booleanConditions hR hq0 hc))
  have hH'H : ∀ b ∈ booleanCone (levyCollapse κ) (levyOrder κ) r, H' (H b) = b := by
    intro b hb
    obtain ⟨hbB, hbc⟩ := (mem_booleanCone_iff _ _ _ _).mp hb
    have hbreg := ((mem_booleanConditions_iff _ _ b).mp hbB).1
    have hA := inter_forcingCone_mem_booleanConditions hR hr hb
    have hC := imageAction_mem_booleanConditions_of_isomorphism hfc hA
    dsimp only [H, H']
    rw [forcingClosure_inter_eq hR hq0 ((mem_booleanConditions_iff _ _ _).mp hC).1,
      imageAction_inverse_image hfc (fun z hz ↦ (mem_inter_iff.mp hz).2),
      forcingClosure_inter_forcingCone hR hbreg hbc]
  have hHH' : ∀ c ∈ booleanCone (levyCollapse κ) (levyOrder κ) (levyCut ξ r), H (H' c) = c := by
    intro c hc
    obtain ⟨hcB, hcc⟩ := (mem_booleanCone_iff _ _ _ _).mp hc
    have hcreg := ((mem_booleanConditions_iff _ _ c).mp hcB).1
    have hA := inter_forcingCone_mem_booleanConditions hR hq0 hc
    have hC := imageAction_mem_booleanConditions_of_isomorphism hfi hA
    dsimp only [H, H']
    rw [forcingClosure_inter_eq hR hr ((mem_booleanConditions_iff _ _ _).mp hC).1,
      imageAction_image_inverse hfc (fun z hz ↦ (mem_inter_iff.mp hz).2),
      forcingClosure_inter_forcingCone hR hcreg hcc]
  have hmonoH : ∀ b c : V, b ⊆ c → H b ⊆ H c := by
    intro b c hbc
    apply forcingClosure_mono
    intro z hz
    obtain ⟨a, ha, rfl⟩ := (mem_imageAction_iff _ _ _).mp hz
    exact (mem_imageAction_iff _ _ _).mpr ⟨a, mem_inter_iff.mpr
      ⟨hbc a (mem_inter_iff.mp ha).1, (mem_inter_iff.mp ha).2⟩, rfl⟩
  have hmonoH' : ∀ b c : V, b ⊆ c → H' b ⊆ H' c := by
    intro b c hbc
    apply forcingClosure_mono
    intro z hz
    obtain ⟨a, ha, rfl⟩ := (mem_imageAction_iff _ _ _).mp hz
    exact (mem_imageAction_iff _ _ _).mpr ⟨a, mem_inter_iff.mpr
      ⟨hbc a (mem_inter_iff.mp ha).1, (mem_inter_iff.mp ha).2⟩, rfl⟩
  have hord : ∀ b ∈ booleanCone (levyCollapse κ) (levyOrder κ) r,
      ∀ c ∈ booleanCone (levyCollapse κ) (levyOrder κ) r,
      ⟨b, c⟩ₖ ∈ restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (booleanCone (levyCollapse κ) (levyOrder κ) r) ↔
      ⟨H b, H c⟩ₖ ∈ restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (booleanCone (levyCollapse κ) (levyOrder κ) (levyCut ξ r)) := by
    intro b hb c hc
    have hbB := ((mem_booleanCone_iff _ _ _ _).mp hb).1
    have hcB := ((mem_booleanCone_iff _ _ _ _).mp hc).1
    have hHbB := ((mem_booleanCone_iff _ _ _ _).mp (hHP b hb)).1
    have hHcB := ((mem_booleanCone_iff _ _ _ _).mp (hHP c hc)).1
    rw [kpair_mem_restrictedOrder_iff, kpair_mem_restrictedOrder_iff,
      kpair_mem_booleanOrder_iff, kpair_mem_booleanOrder_iff]
    simp only [hb, hc, hbB, hcB, hHP b hb, hHP c hc, hHbB, hHcB, true_and, and_true]
    refine ⟨fun h ↦ hmonoH b c h, fun h ↦ ?_⟩
    have h1 := hmonoH' _ _ h
    rwa [hH'H b hb, hH'H c hc] at h1
  refine ⟨definableGraph (booleanCone (levyCollapse κ) (levyOrder κ) r) H hHdef,
    isForcingIsomorphism_of_inverse H H' hHdef hHP hH'Q hH'H hHH' hord, ?_⟩
  intro d hd x hx hne
  obtain ⟨hdreg, hdet⟩ := (mem_levyDeterminedAlgebra_iff _ _ _).mp hd
  obtain ⟨hxB, hxc⟩ := (mem_booleanCone_iff _ _ _ _).mp hx
  have hxreg := ((mem_booleanConditions_iff _ _ x).mp hxB).1
  have hxd : x ∩ d ∈ booleanCone (levyCollapse κ) (levyOrder κ) r := by
    refine (mem_booleanCone_iff _ _ _ _).mpr ⟨(mem_booleanConditions_iff _ _ _).mpr
      ⟨forcingRegular_inter hxreg hdreg, ?_⟩, fun z hz ↦ hxc z (mem_inter_iff.mp hz).1⟩
    by_contra hno
    exact hne (mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hno,
      fun hz ↦ absurd hz not_mem_empty⟩))
  rw [value_definableGraph _ _ _ hxd, value_definableGraph _ _ _ hx]
  have hAcone : (x ∩ d) ∩ forcingCone (levyCollapse κ) (levyOrder κ) r =
      (x ∩ forcingCone (levyCollapse κ) (levyOrder κ) r) ∩ d := by
    apply mem_ext
    intro z
    simp only [mem_inter_iff]
    tauto
  have hiff : ∀ p ∈ forcingCone (levyCollapse κ) (levyOrder κ) r, (f ‘ p ∈ d ↔ p ∈ d) := by
    intro p hp
    have hpP : p ∈ levyCollapse κ := forcingCone_subset _ _ _ p hp
    have hfp : f ‘ p ∈ levyCollapse κ :=
      forcingCone_subset _ _ _ _ (function_value_mem hfc.1 hp)
    rw [hdet _ hfp, hcut' p hp, ← hdet _ hpP]
  have himg : imageAction f ((x ∩ forcingCone (levyCollapse κ) (levyOrder κ) r) ∩ d) =
      imageAction f (x ∩ forcingCone (levyCollapse κ) (levyOrder κ) r) ∩ d := by
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨a, ha, rfl⟩ := (mem_imageAction_iff _ _ _).mp hz
      obtain ⟨haA, had⟩ := mem_inter_iff.mp ha
      exact mem_inter_iff.mpr ⟨(mem_imageAction_iff _ _ _).mpr ⟨a, haA, rfl⟩,
        (hiff a (mem_inter_iff.mp haA).2).mpr had⟩
    · intro hz
      obtain ⟨hz1, hz2⟩ := mem_inter_iff.mp hz
      obtain ⟨a, haA, rfl⟩ := (mem_imageAction_iff _ _ _).mp hz1
      exact (mem_imageAction_iff _ _ _).mpr
        ⟨a, mem_inter_iff.mpr ⟨haA, (hiff a (mem_inter_iff.mp haA).2).mp hz2⟩, rfl⟩
  have hC := imageAction_mem_booleanConditions_of_isomorphism hfc
    (inter_forcingCone_mem_booleanConditions hR hr hx)
  dsimp only [H]
  rw [hAcone, himg, forcingClosure_inter_regular hR hq0
    ((mem_booleanConditions_iff _ _ _).mp hC).1 hdreg]

end ZFVP
