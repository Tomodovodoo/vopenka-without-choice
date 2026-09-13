import ZFVP.ModelTheory.LevyTraceConeIsomorphism
import ZFVP.ModelTheory.LevyRelativeConeSkeleton

/-! Relative homogeneity of the Boolean completion of the Levy collapse over the algebra of sets
determined below `ξ`.

Two elements of the completion with the same trace over `levyDeterminedAlgebra κ ξ` have
isomorphic cones, by an isomorphism commuting with meets by every determined set.

The absorption step `levy_cone_isomorphic_determined` says that a nonzero `x` below a determined
`d` that contains a condition cone whose trace is exactly `d` has its cone isomorphic to the cone
of `d`. The two embeddings needed for the Schroeder-Bernstein argument of
ZFVP/ModelTheory/BooleanConeCantorBernstein.lean are the identity of the cone of `x`, which lands
in the cone of `d` since `x ⊆ d`, and the inverse of the isomorphism of
ZFVP/ModelTheory/LevyTraceConeIsomorphism.lean, which sends the cone of `d` onto the cone of
`coneRegular r ⊆ x`.

The main theorem `levy_relative_cone_isomorphism_of_levyTrace_eq` checks the density hypothesis of
`levy_relative_cone_isomorphic_of_dense`: below a nonzero determined `d'` the two elements have
condition cones with a common cut, the cone of that cut is a determined piece `d ⊆ d'`, and
absorption identifies the cone of `u ∩ d` and the cone of `v ∩ d` with the cone of `d`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Meeting a regular set inside a cone -/

/-- A nonzero meet of a member of the cone of `x` with a regular set is again in the cone. -/
theorem inter_mem_cone_of_ne_empty {P R x z e : V} (hx : x ∈ booleanConditions P R)
    (hz : z ∈ forcingCone (booleanConditions P R) (booleanOrder P R) x)
    (he : IsForcingRegular P R e) (hne : z ∩ e ≠ (∅ : V)) :
    z ∩ e ∈ forcingCone (booleanConditions P R) (booleanOrder P R) x := by
  obtain ⟨hzB, hzx⟩ := (mem_forcingCone_booleanOrder_iff hx).mp hz
  exact (mem_forcingCone_booleanOrder_iff hx).mpr
    ⟨(mem_booleanConditions_iff _ _ _).mpr
      ⟨forcingRegular_inter (booleanConditions_regular hzB) he,
        glue_exists_mem_of_ne_empty hne⟩,
      fun w hw ↦ hzx w (mem_inter_iff.mp hw).1⟩

/-! ### Absorption -/

/-- A nonzero `x` below a determined `d` which contains the cone of a condition whose cut has
cone exactly `d` has its cone isomorphic to the cone of `d`, by an isomorphism commuting with
meets by sets determined below `ξ`. -/
theorem levy_cone_isomorphic_determined {κ ξ x d r : V} [IsOrdinal κ] (hξ : ξ ⊆ κ)
    (hd : d ∈ levyDeterminedAlgebra κ ξ)
    (hx : x ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) (hxd : x ⊆ d)
    (hr : r ∈ levyCollapse κ) (hrx : coneRegular (levyCollapse κ) (levyOrder κ) r ⊆ x)
    (hrd : coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r) = d) :
    ∃ h, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) x)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) x))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) d)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) d)) h ∧
      ∀ e, e ∈ levyDeterminedAlgebra κ ξ → ∀ z, z ∈ forcingCone (booleanConditions (levyCollapse κ)
        (levyOrder κ)) (booleanOrder (levyCollapse κ) (levyOrder κ)) x → z ∩ e ≠ (∅ : V) →
        h ‘ (z ∩ e) = (h ‘ z) ∩ e := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hdreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) d :=
    ((mem_levyDeterminedAlgebra_iff _ _ _).mp hd).1
  have hdB : d ∈ booleanConditions (levyCollapse κ) (levyOrder κ) := by
    obtain ⟨-, p, hp⟩ := (mem_booleanConditions_iff _ _ _).mp hx
    exact (mem_booleanConditions_iff _ _ _).mpr ⟨hdreg, p, hxd p hp⟩
  have hcrB : coneRegular (levyCollapse κ) (levyOrder κ) r ∈
      booleanConditions (levyCollapse κ) (levyOrder κ) := coneRegular_mem_booleanConditions hR hr
  -- the identity of the cone of `x`, an isomorphism onto the cone of `b₀ = x`
  have hid : IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) x)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) x))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) x)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) x))
      (identity (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) x)) :=
    forcingAutomorphism_identity _ _
  have hidequi : ∀ e, e ∈ levyDeterminedAlgebra κ ξ → ∀ z,
      z ∈ forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) x → z ∩ e ≠ (∅ : V) →
      (identity (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) x)) ‘ (z ∩ e) =
      ((identity (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) x)) ‘ z) ∩ e := by
    intro e he z hz hze
    rw [identity_value hz, identity_value
      (inter_mem_cone_of_ne_empty hx hz ((mem_levyDeterminedAlgebra_iff _ _ _).mp he).1 hze)]
  -- the inverse of the trace cone isomorphism, from the cone of `d` onto the cone of `r`
  obtain ⟨G, hG, hGequi⟩ := levy_cone_isomorphic_traceCone (κ := κ) (ξ := ξ) hr hξ
  rw [hrd] at hG
  have hGinv := isForcingIsomorphism_inverse hG
  have hGinvequi : ∀ e, e ∈ levyDeterminedAlgebra κ ξ → ∀ y,
      y ∈ forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) d → y ∩ e ≠ (∅ : V) →
      (converseGraph G) ‘ (y ∩ e) = ((converseGraph G) ‘ y) ∩ e := by
    intro e he y hy hye
    refine sb_inverse_equivariant hR hcrB hdB hG
      ((mem_levyDeterminedAlgebra_iff _ _ _).mp he).1
      (fun w hw hwn ↦ hGequi e he w hw hwn)
      (fun w hw hwn ↦ hGequi _
        ((levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.1 e he) w hw hwn) ?_ hye
    exact hy
  exact exists_coneIsomorphism_of_mutual_equivariant hR hx hdB hcrB hrx hx hxd hid hGinv
    (fun e he ↦ ((mem_levyDeterminedAlgebra_iff _ _ _).mp he).1)
    (fun e he ↦ (levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.1 e he)
    hidequi hGinvequi

/-! ### The relative isomorphism -/

set_option maxHeartbeats 1000000 in
/-- Two nonzero elements of the Boolean completion of `Coll(ω, <κ)` with the same trace over
`levyDeterminedAlgebra κ ξ` have isomorphic cones, by an isomorphism commuting with meets by
every set determined below `ξ`. -/
theorem levy_relative_cone_isomorphism_of_levyTrace_eq {κ ξ u v : V} [IsOrdinal κ]
    (hAC : InternalChoice V) (hξ : ξ ⊆ κ)
    (hu : u ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hv : v ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (htr : levyTrace κ ξ u = levyTrace κ ξ v) :
    ∃ H, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) u)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) u))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) v)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) v)) H ∧
      ∀ e, e ∈ levyDeterminedAlgebra κ ξ → ∀ z, z ∈ forcingCone
        (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) u → z ∩ e ≠ (∅ : V) →
        H ‘ (z ∩ e) = (H ‘ z) ∩ e := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hureg : IsForcingRegular (levyCollapse κ) (levyOrder κ) u := booleanConditions_regular hu
  have hvreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) v := booleanConditions_regular hv
  refine levy_relative_cone_isomorphic_of_dense hAC hξ hu hv htr ?_
  intro d' hd' hd'sub hd'ne
  have hd'reg : IsForcingRegular (levyCollapse κ) (levyOrder κ) d' :=
    ((mem_levyDeterminedAlgebra_iff _ _ _).mp hd').1
  have hd'v : d' ⊆ levyTrace κ ξ v := by rw [← htr]; exact hd'sub
  -- the two meets with `d'` are nonzero and have trace `d'`
  obtain ⟨xu, hxu⟩ := levyTrace_of_nonempty_inter_determined hd' hureg
    (glue_exists_mem_of_ne_empty hd'ne) hd'sub
  obtain ⟨xv, hxv⟩ := levyTrace_of_nonempty_inter_determined hd' hvreg
    (glue_exists_mem_of_ne_empty hd'ne) hd'v
  have hud' : u ∩ d' ∈ booleanConditions (levyCollapse κ) (levyOrder κ) :=
    (mem_booleanConditions_iff _ _ _).mpr ⟨forcingRegular_inter hureg hd'reg,
      xu, mem_inter_iff.mpr ⟨(mem_inter_iff.mp hxu).2, (mem_inter_iff.mp hxu).1⟩⟩
  have hvd' : v ∩ d' ∈ booleanConditions (levyCollapse κ) (levyOrder κ) :=
    (mem_booleanConditions_iff _ _ _).mpr ⟨forcingRegular_inter hvreg hd'reg,
      xv, mem_inter_iff.mpr ⟨(mem_inter_iff.mp hxv).2, (mem_inter_iff.mp hxv).1⟩⟩
  have htru : levyTrace κ ξ (u ∩ d') = d' := by
    rw [levyTrace_inter_determined hξ hureg hd', SetTheory.inter_comm,
      glue_inter_eq_left hd'sub]
  have htrv : levyTrace κ ξ (v ∩ d') = d' := by
    rw [levyTrace_inter_determined hξ hvreg hd', ← htr, SetTheory.inter_comm,
      glue_inter_eq_left hd'sub]
  -- a common cut
  obtain ⟨r, r', hr, hr', hcu, hcv, hcut⟩ :=
    levy_exists_common_cut hξ hud' hvd' (htru.trans htrv.symm)
  have hcutP : levyCut ξ r ∈ levyCollapse κ := levyCollapse_subset hr (levyCut_subset ξ r)
  have hcutP' : levyCut ξ r' ∈ levyCollapse κ := levyCollapse_subset hr' (levyCut_subset ξ r')
  set d : V := coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r) with hddef
  have hdalg : d ∈ levyDeterminedAlgebra κ ξ :=
    coneRegular_levyCut_mem_levyDeterminedAlgebra hξ hr
  have hcutd : levyCut ξ r ∈ d := by
    rw [hddef]
    exact self_mem_coneRegular hR hcutP
  have hdne : d ≠ (∅ : V) := by
    intro hde
    rw [hde] at hcutd
    exact not_mem_empty hcutd
  have hdreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) d :=
    ((mem_levyDeterminedAlgebra_iff _ _ _).mp hdalg).1
  have hrd : coneRegular (levyCollapse κ) (levyOrder κ) r ⊆ d :=
    coneRegular_mono hR hcutP hr
      ((pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr, hcutP, levyCut_subset ξ r⟩)
  have hr'd : coneRegular (levyCollapse κ) (levyOrder κ) r' ⊆ d := by
    rw [hddef, hcut]
    exact coneRegular_mono hR hcutP' hr'
      ((pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr', hcutP', levyCut_subset ξ r'⟩)
  have hdd' : d ⊆ d' := by
    have h1 : levyTrace κ ξ (coneRegular (levyCollapse κ) (levyOrder κ) r) = d :=
      levyTrace_coneRegular hξ hr
    rw [← h1, ← htru]
    exact levyTrace_mono hξ (fun z hz ↦ hureg.1 z (mem_inter_iff.mp hz).1) hcu
  -- the meets with `d`, with their condition cones
  have hru : r ∈ u ∩ d :=
    mem_inter_iff.mpr ⟨(mem_inter_iff.mp (hcu r (self_mem_coneRegular hR hr))).1,
      hrd r (self_mem_coneRegular hR hr)⟩
  have hr'v : r' ∈ v ∩ d :=
    mem_inter_iff.mpr ⟨(mem_inter_iff.mp (hcv r' (self_mem_coneRegular hR hr'))).1,
      hr'd r' (self_mem_coneRegular hR hr')⟩
  have hudB : u ∩ d ∈ booleanConditions (levyCollapse κ) (levyOrder κ) :=
    (mem_booleanConditions_iff _ _ _).mpr ⟨forcingRegular_inter hureg hdreg, r, hru⟩
  have hvdB : v ∩ d ∈ booleanConditions (levyCollapse κ) (levyOrder κ) :=
    (mem_booleanConditions_iff _ _ _).mpr ⟨forcingRegular_inter hvreg hdreg, r', hr'v⟩
  have hcud : coneRegular (levyCollapse κ) (levyOrder κ) r ⊆ u ∩ d := fun z hz ↦
    mem_inter_iff.mpr ⟨(mem_inter_iff.mp (hcu z hz)).1, hrd z hz⟩
  have hcvd : coneRegular (levyCollapse κ) (levyOrder κ) r' ⊆ v ∩ d := fun z hz ↦
    mem_inter_iff.mpr ⟨(mem_inter_iff.mp (hcv z hz)).1, hr'd z hz⟩
  -- absorption on both sides
  obtain ⟨h₁, hiso₁, hequi₁⟩ := levy_cone_isomorphic_determined hξ hdalg hudB
    (fun z hz ↦ (mem_inter_iff.mp hz).2) hr hcud hddef.symm
  obtain ⟨h₂, hiso₂, hequi₂⟩ := levy_cone_isomorphic_determined hξ hdalg hvdB
    (fun z hz ↦ (mem_inter_iff.mp hz).2) hr' hcvd (by rw [hddef, hcut])
  have hinv₂ := isForcingIsomorphism_inverse hiso₂
  have hinv₂equi : ∀ e, e ∈ levyDeterminedAlgebra κ ξ → ∀ y,
      y ∈ forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) d → y ∩ e ≠ (∅ : V) →
      (converseGraph h₂) ‘ (y ∩ e) = ((converseGraph h₂) ‘ y) ∩ e := by
    intro e he y hy hye
    have hdB : d ∈ booleanConditions (levyCollapse κ) (levyOrder κ) :=
      (mem_booleanConditions_iff _ _ _).mpr
        ⟨hdreg, levyCut ξ r, hcutd⟩
    exact sb_inverse_equivariant hR hvdB hdB hiso₂
      ((mem_levyDeterminedAlgebra_iff _ _ _).mp he).1
      (fun w hw hwn ↦ hequi₂ e he w hw hwn)
      (fun w hw hwn ↦ hequi₂ _
        ((levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.1 e he) w hw hwn) hy hye
  refine ⟨d, hdalg, hdd', hdne,
    compose h₁ (converseGraph h₂), isForcingIsomorphism_compose hiso₁ hinv₂, ?_⟩
  intro e he z hz hze
  have hereg : IsForcingRegular (levyCollapse κ) (levyOrder κ) e :=
    ((mem_levyDeterminedAlgebra_iff _ _ _).mp he).1
  have hzin : z ∩ e ∈ forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (u ∩ d) :=
    inter_mem_cone_of_ne_empty hudB hz hereg hze
  have hne : (h₁ ‘ z) ∩ e ≠ (∅ : V) := by
    rw [← hequi₁ e he z hz hze]
    intro hcon
    exact empty_not_mem_booleanConditions
      (hcon ▸ forcingCone_subset _ _ _ _ (function_value_mem hiso₁.1 hzin))
  rw [value_compose_of_mem_function hiso₁.1 hinv₂.1 hzin,
    value_compose_of_mem_function hiso₁.1 hinv₂.1 hz, hequi₁ e he z hz hze]
  exact hinv₂equi e he (h₁ ‘ z) (function_value_mem hiso₁.1 hz) hne

end ZFVP
