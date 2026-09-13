import ZFVP.ModelTheory.LevySwapDeterminedSupport
import ZFVP.ModelTheory.LevySupportValueBound
import ZFVP.ModelTheory.LevyConePairArrangement
import ZFVP.ModelTheory.LevyDeterminedTrace

/-! Value swaps of the Levy collapse in the forced stabilizer, and relative homogeneity for
condition cones.

`ZFVP/ModelTheory/LevySupportValueBound.lean` puts the lifts of the row permutations above `ξ`
into the forced stabilizer of a finite set of saturated nice names. The row permutations move a
condition only above `ξ`, so on their own they say nothing about two conditions that differ below
`ξ`. This file adds the other family of automorphisms of `Coll(ω, <κ)` the Solovay argument uses,
the value swaps `levySwapAutomorphism κ r r'`, and shows they lift into the same forced
stabilizer as soon as `r` and `r'` agree on `ω × ξ`.

* `levy_swapLift_mem_forcedStabilizer`: the lift of the swap of two conditions agreeing on
  `ω × ξ` lies in the forced stabilizer of `E`, given that every base support value of `E` is
  determined below `ξ`.

* `levy_exists_swapLifts_in_forcedStabilizer_finite`: for an internally finite set of saturated
  nice names there is one `ξ < κ` that works for every such pair, matching
  `levy_exists_rowPermutations_in_forcedStabilizer_finite`.

* `levy_swapLift_coneRegular`: the lift carries the cone of `r` to the cone of `r'` when the two
  conditions have equal domain.

* `levy_exists_forcedStabilizer_automorphism_cone`: the two together, which is relative
  homogeneity for condition cones inside the forced stabilizer.

* `levy_exists_forcedStabilizer_automorphism_cone_extensions`: the same after normalizing an
  arbitrary agreeing pair to a common domain.

* `levyCut_eq_iff_agree` and `levy_forcedStabilizer_automorphism_cone_of_levyCut_eq`: agreement on
  `ω × ξ` for conditions of equal domain is the same as equality of the `ξ`-parts, so the
  automorphism exists whenever the two cones have the same trace over `levyDeterminedAlgebra κ ξ`
  in the form `levyCut ξ r = levyCut ξ r'`. The converse direction, from equality of the traces
  back to equality of the `ξ`-parts, is not proved here; see the comment at
  `levy_forcedStabilizer_automorphism_cone_of_levyCut_eq`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The lift of a value swap is in the forced stabilizer -/

/-- The lift of the value swap of two conditions that agree at every coordinate of `ω × ξ` where
both are defined lies in the forced stabilizer of `E`, given that every base support value of `E`
is determined below `ξ`. This is the value-swap counterpart of
`levy_rowPermutations_in_forcedStabilizer_of_determined`. -/
theorem levy_swapLift_mem_forcedStabilizer {κ ξ K E r r' : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ)
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) K σ)
    (hdet : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E,
      IsLevyDeterminedBelow κ ξ a) :
    booleanLift (levyCollapse κ) (levyOrder κ) (levySwapAutomorphism κ r r') ∈
      forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))) E := by
  refine booleanLift_mem_forcedStabilizer_of_fixes_supportValuesBase
    ⟨∅, empty_mem_levyCollapse κ⟩ (levyCollapse_poset κ).1
    (levySwapAutomorphism_isForcingAutomorphism hr hr') hE (fun a ha ↦ ?_)
  have hareg : IsForcingRegular (levyCollapse κ) (levyOrder κ) a :=
    (mem_regularSets_iff _ _ _).mp
      (supportValuesBase_subset_regularSets (levyCollapse_poset κ).1 _ K E a ha)
  exact levySwap_imageAction_eq_self_of_determined hr hr' hagree hareg.1 (hdet a ha)

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hAC hU hc hω hκ in
/-- For a finite set of saturated nice names over `ω × ω` there is one ordinal `ξ < κ` such that
every value swap of two conditions agreeing on `ω × ξ` lifts into the forced stabilizer of the
names. Same `ξ` as in `levy_exists_rowPermutations_in_forcedStabilizer_finite`, obtained from the
same bound on the base support values. -/
theorem levy_exists_swapLifts_in_forcedStabilizer_finite {E : V}
    (hEfin : IsInternallyFinite E)
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ) :
    ∃ ξ ∈ κ, ∀ r r' : V, r ∈ levyCollapse κ → r' ∈ levyCollapse κ →
      (∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z) →
      booleanLift (levyCollapse κ) (levyOrder κ) (levySwapAutomorphism κ r r') ∈
        forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ))) E := by
  obtain ⟨ξ, hξ, hdet⟩ := levy_exists_determined_below_finite_support hAC hU hc hω hκ hEfin
  exact ⟨ξ, hξ, fun r r' hr hr' hagree ↦
    levy_swapLift_mem_forcedStabilizer hr hr' hagree hE hdet⟩

end

/-! ### The action on condition cones -/

/-- The lift of the value swap of two conditions of equal domain carries the cone of the first to
the cone of the second. -/
theorem levy_swapLift_coneRegular {κ r r' : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) (hdom : domain r = domain r') :
    (booleanLift (levyCollapse κ) (levyOrder κ) (levySwapAutomorphism κ r r')) ‘
        (coneRegular (levyCollapse κ) (levyOrder κ) r) =
      coneRegular (levyCollapse κ) (levyOrder κ) r' := by
  rw [booleanLift_coneRegular (levySwapAutomorphism_isForcingAutomorphism hr hr') hr,
    levySwapAutomorphism_value hr,
    levySwapCondition_self (levyCollapse_isFunction hr) (levyCollapse_isFunction hr') hdom]

/-- Relative homogeneity for condition cones inside the forced stabilizer: two conditions of equal
domain that agree on `ω × ξ` have their cones exchanged by an automorphism of the Boolean
completion that lies in the forced stabilizer of `E`, provided every base support value of `E` is
determined below `ξ`. -/
theorem levy_exists_forcedStabilizer_automorphism_cone {κ ξ K E r r' : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) (hdom : domain r = domain r')
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) K σ)
    (hdet : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E,
      IsLevyDeterminedBelow κ ξ a) :
    ∃ Θ ∈ forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))) E,
      IsForcingAutomorphism (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) Θ ∧
        Θ ‘ (coneRegular (levyCollapse κ) (levyOrder κ) r) =
          coneRegular (levyCollapse κ) (levyOrder κ) r' :=
  ⟨booleanLift (levyCollapse κ) (levyOrder κ) (levySwapAutomorphism κ r r'),
    levy_swapLift_mem_forcedStabilizer hr hr' hagree hE hdet,
    booleanLift_isForcingAutomorphism (levySwapAutomorphism_isForcingAutomorphism hr hr'),
    levy_swapLift_coneRegular hr hr' hdom⟩

/-- The equal-domain hypothesis removed by normalizing first: two conditions agreeing on `ω × ξ`
have extensions of a common domain whose cones are exchanged by an automorphism in the forced
stabilizer of `E`. The extensions come from
`levy_exists_common_domain_extensions_agreeing`, which keeps the agreement on `ω × ξ`. -/
theorem levy_exists_forcedStabilizer_automorphism_cone_extensions {κ ξ K E r r' : V}
    (hr : r ∈ levyCollapse κ) (hr' : r' ∈ levyCollapse κ)
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) K σ)
    (hdet : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E,
      IsLevyDeterminedBelow κ ξ a) :
    ∃ r₁ r₁' : V, r ⊆ r₁ ∧ r' ⊆ r₁' ∧ r₁ ∈ levyCollapse κ ∧ r₁' ∈ levyCollapse κ ∧
      domain r₁ = domain r₁' ∧
      ∃ Θ ∈ forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ))) E,
        IsForcingAutomorphism (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) Θ ∧
          Θ ‘ (coneRegular (levyCollapse κ) (levyOrder κ) r₁) =
            coneRegular (levyCollapse κ) (levyOrder κ) r₁' := by
  obtain ⟨r₁, r₁', hsub, hsub', h1, h1', hdom1, hagree1, -, -⟩ :=
    levy_exists_common_domain_extensions_agreeing hr hr' hagree
  exact ⟨r₁, r₁', hsub, hsub', h1, h1', hdom1,
    levy_exists_forcedStabilizer_automorphism_cone h1 h1' hdom1 hagree1 hE hdet⟩

/-! ### The trace form -/

/-- For two conditions of equal domain, agreement at every coordinate of `ω × ξ` where both are
defined is the same as equality of the parts below `ξ`. The direction from equal parts to
agreement does not use the equality of the domains. -/
theorem levyCut_eq_iff_agree {ξ r r' : V} (hrf : IsFunction r) (hr'f : IsFunction r')
    (hdom : domain r = domain r') :
    levyCut ξ r = levyCut ξ r' ↔
      ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z := by
  have := hrf
  have := hr'f
  constructor
  · intro hcut z hz hz' hzω
    have hmem : ⟨z, r ‘ z⟩ₖ ∈ levyCut ξ r :=
      kpair_mem_restrict_iff.mpr ⟨kpair_value_mem hz, hzω⟩
    rw [hcut] at hmem
    exact (value_eq_of_kpair_mem (levyCut_subset ξ r' _ hmem)).symm
  · intro hagree
    apply mem_ext
    intro p
    constructor
    · intro hp
      obtain ⟨hpr, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
      have hxd : x ∈ domain r := mem_domain_of_kpair_mem hpr
      have hxd' : x ∈ domain r' := hdom ▸ hxd
      have hy : y = r ‘ x := (value_eq_of_kpair_mem hpr).symm
      subst hy
      rw [hagree x hxd hxd' hx]
      exact kpair_mem_restrict_iff.mpr ⟨kpair_value_mem hxd', hx⟩
    · intro hp
      obtain ⟨hpr, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
      have hxd' : x ∈ domain r' := mem_domain_of_kpair_mem hpr
      have hxd : x ∈ domain r := hdom ▸ hxd'
      have hy : y = r' ‘ x := (value_eq_of_kpair_mem hpr).symm
      subst hy
      rw [← hagree x hxd hxd' hx]
      exact kpair_mem_restrict_iff.mpr ⟨kpair_value_mem hxd, hx⟩

/-- The trace form of relative homogeneity. Two conditions of equal domain whose parts below `ξ`
are equal have the same trace over `levyDeterminedAlgebra κ ξ`, and their cones are exchanged by
an automorphism in the forced stabilizer of `E`.

Only this direction is proved. The converse, from `levyTrace κ ξ (coneRegular ... r) =
levyTrace κ ξ (coneRegular ... r')` back to `levyCut ξ r = levyCut ξ r'`, would need
`coneRegular (levyCollapse κ) (levyOrder κ)` to be injective on conditions, which is not available
in the development. -/
theorem levy_forcedStabilizer_automorphism_cone_of_levyCut_eq {κ ξ K E r r' : V}
    (hξ : ξ ⊆ κ) (hr : r ∈ levyCollapse κ) (hr' : r' ∈ levyCollapse κ)
    (hdom : domain r = domain r') (hcut : levyCut ξ r = levyCut ξ r')
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) K σ)
    (hdet : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E,
      IsLevyDeterminedBelow κ ξ a) :
    levyTrace κ ξ (coneRegular (levyCollapse κ) (levyOrder κ) r) =
        levyTrace κ ξ (coneRegular (levyCollapse κ) (levyOrder κ) r') ∧
      ∃ Θ ∈ forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ))) E,
        IsForcingAutomorphism (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) Θ ∧
          Θ ‘ (coneRegular (levyCollapse κ) (levyOrder κ) r) =
            coneRegular (levyCollapse κ) (levyOrder κ) r' :=
  ⟨levyTrace_eq_of_agree hξ hr hr' hcut,
    levy_exists_forcedStabilizer_automorphism_cone hr hr' hdom
      ((levyCut_eq_iff_agree (levyCollapse_isFunction hr) (levyCollapse_isFunction hr') hdom).mp
        hcut) hE hdet⟩

end ZFVP
