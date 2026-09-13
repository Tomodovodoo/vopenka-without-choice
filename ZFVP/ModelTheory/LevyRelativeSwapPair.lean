import ZFVP.ModelTheory.LevySwapStabilizer

/-! Relative homogeneity of the Levy collapse over the algebra of sets determined below `ξ`.

`levyDeterminedAlgebra κ ξ` (ZFVP/ModelTheory/LevyDeterminedSubalgebra.lean) is the complete
subalgebra of regular sets of `Coll(ω, <κ)` whose membership only depends on the part of a
condition below `ξ`, and `levyTrace κ ξ b` (ZFVP/ModelTheory/LevyDeterminedTrace.lean) is the
projection of `b` to it. ZFVP/ModelTheory/LevySwapStabilizer.lean produced, for two conditions of
equal domain with equal parts below `ξ`, an automorphism of the Boolean completion exchanging
their cones and fixing every set determined below `ξ`. This file supplies the missing input to
that lemma: two Boolean conditions with the same trace really do have such a pair of conditions
below them.

* `levy_exists_swapPair_of_levyTrace_eq`: if `u` and `v` are nonzero elements of the completion
  with `levyTrace κ ξ u = levyTrace κ ξ v`, then there are conditions `r`, `r'` of equal domain
  and equal parts below `ξ` whose cones sit inside `u` and `v`.

* `levy_exists_determinedFixing_automorphism_of_levyTrace_eq`: the swap automorphism read off
  from that pair. It carries a nonzero part of `u` onto a nonzero part of `v` and fixes every
  member of `levyDeterminedAlgebra κ ξ`.

The argument for the first theorem: pick a condition cone inside `u`, cut it at `ξ`, and take the
cone `d` of the cut. Then `d` is determined below `ξ` and is the trace of the first cone, so `d`
is inside the common trace, and the projection property
`inter_determined_eq_empty_iff_levyTrace` turns that into `d ∩ v ≠ ∅`. A condition cone inside
`d ∩ v` gives a condition `r₁` compatible with the cut, and after adding the cut to `r₁` and the
new cut back to the first condition the two conditions have equal parts below `ξ`. A last call to
`levy_exists_common_domain_extensions_agreeing` makes the domains equal without disturbing the
parts below `ξ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Two small facts about `levyCut` and the trace -/

/-- Cutting twice at the same ordinal is cutting once. -/
theorem levyCut_levyCut_self (ξ p : V) : levyCut ξ (levyCut ξ p) = levyCut ξ p :=
  levyCut_levyCut_of_subset (subset_refl ξ)

/-- The trace is monotone in the set it is the trace of. -/
theorem levyTrace_mono {κ ξ b b' : V} (hξ : ξ ⊆ κ) (hb' : b' ⊆ levyCollapse κ) (h : b ⊆ b') :
    levyTrace κ ξ b ⊆ levyTrace κ ξ b' :=
  levyTrace_subset_of_determined (levyTrace_mem_levyDeterminedAlgebra hξ hb')
    (subset_trans h (subset_levyTrace hb'))

/-! ### The pair of conditions -/

/-- Two nonzero elements of the Boolean completion of `Coll(ω, <κ)` with the same trace over
`levyDeterminedAlgebra κ ξ` have condition cones below them given by conditions of equal domain
whose parts below `ξ` agree. -/
theorem levy_exists_swapPair_of_levyTrace_eq {κ ξ u v : V} [IsOrdinal κ] (hξ : ξ ⊆ κ)
    (hu : u ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hv : v ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (htr : levyTrace κ ξ u = levyTrace κ ξ v) :
    ∃ r r', r ∈ levyCollapse κ ∧ r' ∈ levyCollapse κ ∧
      coneRegular (levyCollapse κ) (levyOrder κ) r ⊆ u ∧
      coneRegular (levyCollapse κ) (levyOrder κ) r' ⊆ v ∧
      domain r = domain r' ∧ levyCut ξ r = levyCut ξ r' := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hureg := booleanConditions_regular hu
  have hvreg := booleanConditions_regular hv
  -- a condition cone inside `u`
  obtain ⟨r₀, hr₀, hcone₀⟩ := exists_coneRegular_subset hR hu
  have hc : levyCut ξ r₀ ∈ levyCollapse κ := levyCollapse_subset hr₀ (levyCut_subset ξ r₀)
  have hdalg : coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r₀) ∈
      levyDeterminedAlgebra κ ξ := coneRegular_levyCut_mem_levyDeterminedAlgebra hξ hr₀
  have hdreg : IsForcingRegular (levyCollapse κ) (levyOrder κ)
      (coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r₀)) :=
    coneRegular_regular hR _
  -- the cone of the cut is the trace of the cone of `r₀`, hence inside the common trace
  have hdv : coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r₀) ⊆ levyTrace κ ξ v := by
    rw [← htr, ← levyTrace_coneRegular (κ := κ) hξ hr₀]
    exact levyTrace_mono hξ hureg.1 hcone₀
  have hcd : levyCut ξ r₀ ∈ coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r₀) :=
    self_mem_coneRegular hR hc
  -- so the cone of the cut meets `v`
  have hmeet : ∃ w : V, w ∈ coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r₀) ∩ v := by
    by_contra hcon
    have hempty := (eq_empty_iff_not_exists_mem _).mpr hcon
    have h2 := (inter_determined_eq_empty_iff_levyTrace hdalg hvreg.1 hvreg.2.1).mp hempty
    have hmem : levyCut ξ r₀ ∈
        coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r₀) ∩ levyTrace κ ξ v :=
      mem_inter_iff.mpr ⟨hcd, hdv _ hcd⟩
    rw [h2] at hmem
    exact not_mem_empty hmem
  obtain ⟨w, hw⟩ := hmeet
  have hdvB : coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r₀) ∩ v ∈
      booleanConditions (levyCollapse κ) (levyOrder κ) :=
    (mem_booleanConditions_iff _ _ _).mpr ⟨forcingRegular_inter hdreg hvreg, w, hw⟩
  obtain ⟨r₁, hr₁, hcone₁⟩ := exists_coneRegular_subset hR hdvB
  -- `r₁` is compatible with the cut, so we may add the cut to it
  have hr₁d : r₁ ∈ coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r₀) :=
    (mem_inter_iff.mp (hcone₁ _ (self_mem_coneRegular hR hr₁))).1
  obtain ⟨-, hh⟩ := mem_coneRegular_iff.mp hr₁d
  obtain ⟨t, ht, htc, htr₁⟩ := hh r₁ hr₁ (hR.2.1 r₁ hr₁)
  have hct : levyCut ξ r₀ ⊆ t := ((pair_mem_reverseInclusionOrder _ _ _).mp htc).2.2
  have hr₁t : r₁ ⊆ t := ((pair_mem_reverseInclusionOrder _ _ _).mp htr₁).2.2
  have hs₁ : r₁ ∪ levyCut ξ r₀ ∈ levyCollapse κ := by
    refine levyCollapse_subset ht (fun z hz ↦ ?_)
    rcases mem_union_iff.mp hz with h | h
    · exact hr₁t z h
    · exact hct z h
  have hs₁f : IsFunction (r₁ ∪ levyCut ξ r₀) := levyCollapse_isFunction hs₁
  -- the cone of `r₁ ∪ levyCut ξ r₀` is inside `v`
  have hconeS : coneRegular (levyCollapse κ) (levyOrder κ) (r₁ ∪ levyCut ξ r₀) ⊆ v := by
    refine subset_trans (coneRegular_mono hR hr₁ hs₁ ?_) (subset_trans hcone₁ ?_)
    · exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hs₁, hr₁, subset_union_left _ _⟩
    · exact fun x hx ↦ (mem_inter_iff.mp hx).2
  -- the cut of `r₀` sits inside the cut of `r₁ ∪ levyCut ξ r₀`
  have hcs : levyCut ξ r₀ ⊆ levyCut ξ (r₁ ∪ levyCut ξ r₀) := by
    rw [levyCut_union_distrib, levyCut_levyCut_self]
    exact subset_union_right _ _
  have he : levyCut ξ (r₁ ∪ levyCut ξ r₀) ∈ levyCollapse κ :=
    levyCollapse_subset hs₁ (levyCut_subset ξ _)
  -- add that cut back to `r₀`
  have hcompat : ∀ x y z : V, ⟨x, y⟩ₖ ∈ r₀ → ⟨x, z⟩ₖ ∈ levyCut ξ (r₁ ∪ levyCut ξ r₀) → y = z := by
    intro x y z hxy hxz
    obtain ⟨hxzS, hxω⟩ := (kpair_mem_levyCut_iff _ _ _ _).mp hxz
    have hxyc : ⟨x, y⟩ₖ ∈ levyCut ξ r₀ := (kpair_mem_levyCut_iff _ _ _ _).mpr ⟨hxy, hxω⟩
    have := hs₁f
    exact IsFunction.unique (subset_union_right r₁ (levyCut ξ r₀) _ hxyc) hxzS
  have hr₂ : r₀ ∪ levyCut ξ (r₁ ∪ levyCut ξ r₀) ∈ levyCollapse κ :=
    levyCollapse_union hr₀ he hcompat
  have hr₂f : IsFunction (r₀ ∪ levyCut ξ (r₁ ∪ levyCut ξ r₀)) := levyCollapse_isFunction hr₂
  have hcut₂ : levyCut ξ (r₀ ∪ levyCut ξ (r₁ ∪ levyCut ξ r₀)) =
      levyCut ξ (r₁ ∪ levyCut ξ r₀) := by
    rw [levyCut_union_distrib, levyCut_levyCut_self]
    apply mem_ext
    intro z
    rw [mem_union_iff]
    exact ⟨fun h ↦ h.elim (fun h ↦ hcs z h) id, fun h ↦ Or.inr h⟩
  -- the cone of the enlarged first condition is still inside `u`
  have hconeR₂ : coneRegular (levyCollapse κ) (levyOrder κ)
      (r₀ ∪ levyCut ξ (r₁ ∪ levyCut ξ r₀)) ⊆ u := by
    refine subset_trans (coneRegular_mono hR hr₀ hr₂ ?_) hcone₀
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr₂, hr₀, subset_union_left _ _⟩
  -- the two conditions agree at every coordinate of `ω × ξ` where both are defined
  have hagree : ∀ z ∈ domain (r₀ ∪ levyCut ξ (r₁ ∪ levyCut ξ r₀)),
      z ∈ domain (r₁ ∪ levyCut ξ r₀) → z ∈ (ω : V) ×ˢ ξ →
      (r₀ ∪ levyCut ξ (r₁ ∪ levyCut ξ r₀)) ‘ z = (r₁ ∪ levyCut ξ r₀) ‘ z := by
    intro z hz _hzs hzω
    have := hr₂f
    have := hs₁f
    have hmem : ⟨z, (r₀ ∪ levyCut ξ (r₁ ∪ levyCut ξ r₀)) ‘ z⟩ₖ ∈
        levyCut ξ (r₀ ∪ levyCut ξ (r₁ ∪ levyCut ξ r₀)) :=
      (kpair_mem_levyCut_iff _ _ _ _).mpr ⟨kpair_value_mem hz, hzω⟩
    rw [hcut₂] at hmem
    exact (value_eq_of_kpair_mem (levyCut_subset ξ _ _ hmem)).symm
  -- equalize the domains
  obtain ⟨r₃, r₃', hsub₃, hsub₃', h₃, h₃', hdom₃, hagree₃, -, -⟩ :=
    levy_exists_common_domain_extensions_agreeing hr₂ hs₁ hagree
  refine ⟨r₃, r₃', h₃, h₃', ?_, ?_, hdom₃, ?_⟩
  · refine subset_trans (coneRegular_mono hR hr₂ h₃ ?_) hconeR₂
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨h₃, hr₂, hsub₃⟩
  · refine subset_trans (coneRegular_mono hR hs₁ h₃' ?_) hconeS
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨h₃', hs₁, hsub₃'⟩
  · exact (levyCut_eq_iff_agree (levyCollapse_isFunction h₃) (levyCollapse_isFunction h₃')
      hdom₃).mpr hagree₃

/-! ### The automorphism -/

/-- Relative homogeneity of the Levy collapse over `levyDeterminedAlgebra κ ξ`: two nonzero
elements of the completion with the same trace have nonzero parts exchanged by an automorphism of
the completion that fixes every set determined below `ξ`. -/
theorem levy_exists_determinedFixing_automorphism_of_levyTrace_eq {κ ξ u v : V} [IsOrdinal κ]
    (hξ : ξ ⊆ κ)
    (hu : u ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hv : v ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (htr : levyTrace κ ξ u = levyTrace κ ξ v) :
    ∃ u' v' Θ, u' ∈ booleanConditions (levyCollapse κ) (levyOrder κ) ∧ u' ⊆ u ∧
      v' ∈ booleanConditions (levyCollapse κ) (levyOrder κ) ∧ v' ⊆ v ∧
      IsForcingAutomorphism (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) Θ ∧
      Θ ‘ u' = v' ∧ (∀ d, d ∈ levyDeterminedAlgebra κ ξ → Θ ‘ d = d) := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  obtain ⟨r, r', hr, hr', hconeu, hconev, hdom, hcut⟩ :=
    levy_exists_swapPair_of_levyTrace_eq hξ hu hv htr
  have hagree := (levyCut_eq_iff_agree (levyCollapse_isFunction hr)
    (levyCollapse_isFunction hr') hdom).mp hcut
  have hπ := levySwapAutomorphism_isForcingAutomorphism hr hr'
  refine ⟨coneRegular (levyCollapse κ) (levyOrder κ) r,
    coneRegular (levyCollapse κ) (levyOrder κ) r',
    booleanLift (levyCollapse κ) (levyOrder κ) (levySwapAutomorphism κ r r'),
    coneRegular_mem_booleanConditions hR hr, hconeu,
    coneRegular_mem_booleanConditions hR hr', hconev,
    booleanLift_isForcingAutomorphism hπ, levy_swapLift_coneRegular hr hr' hdom, ?_⟩
  intro d hd
  by_cases hne : ∃ p : V, p ∈ d
  · have hdB : d ∈ booleanConditions (levyCollapse κ) (levyOrder κ) :=
      (mem_booleanConditions_iff _ _ _).mpr
        ⟨((mem_levyDeterminedAlgebra_iff _ _ _).mp hd).1, hne⟩
    rw [booleanLift_value hdB]
    exact levySwap_imageAction_eq_self_of_determined hr hr' hagree
      (levyDeterminedAlgebra_subset_poset hd) ((mem_levyDeterminedAlgebra_iff _ _ _).mp hd).2
  · have hd0 : d = (∅ : V) := (eq_empty_iff_not_exists_mem d).mpr hne
    rw [hd0]
    refine value_eq_empty_of_not_mem_domain (fun hmem ↦ ?_)
    rw [domain_eq_of_mem_function (booleanLift_mem_function hπ)] at hmem
    obtain ⟨-, p, hp⟩ := (mem_booleanConditions_iff _ _ _).mp hmem
    exact not_mem_empty hp

end ZFVP
