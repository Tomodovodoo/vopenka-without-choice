import ZFVP.ModelTheory.LevyOrbitTransferCone

/-! Support clauses for the cone isomorphisms coming from an automorphism.

`exists_booleanAutomorphism_of_cone_isomorphisms` lifts a pair of cone isomorphisms of the
Boolean completion `B` to an automorphism of `B`, and
`exists_forcedStabilizer_automorphism_of_cone_isomorphisms` puts that automorphism in the forced
stabilizer of a set `E` of saturated nice names provided both isomorphisms satisfy the support
clause

  `coneImage P R b0 f (a ∩ b0) = a ∩ c0`

for every base support value `a` of `E`. `LevyComplementCone` builds the two isomorphisms for
`b0 = coneRegular r` and `c0 = coneRegular r'` out of the value-swap automorphism
`levySwapAutomorphism κ r r'`, but proves nothing about the support values. This module supplies
the missing clause.

* An automorphism `Θ` of `B` restricts to an isomorphism of the cone below `b0` with the cone
  below `Θ ‘ b0`, and that restriction satisfies the support clause for every regular set that
  `Θ` fixes (`coneImage_of_automorphism_restriction`). The same holds for the complementary
  cones, because an automorphism carries `¬b0` to `¬(Θ ‘ b0)`; that is proved here in the form
  "`x ⊆ ¬b0` iff `Θ x ⊆ ¬(Θ b0)`", which also covers the degenerate case where `¬b0` is empty and
  so is not a condition (`coneImage_of_automorphism_restriction_negation`).

* The value swap of two conditions `r`, `r'` that agree on `ω × ξ` wherever both are defined
  fixes every condition whose domain lies in `ω × ξ` (`levySwap_fixes_localized`), hence fixes
  every regular set that is the closure of a set of such conditions
  (`levySwap_imageAction_forcingClosure`).

* Putting the two together gives the two cone isomorphisms of the Levy collapse together with
  their support clauses, either from the assumption that the swap fixes the base support values
  (`levy_cone_isomorphism_support_of_fixed`,
  `levy_complement_cone_isomorphism_support_of_fixed`) or from the assumption that the base
  support values are closures of `ξ`-localized conditions
  (`levy_complement_cone_isomorphism_support_of_agree`).
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A set is empty exactly when it has no member. -/
theorem eq_empty_iff_not_exists_mem (A : V) : A = (∅ : V) ↔ ¬ ∃ z : V, z ∈ A := by
  constructor
  · rintro rfl ⟨z, hz⟩
    exact not_mem_empty hz
  · intro h
    exact mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ h, fun hz ↦ absurd hz not_mem_empty⟩)

/-! ### An automorphism of the Boolean completion -/

section BooleanAutomorphism

variable {P R Θ : V}

/-- An automorphism of the completion preserves and reflects inclusion of conditions. -/
theorem boolAutomorphism_subset_iff
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    {x y : V} (hx : x ∈ booleanConditions P R) (hy : y ∈ booleanConditions P R) :
    Θ ‘ x ⊆ Θ ‘ y ↔ x ⊆ y := by
  have hΘx := function_value_mem hΘ.1 hx
  have hΘy := function_value_mem hΘ.1 hy
  have h := hΘ.2.2.2 x hx y hy
  rw [kpair_mem_booleanOrder_iff, kpair_mem_booleanOrder_iff] at h
  exact ⟨fun hs ↦ (h.mpr ⟨hΘx, hΘy, hs⟩).2.2, fun hs ↦ (h.mp ⟨hx, hy, hs⟩).2.2⟩

/-- An automorphism of the completion preserves and reflects compatibility of conditions: the
meet of two conditions is nonempty exactly when the meet of their images is. -/
theorem boolAutomorphism_inter_nonempty_iff
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    {x y : V} (hx : x ∈ booleanConditions P R) (hy : y ∈ booleanConditions P R) :
    (∃ z : V, z ∈ Θ ‘ x ∩ Θ ‘ y) ↔ (∃ z : V, z ∈ x ∩ y) := by
  constructor
  · rintro ⟨z, hz⟩
    have hwB := inter_mem_booleanConditions (function_value_mem hΘ.1 hx)
      (function_value_mem hΘ.1 hy) hz
    obtain ⟨u, hu, huv⟩ := forcingAutomorphism_surjective hΘ _ hwB
    obtain ⟨w, hw⟩ := booleanConditions_nonempty hu
    have hux : u ⊆ x := (boolAutomorphism_subset_iff hΘ hu hx).mp
      (by rw [huv]; exact fun t ht ↦ (mem_inter_iff.mp ht).1)
    have huy : u ⊆ y := (boolAutomorphism_subset_iff hΘ hu hy).mp
      (by rw [huv]; exact fun t ht ↦ (mem_inter_iff.mp ht).2)
    exact ⟨w, mem_inter_iff.mpr ⟨hux w hw, huy w hw⟩⟩
  · rintro ⟨z, hz⟩
    have hwB := inter_mem_booleanConditions hx hy hz
    obtain ⟨w, hw⟩ := booleanConditions_nonempty (function_value_mem hΘ.1 hwB)
    have h1 : Θ ‘ (x ∩ y) ⊆ Θ ‘ x :=
      (boolAutomorphism_subset_iff hΘ hwB hx).mpr (fun t ht ↦ (mem_inter_iff.mp ht).1)
    have h2 : Θ ‘ (x ∩ y) ⊆ Θ ‘ y :=
      (boolAutomorphism_subset_iff hΘ hwB hy).mpr (fun t ht ↦ (mem_inter_iff.mp ht).2)
    exact ⟨w, mem_inter_iff.mpr ⟨h1 w hw, h2 w hw⟩⟩

/-- The disjointness form of the previous lemma. -/
theorem boolAutomorphism_inter_empty_iff
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    {x y : V} (hx : x ∈ booleanConditions P R) (hy : y ∈ booleanConditions P R) :
    Θ ‘ x ∩ Θ ‘ y = (∅ : V) ↔ x ∩ y = (∅ : V) := by
  rw [eq_empty_iff_not_exists_mem, eq_empty_iff_not_exists_mem]
  exact not_congr (boolAutomorphism_inter_nonempty_iff hΘ hx hy)

/-- The restriction of an automorphism to the cone below `b`, as an isomorphism onto the cone
below `c`, whenever the automorphism matches the two cones. -/
theorem coneRestrictMap_isForcingIsomorphism {b c : V}
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    (hbc : ∀ x ∈ booleanConditions P R,
      ⟨x, b⟩ₖ ∈ booleanOrder P R ↔ ⟨Θ ‘ x, c⟩ₖ ∈ booleanOrder P R) :
    IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) b)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b))
      (forcingCone (booleanConditions P R) (booleanOrder P R) c)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) c))
      (coneRestrictMap P R b Θ) := by
  have : IsFunction Θ := IsFunction.of_mem hΘ.1
  have hFP : ∀ x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b,
      Θ ‘ x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) c := by
    intro x hx
    obtain ⟨hxQ, hxb⟩ := (mem_forcingCone_iff _ _ _ _).mp hx
    exact (mem_forcingCone_iff _ _ _ _).mpr
      ⟨function_value_mem hΘ.1 hxQ, (hbc x hxQ).mp hxb⟩
  have hGQ : ∀ y ∈ forcingCone (booleanConditions P R) (booleanOrder P R) c,
      (converseGraph Θ) ‘ y ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b := by
    intro y hy
    obtain ⟨hyQ, hyc⟩ := (mem_forcingCone_iff _ _ _ _).mp hy
    obtain ⟨a, ha, rfl⟩ := forcingAutomorphism_surjective hΘ y hyQ
    rw [converseGraph_value_value hΘ.1 hΘ.2.1 ha]
    exact (mem_forcingCone_iff _ _ _ _).mpr ⟨ha, (hbc a ha).mpr hyc⟩
  refine isForcingIsomorphism_of_inverse (fun x ↦ Θ ‘ x) (fun y ↦ (converseGraph Θ) ‘ y)
    (by definability) hFP hGQ ?_ ?_ ?_
  · intro x hx
    exact converseGraph_value_value hΘ.1 hΘ.2.1 ((mem_forcingCone_iff _ _ _ _).mp hx).1
  · intro y hy
    exact value_converseGraph_value hΘ.1 hΘ.2.1
      (hΘ.2.2.1.symm ▸ ((mem_forcingCone_iff _ _ _ _).mp hy).1)
  · intro x hx y hy
    have hxQ := ((mem_forcingCone_iff _ _ _ _).mp hx).1
    have hyQ := ((mem_forcingCone_iff _ _ _ _).mp hy).1
    rw [kpair_mem_restrictedOrder_iff, kpair_mem_restrictedOrder_iff]
    simp only [hx, hy, hFP x hx, hFP y hy, and_true]
    exact hΘ.2.2.2 x hxQ y hyQ

/-- The support clause for the restriction of an automorphism to a cone. The hypothesis `himg`
says that the automorphism matches the two regular sets `b` and `c`; the hypothesis on `a` says
that the automorphism fixes `a` whenever `a` is a condition, which is all that can be asked since
the empty regular set is not a condition. -/
theorem coneImage_coneRestrictMap_eq {b c a : V}
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    (hf : IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) b)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b))
      (forcingCone (booleanConditions P R) (booleanOrder P R) c)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) c))
      (coneRestrictMap P R b Θ))
    (hb : IsForcingRegular P R b) (hc : IsForcingRegular P R c)
    (himg : ∀ x ∈ booleanConditions P R, x ⊆ b ↔ Θ ‘ x ⊆ c)
    (ha : IsForcingRegular P R a) (hfix : a ∈ booleanConditions P R → Θ ‘ a = a) :
    coneImage P R b (coneRestrictMap P R b Θ) (a ∩ b) = a ∩ c := by
  by_cases hne : ∃ z : V, z ∈ a ∩ b
  · obtain ⟨z, hz⟩ := hne
    have haB : a ∈ booleanConditions P R :=
      (mem_booleanConditions_iff _ _ _).mpr ⟨ha, z, (mem_inter_iff.mp hz).1⟩
    have hbB : b ∈ booleanConditions P R :=
      (mem_booleanConditions_iff _ _ _).mpr ⟨hb, z, (mem_inter_iff.mp hz).2⟩
    have habB : a ∩ b ∈ booleanConditions P R := inter_mem_booleanConditions haB hbB hz
    have habc : a ∩ b ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b :=
      mem_forcingCone_of_subset habB hbB (fun w hw ↦ (mem_inter_iff.mp hw).2)
    have hΘa : Θ ‘ a = a := hfix haB
    rw [coneImage_value hf habc, coneRestrictMap_value habc]
    apply SetTheory.subset_antisymm
    · intro w hw
      refine mem_inter_iff.mpr ⟨?_, ?_⟩
      · have hsub := (boolAutomorphism_subset_iff hΘ habB haB).mpr
          (fun t ht ↦ (mem_inter_iff.mp ht).1)
        rw [hΘa] at hsub
        exact hsub w hw
      · exact (himg _ habB).mp (fun t ht ↦ (mem_inter_iff.mp ht).2) w hw
    · intro w hw
      have hcB : c ∈ booleanConditions P R :=
        (mem_booleanConditions_iff _ _ _).mpr ⟨hc, w, (mem_inter_iff.mp hw).2⟩
      have hacB : a ∩ c ∈ booleanConditions P R := inter_mem_booleanConditions haB hcB hw
      obtain ⟨u, hu, huv⟩ := forcingAutomorphism_surjective hΘ _ hacB
      have hua : u ⊆ a := by
        refine (boolAutomorphism_subset_iff hΘ hu haB).mp ?_
        rw [huv, hΘa]
        exact fun t ht ↦ (mem_inter_iff.mp ht).1
      have hub : u ⊆ b := (himg u hu).mpr
        (by rw [huv]; exact fun t ht ↦ (mem_inter_iff.mp ht).2)
      have hsub := (boolAutomorphism_subset_iff hΘ hu habB).mpr
        (fun t ht ↦ mem_inter_iff.mpr ⟨hua t ht, hub t ht⟩)
      rw [huv] at hsub
      exact hsub w hw
  · have h0 : a ∩ b = (∅ : V) := (eq_empty_iff_not_exists_mem _).mpr hne
    rw [h0, coneImage_empty]
    refine ((eq_empty_iff_not_exists_mem _).mpr ?_).symm
    rintro ⟨w, hw⟩
    have haB : a ∈ booleanConditions P R :=
      (mem_booleanConditions_iff _ _ _).mpr ⟨ha, w, (mem_inter_iff.mp hw).1⟩
    have hcB : c ∈ booleanConditions P R :=
      (mem_booleanConditions_iff _ _ _).mpr ⟨hc, w, (mem_inter_iff.mp hw).2⟩
    have hacB : a ∩ c ∈ booleanConditions P R := inter_mem_booleanConditions haB hcB hw
    obtain ⟨u, hu, huv⟩ := forcingAutomorphism_surjective hΘ _ hacB
    have hua : u ⊆ a := by
      refine (boolAutomorphism_subset_iff hΘ hu haB).mp ?_
      rw [huv, hfix haB]
      exact fun t ht ↦ (mem_inter_iff.mp ht).1
    have hub : u ⊆ b := (himg u hu).mpr
      (by rw [huv]; exact fun t ht ↦ (mem_inter_iff.mp ht).2)
    obtain ⟨t, ht⟩ := booleanConditions_nonempty hu
    exact hne ⟨t, mem_inter_iff.mpr ⟨hua t ht, hub t ht⟩⟩

/-- An automorphism of the completion restricts to an isomorphism of the cone below `b0` with
the cone below its image, and that restriction satisfies the support clause at every regular set
that the automorphism fixes. -/
theorem coneImage_of_automorphism_restriction {b0 : V}
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    (hb0 : b0 ∈ booleanConditions P R) :
    ∃ f, IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) b0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b0))
      (forcingCone (booleanConditions P R) (booleanOrder P R) (Θ ‘ b0))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (Θ ‘ b0))) f ∧
      ∀ a : V, IsForcingRegular P R a → (a ∈ booleanConditions P R → Θ ‘ a = a) →
        coneImage P R b0 f (a ∩ b0) = a ∩ Θ ‘ b0 := by
  have hc0 : Θ ‘ b0 ∈ booleanConditions P R := function_value_mem hΘ.1 hb0
  have hbc : ∀ x ∈ booleanConditions P R,
      ⟨x, b0⟩ₖ ∈ booleanOrder P R ↔ ⟨Θ ‘ x, Θ ‘ b0⟩ₖ ∈ booleanOrder P R :=
    fun x hx ↦ hΘ.2.2.2 x hx b0 hb0
  have himg : ∀ x ∈ booleanConditions P R, x ⊆ b0 ↔ Θ ‘ x ⊆ Θ ‘ b0 :=
    fun x hx ↦ (boolAutomorphism_subset_iff hΘ hx hb0).symm
  exact ⟨coneRestrictMap P R b0 Θ, coneRestrictMap_isForcingIsomorphism hΘ hbc,
    fun a ha hfix ↦ coneImage_coneRestrictMap_eq hΘ
      (coneRestrictMap_isForcingIsomorphism hΘ hbc) (booleanConditions_regular hb0)
      (booleanConditions_regular hc0) himg ha hfix⟩

/-- The same for the complementary cones: an automorphism carries the negation of `b0` to the
negation of the image of `b0`, so it restricts to an isomorphism of the two complementary cones,
and that restriction satisfies the support clause at every regular set the automorphism fixes.
The degenerate case where the negation of `b0` is empty is covered: then the negation of the
image is empty as well and both cones are empty. -/
theorem coneImage_of_automorphism_restriction_negation {b0 : V}
    (hR : IsForcingPreorder P R)
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    (hb0 : b0 ∈ booleanConditions P R) :
    ∃ g, IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R b0))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R b0)))
      (forcingCone (booleanConditions P R) (booleanOrder P R)
        (forcingNegation P R (Θ ‘ b0)))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R)
          (forcingNegation P R (Θ ‘ b0)))) g ∧
      ∀ a : V, IsForcingRegular P R a → (a ∈ booleanConditions P R → Θ ‘ a = a) →
        coneImage P R (forcingNegation P R b0) g (a ∩ forcingNegation P R b0) =
          a ∩ forcingNegation P R (Θ ‘ b0) := by
  have hc0 : Θ ‘ b0 ∈ booleanConditions P R := function_value_mem hΘ.1 hb0
  have hn0r : IsForcingRegular P R (forcingNegation P R b0) :=
    forcingNegation_regular hR (booleanConditions_regular hb0).2.1
  have hm0r : IsForcingRegular P R (forcingNegation P R (Θ ‘ b0)) :=
    forcingNegation_regular hR (booleanConditions_regular hc0).2.1
  have himg : ∀ x ∈ booleanConditions P R,
      x ⊆ forcingNegation P R b0 ↔ Θ ‘ x ⊆ forcingNegation P R (Θ ‘ b0) := by
    intro x hx
    rw [subset_forcingNegation_iff hR (booleanConditions_regular hx)
        (booleanConditions_subset hb0),
      subset_forcingNegation_iff hR (booleanConditions_regular (function_value_mem hΘ.1 hx))
        (booleanConditions_subset hc0)]
    exact (boolAutomorphism_inter_empty_iff hΘ hx hb0).symm
  have hbc : ∀ x ∈ booleanConditions P R,
      ⟨x, forcingNegation P R b0⟩ₖ ∈ booleanOrder P R ↔
        ⟨Θ ‘ x, forcingNegation P R (Θ ‘ b0)⟩ₖ ∈ booleanOrder P R := by
    intro x hx
    rw [kpair_mem_booleanOrder_iff, kpair_mem_booleanOrder_iff]
    constructor
    · rintro ⟨-, -, hsub⟩
      have h2 := (himg x hx).mp hsub
      obtain ⟨w, hw⟩ := booleanConditions_nonempty (function_value_mem hΘ.1 hx)
      exact ⟨function_value_mem hΘ.1 hx,
        (mem_booleanConditions_iff _ _ _).mpr ⟨hm0r, w, h2 w hw⟩, h2⟩
    · rintro ⟨-, -, hsub⟩
      have h2 := (himg x hx).mpr hsub
      obtain ⟨w, hw⟩ := booleanConditions_nonempty hx
      exact ⟨hx, (mem_booleanConditions_iff _ _ _).mpr ⟨hn0r, w, h2 w hw⟩, h2⟩
  exact ⟨coneRestrictMap P R (forcingNegation P R b0) Θ,
    coneRestrictMap_isForcingIsomorphism hΘ hbc,
    fun a ha hfix ↦ coneImage_coneRestrictMap_eq hΘ
      (coneRestrictMap_isForcingIsomorphism hΘ hbc) hn0r hm0r himg ha hfix⟩

end BooleanAutomorphism

/-! ### The value swap on localized conditions -/

/-- If `r` and `r'` agree at every coordinate of `ω × ξ` where both are defined, then swapping
their values fixes every function whose domain is contained in `ω × ξ`. -/
theorem levySwap_fixes_localized {κ ξ r r' s : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ)
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)
    (hs : IsFunction s) (hsdom : domain s ⊆ (ω : V) ×ˢ ξ) :
    levySwapCondition r r' s = s := by
  have := hs
  have := levyCollapse_isFunction hr
  have := levyCollapse_isFunction hr'
  apply functions_eq_of_domain_values
  · exact levySwapCondition_domain r r' s
  · intro z hz
    rw [levySwapCondition_domain] at hz
    rw [levySwapCondition_value hz]
    by_cases h1 : ⟨z, s ‘ z⟩ₖ ∈ r ∧ z ∈ domain r'
    · rw [levySwapValue_left h1.1 h1.2]
      have hzr : z ∈ domain r := mem_domain_of_kpair_mem h1.1
      rw [← hagree z hzr h1.2 (hsdom z hz)]
      exact value_eq_of_kpair_mem h1.1
    · by_cases h2 : ⟨z, s ‘ z⟩ₖ ∈ r' ∧ z ∈ domain r
      · have hnp : ⟨z, s ‘ z⟩ₖ ∉ r := fun h ↦ h1 ⟨h, mem_domain_of_kpair_mem h2.1⟩
        rw [levySwapValue_right h2.1 h2.2 hnp]
        have hzr' : z ∈ domain r' := mem_domain_of_kpair_mem h2.1
        rw [hagree z h2.2 hzr' (hsdom z hz)]
        exact value_eq_of_kpair_mem h2.1
      · exact levySwapValue_fixed (by rintro (h | h); exacts [h1 h, h2 h])

/-- The value swap of two conditions agreeing on `ω × ξ` fixes the regular closure of any set of
conditions with domains inside `ω × ξ`. Those closures are genuine regular sets of the collapse,
as the first half of the conclusion records; the regular cone of a condition of `levyCollapse ξ`
is one of them. -/
theorem levySwap_imageAction_forcingClosure {κ ξ r r' X : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ)
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)
    (hX : X ⊆ levyCollapse κ) (hXdom : ∀ s ∈ X, domain s ⊆ (ω : V) ×ˢ ξ) :
    IsForcingRegular (levyCollapse κ) (levyOrder κ)
        (forcingClosure (levyCollapse κ) (levyOrder κ) X) ∧
      imageAction (levySwapAutomorphism κ r r')
          (forcingClosure (levyCollapse κ) (levyOrder κ) X) =
        forcingClosure (levyCollapse κ) (levyOrder κ) X := by
  have hπ := levySwapAutomorphism_isForcingAutomorphism hr hr'
  have hfixX : ∀ s ∈ X, (levySwapAutomorphism κ r r') ‘ s = s := by
    intro s hs
    rw [levySwapAutomorphism_value (hX s hs)]
    exact levySwap_fixes_localized hr hr' hagree (levyCollapse_isFunction (hX s hs)) (hXdom s hs)
  have hAB : ∀ q ∈ levyCollapse κ, (levySwapAutomorphism κ r r') ‘ q ∈ X ↔ q ∈ X := by
    intro q hq
    constructor
    · intro h
      have hswap : levySwapCondition r r' q ∈ levyCollapse κ := levySwapCondition_mem hr hr' hq
      have h1 : (levySwapAutomorphism κ r r') ‘ ((levySwapAutomorphism κ r r') ‘ q) = q := by
        rw [levySwapAutomorphism_value hq, levySwapAutomorphism_value hswap]
        exact levySwapCondition_involutive (levyCollapse_isFunction hr)
          (levyCollapse_isFunction hr') (levyCollapse_isFunction hq)
      rw [hfixX _ h] at h1
      exact h1 ▸ h
    · intro h
      rw [hfixX q h]
      exact h
  refine ⟨forcingClosure_regular (levyCollapse_poset κ).1 hX, ?_⟩
  exact imageAction_eq_of_iff hπ (forcingClosure_subset _ _ _) (forcingClosure_subset _ _ _)
    (fun q hq ↦ forcingClosure_action_iff hπ hX hX hAB hq)

/-! ### The two cone isomorphisms of the Levy collapse with their support clauses -/

section LevyCones

variable {κ r r' K E : V}

/-- The positive cone isomorphism together with its support clause, from the assumption that the
value swap fixes every base support value of `E`. -/
theorem levy_cone_isomorphism_support_of_fixed (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) (hdom : domain r = domain r')
    (hfix : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E,
      imageAction (levySwapAutomorphism κ r r') a = a) :
    ∃ f, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) r))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) r)))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) r'))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) r'))) f ∧
      ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E,
        coneImage (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r) f
            (a ∩ coneRegular (levyCollapse κ) (levyOrder κ) r) =
          a ∩ coneRegular (levyCollapse κ) (levyOrder κ) r' := by
  have hπ := levySwapAutomorphism_isForcingAutomorphism hr hr'
  have hΘ := booleanLift_isForcingAutomorphism hπ
  have hb0 := coneRegular_mem_booleanConditions (levyCollapse_poset κ).1 hr
  have hval : (levySwapAutomorphism κ r r') ‘ r = r' := by
    rw [levySwapAutomorphism_value hr]
    exact levySwapCondition_self (levyCollapse_isFunction hr) (levyCollapse_isFunction hr') hdom
  have hΘb0 : (booleanLift (levyCollapse κ) (levyOrder κ) (levySwapAutomorphism κ r r')) ‘
      (coneRegular (levyCollapse κ) (levyOrder κ) r) =
      coneRegular (levyCollapse κ) (levyOrder κ) r' := by
    rw [booleanLift_coneRegular hπ hr, hval]
  obtain ⟨f, hf, hcl⟩ := coneImage_of_automorphism_restriction hΘ hb0
  rw [hΘb0] at hf hcl
  refine ⟨f, hf, fun a ha ↦ ?_⟩
  obtain ⟨k, -, σ, -, rfl⟩ := (mem_supportValuesBase_iff _ _ _ _ _ _).mp ha
  refine hcl _ (booleanValueBase_regular (levyCollapse_poset κ).1 _ _) (fun haB ↦ ?_)
  rw [booleanLift_value haB]
  exact hfix _ ha

/-- The complementary cone isomorphism together with its support clause, from the assumption
that the value swap fixes every base support value of `E`. This is the clause asked for by
`exists_forcedStabilizer_automorphism_of_cone_isomorphisms`. -/
theorem levy_complement_cone_isomorphism_support_of_fixed (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) (hdom : domain r = domain r')
    (hfix : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E,
      imageAction (levySwapAutomorphism κ r r') a = a) :
    ∃ g, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r)))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r))))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r')))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r')))) g ∧
      ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E,
        coneImage (levyCollapse κ) (levyOrder κ)
            (forcingNegation (levyCollapse κ) (levyOrder κ)
              (coneRegular (levyCollapse κ) (levyOrder κ) r)) g
            (a ∩ forcingNegation (levyCollapse κ) (levyOrder κ)
              (coneRegular (levyCollapse κ) (levyOrder κ) r)) =
          a ∩ forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r') := by
  have hπ := levySwapAutomorphism_isForcingAutomorphism hr hr'
  have hΘ := booleanLift_isForcingAutomorphism hπ
  have hb0 := coneRegular_mem_booleanConditions (levyCollapse_poset κ).1 hr
  have hval : (levySwapAutomorphism κ r r') ‘ r = r' := by
    rw [levySwapAutomorphism_value hr]
    exact levySwapCondition_self (levyCollapse_isFunction hr) (levyCollapse_isFunction hr') hdom
  have hΘb0 : (booleanLift (levyCollapse κ) (levyOrder κ) (levySwapAutomorphism κ r r')) ‘
      (coneRegular (levyCollapse κ) (levyOrder κ) r) =
      coneRegular (levyCollapse κ) (levyOrder κ) r' := by
    rw [booleanLift_coneRegular hπ hr, hval]
  obtain ⟨g, hg, hcl⟩ :=
    coneImage_of_automorphism_restriction_negation (levyCollapse_poset κ).1 hΘ hb0
  rw [hΘb0] at hg hcl
  refine ⟨g, hg, fun a ha ↦ ?_⟩
  obtain ⟨k, -, σ, -, rfl⟩ := (mem_supportValuesBase_iff _ _ _ _ _ _).mp ha
  refine hcl _ (booleanValueBase_regular (levyCollapse_poset κ).1 _ _) (fun haB ↦ ?_)
  rw [booleanLift_value haB]
  exact hfix _ ha

end LevyCones

/-! ### The two cone isomorphisms from agreement below `ξ` -/

/-- Both cone isomorphisms with their support clauses, for two conditions of equal domain that
agree at every coordinate of `ω × ξ` where both are defined, under the assumption that every base
support value of `E` is the regular closure of a set of conditions with domains inside `ω × ξ`.
The agreement hypothesis and the localization hypothesis together give the fixed-point
hypothesis of `levy_cone_isomorphism_support_of_fixed` and
`levy_complement_cone_isomorphism_support_of_fixed`. -/
theorem levy_complement_cone_isomorphism_support_of_agree {κ ξ r r' E : V}
    (hr : r ∈ levyCollapse κ) (hr' : r' ∈ levyCollapse κ) (hdom : domain r = domain r')
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)
    (hloc : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
        ((ω : V) ×ˢ (ω : V)) E,
      ∃ X, X ⊆ levyCollapse κ ∧ (∀ s ∈ X, domain s ⊆ (ω : V) ×ˢ ξ) ∧
        a = forcingClosure (levyCollapse κ) (levyOrder κ) X) :
    (∃ g, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r)))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r))))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r')))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r')))) g ∧
      ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
          ((ω : V) ×ˢ (ω : V)) E,
        coneImage (levyCollapse κ) (levyOrder κ)
            (forcingNegation (levyCollapse κ) (levyOrder κ)
              (coneRegular (levyCollapse κ) (levyOrder κ) r)) g
            (a ∩ forcingNegation (levyCollapse κ) (levyOrder κ)
              (coneRegular (levyCollapse κ) (levyOrder κ) r)) =
          a ∩ forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r')) ∧
    (∃ f, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) r))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) r)))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) r'))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) r'))) f ∧
      ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
          ((ω : V) ×ˢ (ω : V)) E,
        coneImage (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r) f
            (a ∩ coneRegular (levyCollapse κ) (levyOrder κ) r) =
          a ∩ coneRegular (levyCollapse κ) (levyOrder κ) r') := by
  have hfix : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
      ((ω : V) ×ˢ (ω : V)) E, imageAction (levySwapAutomorphism κ r r') a = a := by
    intro a ha
    obtain ⟨X, hX, hXdom, rfl⟩ := hloc a ha
    exact (levySwap_imageAction_forcingClosure hr hr' hagree hX hXdom).2
  exact ⟨levy_complement_cone_isomorphism_support_of_fixed hr hr' hdom hfix,
    levy_cone_isomorphism_support_of_fixed hr hr' hdom hfix⟩

end ZFVP
