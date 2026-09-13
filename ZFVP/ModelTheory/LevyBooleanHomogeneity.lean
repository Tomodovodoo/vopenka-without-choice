import ZFVP.ModelTheory.LevyComplementCone

/-! How far the cones of the Boolean completion of the Levy collapse are alike.

The transfer step for Karagila-Schilhan Lemma 9.3 needs, for two nonzero conditions `a`, `b` of
the Boolean completion `B` of `Coll(ω, <κ)`, an isomorphism of the cone `B|¬a` with the cone
`B|¬b`. The clean sufficient statement is homogeneity of `B`: `B|a ≅ B` for every nonzero `a`.
This file records what the repository proves towards that and where the proof stops.

What is proved here.

* For a condition `p` of the collapse the cone of `B` below `coneRegular p` is isomorphic to all
  of `B` (`levy_forcingCone_coneRegular_isomorphic`). This is
  `levy_booleanCone_isomorphic` of `LevyConeIsomorphism.lean` restated in the `forcingCone`
  vocabulary, the two descriptions of that cone being the same set
  (`booleanCone_eq_forcingCone`). No hypothesis on `κ` is used: the coordinate renaming behind
  `levyCollapse_cone_isomorphic` only needs `ω` to be regular.

* Cones of the form `coneRegular p` are dense: every nonzero `a` of `B` has some `coneRegular q`
  below it (`exists_coneRegular_mem_forcingCone`). So below every nonzero `a` there is an element
  whose cone is isomorphic to the whole of `B` (`levy_exists_subcone_isomorphic_completion`), and
  more generally, for nonzero `a` and `b` there is `d ≤ a` with `B|d ≅ B|b`
  (`levy_exists_subcone_isomorphic_cone`). Any two cones therefore embed in each other as cones.

* For conditions `r`, `r'` of the collapse with the same domain, `LevyComplementCone.lean` gives
  the complementary isomorphism `B|¬coneRegular r ≅ B|¬coneRegular r'`. For arbitrary `r`, `r'`
  this is inherited only after extending both to a common domain
  (`levy_exists_extensions_complement_cone_isomorphism`).

What was open here, and where it is now proved.

The section that stood here recorded homogeneity, `B|a ≅ B` for every nonzero `a`, as out of
reach from the material in the repository, and said that a Cantor-Bernstein argument for cones
would fail. Both are now proved elsewhere.

* Homogeneity is `levy_cone_isomorphic_completion` in `LevyConeHomogeneity.lean`, with
  `levy_cone_isomorphic_cone` for the two-cone form the transfer step wants. The proof splits `a`
  and the top of `B` into disjoint pieces whose cones are each isomorphic to `B`, matches the two
  index sets, and glues the piece isomorphisms. It uses neither an absorption theorem below an
  arbitrary Boolean condition nor a uniqueness theorem for the collapse algebra, so the classical
  ingredient named at the end of the old section is not what the proof runs on.

* Cantor-Bernstein for cones is `exists_coneIsomorphism_of_mutual` in
  `BooleanConeCantorBernstein.lean`, with the equivariant form
  `exists_coneIsomorphism_of_mutual_equivariant`: cones that embed in each other as cones are
  isomorphic. This is the theorem of Sikorski and Tarski, and the countable joins of the algebra
  of regular sets are what carry it; the Kinoshita counterexample is for Boolean algebras without
  them and does not apply.

Two observations of the old section stay true and are kept. An automorphism of the collapse poset
cannot carry a condition `r` to one whose domain has a different size, since the conditions above
`r` are exactly its subsets and their number `2^|dom r|` is an order invariant; that is why
`exists_levyAutomorphism_of_domain_eq` carries the domain hypothesis and why
`exists_common_domain_extensions` has to extend first. And `¬coneRegular r` is not the cone
`coneRegular s` of any condition, so `levy_forcingCone_coneRegular_isomorphic` does not apply to
it directly.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The two names of the cone below a regular cone -/

section General

variable {P R p a c : V}

/-- The conditions of the Boolean completion below the regular cone of `p`, described as a subset
of the regular cone, are exactly its cone in the Boolean order. -/
theorem booleanCone_eq_forcingCone (hR : IsForcingPreorder P R) (hp : p ∈ P) :
    booleanCone P R p =
      forcingCone (booleanConditions P R) (booleanOrder P R) (coneRegular P R p) := by
  apply mem_ext
  intro b
  rw [mem_booleanCone_iff, mem_forcingCone_iff, kpair_mem_booleanOrder_iff]
  exact ⟨fun h ↦ ⟨h.1, h.1, coneRegular_mem_booleanConditions hR hp, h.2⟩,
    fun h ↦ ⟨h.1, h.2.2.2⟩⟩

/-! ### Cones of cones -/

/-- Restricting an already restricted order to a smaller set. -/
theorem restrictedOrder_restrictedOrder {A C : V} (h : C ⊆ A) :
    restrictedOrder (restrictedOrder R A) C = restrictedOrder R C := by
  apply mem_ext
  intro z
  unfold restrictedOrder
  rw [mem_inter_iff, mem_inter_iff, mem_inter_iff]
  refine ⟨fun hz ↦ ⟨hz.1.1, hz.2⟩, fun hz ↦ ⟨⟨hz.1, ?_⟩, hz.2⟩⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp hz.2
  exact kpair_mem_iff.mpr ⟨h x hx, h y hy⟩

/-- The cone of a cone is a cone: below an element `c` of the cone of `a`, the two cones agree. -/
theorem forcingCone_forcingCone (hR : IsForcingPreorder P R) (ha : a ∈ P)
    (hc : c ∈ forcingCone P R a) :
    forcingCone (forcingCone P R a) (restrictedOrder R (forcingCone P R a)) c =
      forcingCone P R c := by
  obtain ⟨hcP, hca⟩ := (mem_forcingCone_iff _ _ _ _).mp hc
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨hxa, hxc⟩ := (mem_forcingCone_iff _ _ _ _).mp hx
    exact (mem_forcingCone_iff _ _ _ _).mpr
      ⟨((mem_forcingCone_iff _ _ _ _).mp hxa).1,
        ((kpair_mem_restrictedOrder_iff _ _ _ _).mp hxc).1⟩
  · intro hx
    obtain ⟨hxP, hxc⟩ := (mem_forcingCone_iff _ _ _ _).mp hx
    have hxa : x ∈ forcingCone P R a :=
      (mem_forcingCone_iff _ _ _ _).mpr ⟨hxP, hR.2.2 x hxP c hcP a ha hxc hca⟩
    exact (mem_forcingCone_iff _ _ _ _).mpr
      ⟨hxa, (kpair_mem_restrictedOrder_iff _ _ _ _).mpr ⟨hxc, hxa, hc⟩⟩

/-- The order of the cone of a cone, likewise. -/
theorem restrictedOrder_forcingCone_forcingCone (hR : IsForcingPreorder P R) (ha : a ∈ P)
    (hc : c ∈ forcingCone P R a) :
    restrictedOrder (restrictedOrder R (forcingCone P R a)) (forcingCone P R c) =
      restrictedOrder R (forcingCone P R c) := by
  refine restrictedOrder_restrictedOrder (fun x hx ↦ ?_)
  rw [← forcingCone_forcingCone hR ha hc] at hx
  exact ((mem_forcingCone_iff _ _ _ _).mp hx).1

/-! ### Cones under an isomorphism -/

/-- A forcing isomorphism restricts to an isomorphism of the cone of a condition with the cone of
its image. -/
theorem exists_coneIsomorphism_of_isomorphism {Q S f : V} (hf : IsForcingIsomorphism P R Q S f)
    (hp : p ∈ P) :
    ∃ g, IsForcingIsomorphism (forcingCone P R p) (restrictedOrder R (forcingCone P R p))
      (forcingCone Q S (f ‘ p)) (restrictedOrder S (forcingCone Q S (f ‘ p))) g := by
  have : IsFunction f := IsFunction.of_mem hf.1
  have hi := isForcingIsomorphism_inverse hf
  have hfp : f ‘ p ∈ Q := function_value_mem hf.1 hp
  have hFP : ∀ x ∈ forcingCone P R p, f ‘ x ∈ forcingCone Q S (f ‘ p) := by
    intro x hx
    obtain ⟨hxP, hxp⟩ := (mem_forcingCone_iff _ _ _ _).mp hx
    exact (mem_forcingCone_iff _ _ _ _).mpr
      ⟨function_value_mem hf.1 hxP, (hf.2.2.2 x hxP p hp).mp hxp⟩
  have hGQ : ∀ y ∈ forcingCone Q S (f ‘ p), (converseGraph f) ‘ y ∈ forcingCone P R p := by
    intro y hy
    obtain ⟨hyQ, hyp⟩ := (mem_forcingCone_iff _ _ _ _).mp hy
    have h := (hi.2.2.2 y hyQ (f ‘ p) hfp).mp hyp
    rw [converseGraph_value_value hf.1 hf.2.1 hp] at h
    exact (mem_forcingCone_iff _ _ _ _).mpr ⟨function_value_mem hi.1 hyQ, h⟩
  refine ⟨definableGraph (forcingCone P R p) (fun x ↦ f ‘ x) (by definability),
    isForcingIsomorphism_of_inverse (fun x ↦ f ‘ x) (fun y ↦ (converseGraph f) ‘ y)
      (by definability) hFP hGQ ?_ ?_ ?_⟩
  · intro x hx
    exact converseGraph_value_value hf.1 hf.2.1 ((mem_forcingCone_iff _ _ _ _).mp hx).1
  · intro y hy
    exact value_converseGraph_value hf.1 hf.2.1
      (hf.2.2.1.symm ▸ ((mem_forcingCone_iff _ _ _ _).mp hy).1)
  · intro x hx y hy
    have hxP := ((mem_forcingCone_iff _ _ _ _).mp hx).1
    have hyP := ((mem_forcingCone_iff _ _ _ _).mp hy).1
    rw [kpair_mem_restrictedOrder_iff, kpair_mem_restrictedOrder_iff]
    simp only [hx, hy, hFP x hx, hFP y hy, and_true]
    exact hf.2.2.2 x hxP y hyP

/-! ### Cones of conditions are dense in the Boolean completion -/

/-- Every nonzero condition of the Boolean completion has the regular cone of a condition of the
poset below it. -/
theorem exists_coneRegular_subset (hR : IsForcingPreorder P R)
    (ha : a ∈ booleanConditions P R) : ∃ q ∈ P, coneRegular P R q ⊆ a := by
  obtain ⟨hareg, q, hq⟩ := (mem_booleanConditions_iff P R a).mp ha
  exact ⟨q, hareg.1 q hq, coneRegular_subset_of_mem hR hareg hq⟩

/-- The same, in the cone vocabulary: the regular cones of conditions are dense in the Boolean
completion. -/
theorem exists_coneRegular_mem_forcingCone (hR : IsForcingPreorder P R)
    (ha : a ∈ booleanConditions P R) :
    ∃ q ∈ P, coneRegular P R q ∈
      forcingCone (booleanConditions P R) (booleanOrder P R) a := by
  obtain ⟨q, hq, hsub⟩ := exists_coneRegular_subset hR ha
  exact ⟨q, hq, (mem_forcingCone_iff _ _ _ _).mpr
    ⟨coneRegular_mem_booleanConditions hR hq, (kpair_mem_booleanOrder_iff _ _ _ _).mpr
      ⟨coneRegular_mem_booleanConditions hR hq, ha, hsub⟩⟩⟩

end General

/-! ### The Levy collapse: cones of conditions -/

section Levy

variable {κ a b p r r' : V}

/-- The cone of the Boolean completion of `Coll(ω, <κ)` below the regular cone of a condition `p`
is isomorphic to the whole completion. This is `levy_booleanCone_isomorphic` in the `forcingCone`
vocabulary. No hypothesis on `κ`. -/
theorem levy_forcingCone_coneRegular_isomorphic (hp : p ∈ levyCollapse κ) :
    ∃ F, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) p))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) p)))
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) F := by
  rw [← booleanCone_eq_forcingCone (levyCollapse_poset κ).1 hp]
  exact levy_booleanCone_isomorphic hp

/-- Below every nonzero condition `a` of the Boolean completion of `Coll(ω, <κ)` there is a
condition `c` whose cone, computed inside the cone of `a` or inside the whole completion, is the
same and is isomorphic to the whole completion. This does not say `B|a ≅ B`: the isomorphic cone
sits strictly below `a` in general. -/
theorem levy_exists_subcone_isomorphic_completion
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) :
    ∃ c ∈ forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) a,
      forcingCone
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) a)
          (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
            (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
              (booleanOrder (levyCollapse κ) (levyOrder κ)) a)) c =
        forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) c ∧
      restrictedOrder
          (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
            (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
              (booleanOrder (levyCollapse κ) (levyOrder κ)) a))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) c) =
        restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) c) ∧
      ∃ F, IsForcingIsomorphism
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) c)
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) c))
        (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) F := by
  obtain ⟨q, hq, hmem⟩ := exists_coneRegular_mem_forcingCone (levyCollapse_poset κ).1 ha
  exact ⟨coneRegular (levyCollapse κ) (levyOrder κ) q, hmem,
    forcingCone_forcingCone (booleanOrder_poset _ _).1 ha hmem,
    restrictedOrder_forcingCone_forcingCone (booleanOrder_poset _ _).1 ha hmem,
    levy_forcingCone_coneRegular_isomorphic hq⟩

/-- For nonzero conditions `a` and `b` of the Boolean completion of `Coll(ω, <κ)` there is a
condition `d` below `a` whose cone is isomorphic to the cone of `b`. So any two cones embed in
each other as cones. Taking `b` to be the top gives an isomorphic copy of the whole completion
below `a`. The isomorphic copy is a cone below `a`, not the cone of `a`, which is what
homogeneity would need. -/
theorem levy_exists_subcone_isomorphic_cone
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hb : b ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) :
    ∃ d ∈ forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) a,
      ∃ g, IsForcingIsomorphism
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) d)
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) d))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) b)
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) b)) g := by
  obtain ⟨c, hc, hcone, hord, F, hF⟩ := levy_exists_subcone_isomorphic_completion ha
  have hB := (booleanOrder_poset (levyCollapse κ) (levyOrder κ)).1
  have hi := isForcingIsomorphism_inverse hF
  have : IsFunction (converseGraph F) := IsFunction.of_mem hi.1
  set d := (converseGraph F) ‘ b with hd
  have hdc : d ∈ forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) c := function_value_mem hi.1 hb
  obtain ⟨hcB, hca⟩ := (mem_forcingCone_iff _ _ _ _).mp hc
  obtain ⟨hdB, hdc'⟩ := (mem_forcingCone_iff _ _ _ _).mp hdc
  refine ⟨d, (mem_forcingCone_iff _ _ _ _).mpr ⟨hdB, hB.2.2 d hdB c hcB a ha hdc' hca⟩, ?_⟩
  obtain ⟨g, hg⟩ := exists_coneIsomorphism_of_isomorphism hi hb
  rw [← hd, forcingCone_forcingCone hB hcB hdc,
    restrictedOrder_forcingCone_forcingCone hB hcB hdc] at hg
  exact ⟨converseGraph g, isForcingIsomorphism_inverse hg⟩

/-- The complementary cones for two conditions of the collapse, after matching their shapes: any
two conditions have extensions whose complementary cones are isomorphic. Extension is superset,
so the regular cone shrinks and the complementary cone grows; this does not give an isomorphism
of the complementary cones of `r` and `r'` themselves. -/
theorem levy_exists_extensions_complement_cone_isomorphism (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) :
    ∃ r₁ r₁', r₁ ∈ levyCollapse κ ∧ r₁' ∈ levyCollapse κ ∧ r ⊆ r₁ ∧ r' ⊆ r₁' ∧
      ∃ g, IsForcingIsomorphism
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r₁)))
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ))
            (forcingNegation (levyCollapse κ) (levyOrder κ)
              (coneRegular (levyCollapse κ) (levyOrder κ) r₁))))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r₁')))
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ))
            (forcingNegation (levyCollapse κ) (levyOrder κ)
              (coneRegular (levyCollapse κ) (levyOrder κ) r₁')))) g := by
  obtain ⟨r₁, r₁', h1, h2, hs1, hs2, hdom⟩ := exists_common_domain_extensions hr hr'
  exact ⟨r₁, r₁', h1, h2, hs1, hs2,
    levy_complement_cone_isomorphism_of_domain_eq h1 h2 hdom⟩

end Levy

end ZFVP
