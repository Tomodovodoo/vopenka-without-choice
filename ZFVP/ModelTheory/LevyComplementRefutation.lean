import ZFVP.ModelTheory.LevyConeComplementHomogeneity
import ZFVP.ModelTheory.LevyBooleanHomogeneity

/-! The complement cone hypothesis of `LevyConeComplementHomogeneity` is false for the Levy
collapse, so the export `solovay_corollary_of_complement` is vacuous.

`ForcingContext.ComplementConeIsomorphic A E` quantifies over *all* pairs `b0`, `c0` of Boolean
conditions and all isomorphisms `f : B|b0 ≅ B|c0` fixing the base support values of `E`
relatively. It asks for an isomorphism of the complementary cones `B|¬b0 ≅ B|¬c0`. Nothing in the
statement ties `¬b0` to `¬c0`, and that is where it breaks: take

* `E := range ∅ = ∅`, so `supportValuesBase P R P (ω ×ˢ ω) E` is empty and both support clauses
  are vacuous;
* `b0 := P`, the top of the completion, for which `forcingNegation P R P = ∅` and the cone
  `B|¬b0` is therefore empty;
* `c0 := coneRegular P R p` for a one point condition `p` of `Coll(ω, <κ)`. The condition with the
  same coordinate and a different value is not in `coneRegular P R p`, so `forcingNegation P R c0`
  is nonempty and the cone `B|¬c0` is nonempty.

The isomorphism `f` that the hypothesis needs exists: `levy_forcingCone_coneRegular_isomorphic`
gives `B|coneRegular p ≅ B`, its inverse is `B ≅ B|coneRegular p`, and `B` is the cone of the top
(`forcingCone_booleanOrder_top`, `restrictedOrder_booleanOrder_self`). An `IsForcingIsomorphism`
carries `range f = Q`, so it cannot map an empty poset onto a nonempty one. That contradiction is
`not_levy_complementConeIsomorphic` and `not_complementConeIsomorphic_empty_support`.

The refutation uses no hypothesis on `κ` beyond `IsOrdinal κ` and `ω ∈ κ`, and no hypothesis on
the generic filter. So every consequence of `ComplementConeIsomorphic` in
`LevyConeComplementHomogeneity`, in particular `solovay_corollary_of_complement`, is proved from a
false assumption and carries no information.

What a usable form of the hypothesis has to add. Two side conditions are necessary, and both fail
here for the pair `(P, coneRegular P R p)`.

* Matching complements: `forcingNegation b0 = ∅ ↔ forcingNegation c0 = ∅`. This is necessary
  because an isomorphism of the complementary cones already forces it
  (`forcingNegation_eq_empty_iff_of_complementIsomorphism`). It is exactly what the counterexample
  violates, since `b0` is the top and `c0` is not.
* Matching traces: `∀ a ∈ supportValuesBase …, a ∩ forcingNegation b0 = ∅ ↔ a ∩ forcingNegation c0
  = ∅`. The positive support clause already gives one half of the corresponding statement for
  `b0`, `c0` themselves (`inter_eq_empty_of_support_clause`), and the conclusion's support clause
  gives the same for the complements, so a hypothesis that omits it asks for more than its own
  conclusion allows.

Adding both is still not enough to make the statement true, but without them it is refutable by
the pair above. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Cones of the Boolean completion at the top and at zero -/

/-- The cone of the Boolean completion below the top condition is the whole completion. -/
theorem forcingCone_booleanOrder_top {P R : V} (hP : ∃ p, p ∈ P) :
    forcingCone (booleanConditions P R) (booleanOrder P R) P = booleanConditions P R := by
  apply mem_ext
  intro A
  rw [mem_forcingCone_iff, kpair_mem_booleanOrder_iff]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  exact ⟨h, top_mem_booleanConditions hP, ((mem_booleanConditions_iff P R A).mp h).1.1⟩

/-- Restricting the Boolean order to all of the Boolean conditions changes nothing. -/
theorem restrictedOrder_booleanOrder_self (P R : V) :
    restrictedOrder (booleanOrder P R) (booleanConditions P R) = booleanOrder P R := by
  unfold restrictedOrder
  apply SetTheory.subset_antisymm (fun z hz ↦ (mem_inter_iff.mp hz).1)
  intro z hz
  exact mem_inter_iff.mpr ⟨hz, (show z ∈ booleanOrder P R ↔ _ from mem_sep_iff).mp hz |>.1⟩

/-- The cone of the Boolean completion below zero is empty: zero is not a Boolean condition. -/
theorem forcingCone_booleanOrder_empty (P R : V) :
    forcingCone (booleanConditions P R) (booleanOrder P R) (∅ : V) = (∅ : V) := by
  apply mem_ext
  intro A
  simp only [not_mem_empty, iff_false]
  intro h
  obtain ⟨-, hle⟩ := (mem_forcingCone_iff _ _ _ _).mp h
  obtain ⟨-, hemp, -⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hle
  obtain ⟨-, x, hx⟩ := (mem_booleanConditions_iff P R (∅ : V)).mp hemp
  exact not_mem_empty hx

/-- The cone of a regular set inside the Boolean completion is empty exactly when the set is. -/
theorem forcingCone_eq_empty_iff_regular {P R n : V} (hn : IsForcingRegular P R n) :
    forcingCone (booleanConditions P R) (booleanOrder P R) n = (∅ : V) ↔ n = (∅ : V) := by
  constructor
  · intro h
    apply mem_ext
    intro z
    simp only [not_mem_empty, iff_false]
    intro hz
    have hnB : n ∈ booleanConditions P R := (mem_booleanConditions_iff _ _ _).mpr ⟨hn, z, hz⟩
    have hself : n ∈ forcingCone (booleanConditions P R) (booleanOrder P R) n :=
      (mem_forcingCone_iff _ _ _ _).mpr ⟨hnB,
        (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hnB, hnB, subset_refl n⟩⟩
    rw [h] at hself
    exact not_mem_empty hself
  · rintro rfl
    exact forcingCone_booleanOrder_empty P R

/-! ### Forcing isomorphisms and the empty poset -/

/-- A forcing isomorphism out of the empty poset has empty target: its range is the target. -/
theorem isForcingIsomorphism_target_eq_empty {S Q T f : V}
    (h : IsForcingIsomorphism (∅ : V) S Q T f) : Q = (∅ : V) := by
  obtain ⟨hfun, -, hrange, -⟩ := h
  apply mem_ext
  intro x
  simp only [not_mem_empty, iff_false]
  intro hx
  rw [← hrange] at hx
  obtain ⟨y, hy⟩ := mem_range_iff.mp hx
  have hdom := mem_domain_of_kpair_mem hy
  rw [domain_eq_of_mem_function hfun] at hdom
  exact not_mem_empty hdom

/-- A forcing isomorphism into the empty poset has empty source. -/
theorem isForcingIsomorphism_source_eq_empty {P R T f : V}
    (h : IsForcingIsomorphism P R (∅ : V) T f) : P = (∅ : V) := by
  apply mem_ext
  intro x
  simp only [not_mem_empty, iff_false]
  intro hx
  exact not_mem_empty (function_value_mem h.1 hx)

/-- There is no forcing isomorphism from the empty poset onto a nonempty one. -/
theorem not_isForcingIsomorphism_of_empty_source {S Q T f : V} (hQ : ∃ x, x ∈ Q) :
    ¬ IsForcingIsomorphism (∅ : V) S Q T f := by
  intro h
  obtain ⟨x, hx⟩ := hQ
  rw [isForcingIsomorphism_target_eq_empty h] at hx
  exact not_mem_empty hx

/-! ### The two necessary side conditions -/

/-- An isomorphism of the complementary cones forces the two negations to be zero together. This
is the first side condition that `ComplementConeIsomorphic` omits, and the one the counterexample
below violates. -/
theorem forcingNegation_eq_empty_iff_of_complementIsomorphism {P R b0 c0 g : V}
    (hR : IsForcingPreorder P R) (hb0 : b0 ∈ booleanConditions P R)
    (hc0 : c0 ∈ booleanConditions P R)
    (hg : IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R b0))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R b0)))
      (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R c0))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R c0))) g) :
    forcingNegation P R b0 = (∅ : V) ↔ forcingNegation P R c0 = (∅ : V) := by
  have hnb : IsForcingRegular P R (forcingNegation P R b0) :=
    forcingNegation_regular hR (booleanConditions_regular hb0).2.1
  have hnc : IsForcingRegular P R (forcingNegation P R c0) :=
    forcingNegation_regular hR (booleanConditions_regular hc0).2.1
  rw [← forcingCone_eq_empty_iff_regular hnb, ← forcingCone_eq_empty_iff_regular hnc]
  constructor
  · intro h
    rw [h] at hg
    exact isForcingIsomorphism_target_eq_empty hg
  · intro h
    rw [h] at hg
    exact isForcingIsomorphism_source_eq_empty hg

/-- The support clause in `coneImage` form carries empty relative traces from `b0` to `c0`. This
is the easy half of the second side condition, the matching of traces. -/
theorem inter_eq_empty_of_support_clause {P R b0 c0 f a : V}
    (h : coneImage P R b0 f (a ∩ b0) = a ∩ c0) (ha : a ∩ b0 = (∅ : V)) : a ∩ c0 = (∅ : V) := by
  rw [← h, ha, coneImage_empty]

/-! ### The refutation -/

namespace ForcingContext

/-- The complement cone hypothesis fails whenever the support values of `E` are empty and the
poset has a condition `p` whose regular cone misses some condition `q`, provided the cone below
`coneRegular p` is isomorphic to the whole completion.

The pair of conditions used is the top `A.P` and `coneRegular A.P A.R p`. The isomorphism of the
positive cones is the inverse of the given one, the support clauses are vacuous, and the
conclusion would give an isomorphism from the empty cone below `¬A.P` onto the nonempty cone below
`¬coneRegular A.P A.R p`. -/
theorem not_complementConeIsomorphic_of_witness (A : ForcingContext V) {E p q : V}
    (hE : ∀ a, a ∉ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) E)
    (hp : p ∈ A.P) (hq : q ∈ A.P) (hqp : q ∉ coneRegular A.P A.R p)
    (hiso : ∃ F, IsForcingIsomorphism
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) (coneRegular A.P A.R p))
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R p)))
      (booleanConditions A.P A.R) (booleanOrder A.P A.R) F) :
    ¬ A.ComplementConeIsomorphic E := by
  intro hcomp
  have hPne : ∃ x, x ∈ A.P := ⟨A.one, A.top.1⟩
  have hb0 : A.P ∈ booleanConditions A.P A.R := top_mem_booleanConditions hPne
  have hc0 : coneRegular A.P A.R p ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hp
  obtain ⟨F, hF⟩ := hiso
  have hf : IsForcingIsomorphism
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P))
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) (coneRegular A.P A.R p))
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R p))) (converseGraph F) := by
    rw [forcingCone_booleanOrder_top hPne, restrictedOrder_booleanOrder_self]
    exact isForcingIsomorphism_inverse hF
  obtain ⟨g, hg, -⟩ := hcomp _ hb0 _ hc0 _ hf (fun a ha ↦ absurd ha (hE a))
  rw [forcingNegation_top A.order, forcingCone_booleanOrder_empty] at hg
  -- the negation of the regular cone of `p` is nonzero, so its cone is nonempty
  obtain ⟨w, hw, -⟩ :=
    exists_forcingNegation_of_not_mem hq hqp (coneRegular_regular A.order p).2.2
  have hnB : forcingNegation A.P A.R (coneRegular A.P A.R p) ∈ booleanConditions A.P A.R :=
    (mem_booleanConditions_iff _ _ _).mpr
      ⟨forcingNegation_regular A.order (coneRegular_regular A.order p).2.1, w, hw⟩
  have hne : ∃ x, x ∈ forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
      (forcingNegation A.P A.R (coneRegular A.P A.R p)) :=
    ⟨forcingNegation A.P A.R (coneRegular A.P A.R p),
      (mem_forcingCone_iff _ _ _ _).mpr ⟨hnB,
        (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hnB, hnB, subset_refl _⟩⟩⟩
  exact not_isForcingIsomorphism_of_empty_source hne hg

end ForcingContext

/-! ### The base support values of the empty name set -/

/-- The empty set has no base support values. -/
theorem not_mem_supportValuesBase_range_empty (P R one K a : V) :
    a ∉ supportValuesBase P R one K (range (∅ : V)) := by
  intro ha
  obtain ⟨-, -, σ, hσ, -⟩ := (mem_supportValuesBase_iff _ _ _ _ _ _).mp ha
  obtain ⟨x, hx⟩ := mem_range_iff.mp hσ
  exact not_mem_empty hx

/-! ### The Levy witness: two incompatible one point conditions -/

section Levy

variable {κ : V} [IsOrdinal κ]

/-- The condition of `Coll(ω, <κ)` sending the row `⟨0, ω⟩` to the value `v`. -/
noncomputable def levyRowPoint (v : V) : V := insert ⟨⟨(∅ : V), (ω : V)⟩ₖ, v⟩ₖ (∅ : V)

theorem levyRowPoint_mem {v : V} (hω : (ω : V) ∈ κ) (hv : v ∈ (ω : V)) :
    levyRowPoint v ∈ levyCollapse κ :=
  levyCollapse_insert (empty_mem_levyCollapse κ) empty_mem_ω hω hv (fun _ h ↦ not_mem_empty h)

theorem kpair_mem_levyRowPoint (v : V) : ⟨⟨(∅ : V), (ω : V)⟩ₖ, v⟩ₖ ∈ levyRowPoint v :=
  mem_insert.mpr (Or.inl rfl)

/-- The one point condition with value `1` is not in the regular cone of the one point condition
with value `0`: a common extension would be a partial function taking two values at the row
`⟨0, ω⟩`. -/
theorem levyRowPoint_not_mem_coneRegular (hω : (ω : V) ∈ κ) :
    levyRowPoint (succ (∅ : V)) ∉
      coneRegular (levyCollapse κ) (levyOrder κ) (levyRowPoint (∅ : V)) := by
  intro hmem
  have hq : levyRowPoint (succ (∅ : V)) ∈ levyCollapse κ :=
    levyRowPoint_mem hω (ω_succ_closed empty_mem_ω)
  obtain ⟨-, hh⟩ := mem_coneRegular_iff.mp hmem
  obtain ⟨s, hsP, hsp, hsq⟩ := hh _ hq ((levyCollapse_poset κ).1.2.1 _ hq)
  have hps : levyRowPoint (∅ : V) ⊆ s :=
    ((pair_mem_reverseInclusionOrder _ _ _).mp hsp).2.2
  have hqs : levyRowPoint (succ (∅ : V)) ⊆ s :=
    ((pair_mem_reverseInclusionOrder _ _ _).mp hsq).2.2
  have hfun : IsFunction s :=
    ((mem_finitePartialFunctions _ _ s).mp (levyCollapse_finitePartialFunction hsP)).2.1
  have h0 : ⟨⟨(∅ : V), (ω : V)⟩ₖ, (∅ : V)⟩ₖ ∈ s := hps _ (kpair_mem_levyRowPoint _)
  have h1 : ⟨⟨(∅ : V), (ω : V)⟩ₖ, succ (∅ : V)⟩ₖ ∈ s := hqs _ (kpair_mem_levyRowPoint _)
  have hval : (∅ : V) = succ (∅ : V) := IsFunction.unique h0 h1
  have hmem : (∅ : V) ∈ (∅ : V) := by
    have h2 := mem_succ_self (∅ : V)
    rwa [← hval] at h2
  exact not_mem_empty hmem

/-- The complement cone hypothesis of `LevyConeComplementHomogeneity` is false for the Levy
collapse and the empty set of names, for every forcing context over `Coll(ω, <κ)`. -/
theorem not_levy_complementConeIsomorphic (A : ForcingContext V) (hAP : A.P = levyCollapse κ)
    (hAR : A.R = levyOrder κ) (hω : (ω : V) ∈ κ) :
    ¬ A.ComplementConeIsomorphic (range (∅ : V)) := by
  refine A.not_complementConeIsomorphic_of_witness (p := levyRowPoint (∅ : V))
    (q := levyRowPoint (succ (∅ : V))) (not_mem_supportValuesBase_range_empty _ _ _ _)
    ?_ ?_ ?_ ?_
  · rw [hAP]; exact levyRowPoint_mem hω empty_mem_ω
  · rw [hAP]; exact levyRowPoint_mem hω (ω_succ_closed empty_mem_ω)
  · rw [hAP, hAR]; exact levyRowPoint_not_mem_coneRegular hω
  · rw [hAP, hAR]; exact levy_forcingCone_coneRegular_isomorphic (levyRowPoint_mem hω empty_mem_ω)

/-- The refutation for the Levy context itself: the hypothesis of
`solovay_corollary_of_complement` fails at the empty support sequence, so that corollary is
vacuous. -/
theorem not_complementConeIsomorphic_empty_support (hω : (ω : V) ∈ κ) {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G) :
    ¬ (levyContext κ hG).ComplementConeIsomorphic (range (∅ : V)) :=
  not_levy_complementConeIsomorphic (levyContext κ hG) rfl rfl hω

/-- The hypothesis of `solovay_corollary_of_complement`, asked of every `range s`, is false. -/
theorem not_forall_complementConeIsomorphic (hω : (ω : V) ∈ κ) {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G) :
    ¬ ∀ s : V, (levyContext κ hG).ComplementConeIsomorphic (range s) :=
  fun h ↦ not_complementConeIsomorphic_empty_support hω hG (h (∅ : V))

end Levy

end ZFVP
