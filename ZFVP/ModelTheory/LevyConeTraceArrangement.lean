import ZFVP.ModelTheory.LevyConeTraceAlignment
import ZFVP.SetTheory.LevyCollapseSmallSets

/-! How far `ForcingContext.ConeTraceAligned` gets from the cone construction, and what is left.

`ForcingContext.ConeTraceAligned` (`ZFVP/ModelTheory/LevyConeTraceAlignment.lean`) asks, for every
orbit filter `H`, for a pair `b0`, `c0` of Boolean conditions carrying an isomorphism of cones with
the filter clause and the support clause, and in addition the two trace conditions

* `(N1)` `¬b0 = ∅ ↔ ¬c0 = ∅`;
* `(N2)` `a ∩ ¬b0 = ∅ ↔ a ∩ ¬c0 = ∅` for every base support value `a`.

`exists_orbit_cone_isomorphism_support` produces everything except `(N1)` and `(N2)`, with the
condition on the side of the generic already the regular cone `coneRegular r` of a condition
`r ∈ A.G`. This module shrinks that pair and reads off what the two trace conditions become.

* Shrinking. `coneShrink_data`: if `φ` is an isomorphism of the cone below `b0` onto the cone below
  `c0` with the filter clause and the support clause, and `b1 ⊆ b0` is a condition met by the
  generic, then `c1 := φ ‘ b1` is a condition with `A.check c1 ∈ H` and the restricted map
  `coneRestrictMap A.P A.R b1 φ` carries both clauses for the pair `(b1, c1)`. The direction that
  is restricted is the one out of the cone on the side of the generic, that is, the inverse of the
  isomorphism `ψ` that `exists_orbit_cone_isomorphism_support` returns.

* `(N1)`. `forcingNegation_eq_empty_iff` says `¬b = ∅ ↔ b = A.P` for a regular `b`, so `(N1)` for
  the shrunk pair is `b1 = A.P ↔ c1 = A.P`. Both sides are made false at once by a single witness:
  a condition `q` with `q ∈ b0` and `q ∉ b1`. It gives `¬b1 ≠ ∅` directly, and it gives `b1 ≠ b0`,
  hence `c1 = φ ‘ b1 ≠ φ ‘ b0 = c0`, hence `c1 ≠ A.P` because `c1 ⊆ c0 ⊆ A.P`. For the Levy
  collapse such a witness always exists below any condition of the generic filter:
  `levy_exists_generic_extension_witness` picks a row of the column `ω` that `r` does not use,
  meets the dense set of conditions that do use it, and takes a common extension in the filter.

* `(N2)`. `inter_forcingNegation_eq_empty_iff` turns `a ∩ ¬b1 = ∅` into `a ⊆ b1`, so `(N2)` reads
  `a ⊆ b1 ↔ a ⊆ c1`. What the support clause gives on its own is the trace equivalence
  `a ∩ b1 = ∅ ↔ a ∩ c1 = ∅` (`inter_eq_empty_iff_of_coneImage`); the same equivalence at the
  negation of `a`, which is again in the base support algebra, reads `b1 ⊆ a ↔ c1 ⊆ a`. Both are
  the dual of what `(N2)` asks, and `(N2)` does not follow from them. Nor does the implication
  `a ⊆ c1 → b1 ⊆ a`: take `b0 = c0 = b1 = A.P` and `φ` the identity, so that `c1 = A.P` as well;
  the support clause holds for every `a`, every `a` is below `c1`, and `b1 ⊆ a` fails at every `a`
  other than the top.

  What is proved here is `(N2)` at every support value that the shrunk condition misses or that is
  the top: `coneTrace_of_inter_empty` and `coneTrace_of_eq_top`. `ForcingContext.NoSupportValueBelow`
  packages that case distinction together with the witness for `(N1)`, and
  `coneTraceAligned_of_noSupportValueBelow` derives `ConeTraceAligned` from it. Its last clause,
  that every base support value is either the top or disjoint from `coneRegular r₁`, is the open
  residue. It is one condition deciding every base support value at once, and the base support
  values are indexed by `(ω ×ˢ ω) ×ˢ range s`, which is infinite, so it is not a density statement
  about a single value.

* What is dense. `levy_exists_extension_not_subset_coneRegular` proves the density half for one
  support value at a time, in the weaker form that is actually dense: for a nonempty `a ⊆ P` and
  any `r` there is `r₁ ⊇ r` with `¬ (a ⊆ coneRegular r₁)`. The proof takes a condition `p ∈ a`, a
  row of the column `ω` used by neither `p` nor `r`, and puts a value there in `r₁`; then the
  extension of `p` that disagrees at that row witnesses `p ∉ coneRegular r₁`. Note that the
  disjointness clause `a ∩ coneRegular r₁ = ∅` used above is not dense in this way: every condition
  of a nonzero regular `a` has its own cone inside `a`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Regular cones, negations and traces -/

section Regular

variable {P R : V}

/-- A condition below `p` is in the regular cone of `p`. -/
theorem mem_coneRegular_of_le (hR : IsForcingPreorder P R) {p q : V} (hp : p ∈ P) (hq : q ∈ P)
    (hqp : ⟨q, p⟩ₖ ∈ R) : q ∈ coneRegular P R p :=
  mem_coneRegular_iff.mpr ⟨hq, fun t ht htq ↦ ⟨t, ht, hR.2.2 t ht q hq p hp htq hqp,
    hR.2.1 t ht⟩⟩

/-- Regular cones shrink as conditions grow: if `q` is below `p` then the cone of `q` is inside the
cone of `p`. -/
theorem coneRegular_subset_coneRegular (hR : IsForcingPreorder P R) {p q : V} (hp : p ∈ P)
    (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) : coneRegular P R q ⊆ coneRegular P R p :=
  coneRegular_subset_of_mem hR (coneRegular_regular hR p) (mem_coneRegular_of_le hR hp hq hqp)

/-- The negation of a regular set is empty exactly when the set is everything. -/
theorem forcingNegation_eq_empty_iff (hR : IsForcingPreorder P R) {b : V}
    (hb : IsForcingRegular P R b) : forcingNegation P R b = (∅ : V) ↔ b = P := by
  classical
  constructor
  · intro h
    refine SetTheory.subset_antisymm hb.1 (fun p hp ↦ ?_)
    refine hb.2.2 p hp (fun q hq hqp ↦ ?_)
    by_contra hno
    have hqn : q ∈ forcingNegation P R b := by
      refine (mem_forcingNegation_iff _ _ _ _).mpr ⟨hq, fun t ht htq ↦ ?_⟩
      intro htb
      exact hno ⟨t, htb, htq⟩
    rw [h] at hqn
    exact not_mem_empty hqn
  · rintro rfl
    exact forcingNegation_top hR

/-- The negation of a regular set is nonempty as soon as some condition is outside it. -/
theorem forcingNegation_ne_empty_of_not_mem (hR : IsForcingPreorder P R) {b q : V}
    (hb : IsForcingRegular P R b) (hq : q ∈ P) (hqb : q ∉ b) :
    forcingNegation P R b ≠ (∅ : V) := by
  intro h
  rw [forcingNegation_eq_empty_iff hR hb] at h
  exact hqb (h ▸ hq)

/-- A regular set misses the negation of a regular set exactly when it is below it. -/
theorem inter_forcingNegation_eq_empty_iff (hR : IsForcingPreorder P R) {a b : V}
    (ha : IsForcingRegular P R a) (hb : IsForcingRegular P R b) :
    a ∩ forcingNegation P R b = (∅ : V) ↔ a ⊆ b := by
  have h := subset_forcingNegation_iff (B := forcingNegation P R b) hR ha
    (forcingNegation_subset P R b)
  rw [forcingNegation_negation hR hb] at h
  exact h.symm

end Regular

/-! ### Disagreeing conditions of the Levy collapse -/

section LevyWitness

variable {κ : V} [IsOrdinal κ]

omit [IsOrdinal κ] in
/-- Two conditions of the Levy collapse that take different values at one row are incompatible, so
neither is in the regular cone of the other. -/
theorem levy_not_mem_coneRegular_of_disagree {n γ δ p q : V} (hp : p ∈ levyCollapse κ)
    (hpv : ⟨⟨n, (ω : V)⟩ₖ, γ⟩ₖ ∈ p)
    (hqv : ⟨⟨n, (ω : V)⟩ₖ, δ⟩ₖ ∈ q) (hne : γ ≠ δ) :
    p ∉ coneRegular (levyCollapse κ) (levyOrder κ) q := by
  intro hmem
  obtain ⟨-, hh⟩ := mem_coneRegular_iff.mp hmem
  obtain ⟨s, hsP, hsq, hsp⟩ := hh _ hp ((levyCollapse_poset κ).1.2.1 _ hp)
  have hqs : q ⊆ s := ((pair_mem_reverseInclusionOrder _ _ _).mp hsq).2.2
  have hps : p ⊆ s := ((pair_mem_reverseInclusionOrder _ _ _).mp hsp).2.2
  have hfun : IsFunction s :=
    ((mem_finitePartialFunctions _ _ s).mp (levyCollapse_finitePartialFunction hsP)).2.1
  exact hne (IsFunction.unique (hps _ hpv) (hqs _ hqv))

/-- Below any condition of the generic filter there is a condition of the generic filter whose cone
misses a condition of the cone of the first. The row used is one that `r` leaves free, and the
condition of the filter that fills it comes from the density of the conditions that do.

This is the witness that makes both halves of `(N1)` false at once for the shrunk pair. -/
theorem levy_exists_generic_extension_witness (hω : (ω : V) ∈ κ) {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G) {r : V} (hrG : r ∈ G) :
    ∃ r₁ ∈ G, ⟨r₁, r⟩ₖ ∈ levyOrder κ ∧
      ∃ q ∈ levyCollapse κ, q ∈ coneRegular (levyCollapse κ) (levyOrder κ) r ∧
        q ∉ coneRegular (levyCollapse κ) (levyOrder κ) r₁ := by
  have hr : r ∈ levyCollapse κ := hG.1.1 r hrG
  obtain ⟨n, hn, hnfresh⟩ := internallyFinite_fresh_natural (columnRows_finite (β := (ω : V)) hr)
  have hfresh : ∀ δ, ⟨⟨n, (ω : V)⟩ₖ, δ⟩ₖ ∉ r :=
    fun δ h ↦ hnfresh (mem_sep_iff.mpr ⟨hn, δ, h⟩)
  obtain ⟨r₀, hr₀G, hr₀D⟩ := hG.2 _ (levyColumn_total_dense hω empty_mem_ω hn)
  obtain ⟨-, γ, hγ⟩ := mem_sep_iff.mp hr₀D
  obtain ⟨r₁, hr₁G, hr₁r, hr₁r₀⟩ := hG.1.2.2.2 r hrG r₀ hr₀G
  have hr₁ : r₁ ∈ levyCollapse κ := hG.1.1 r₁ hr₁G
  have hr₀r₁ : r₀ ⊆ r₁ := ((pair_mem_reverseInclusionOrder _ _ _).mp hr₁r₀).2.2
  have hγ₁ : ⟨⟨n, (ω : V)⟩ₖ, γ⟩ₖ ∈ r₁ := hr₀r₁ _ hγ
  have hγω : γ ∈ (ω : V) := levyCollapse_value hr₁ hγ₁
  set q : V := insert ⟨⟨n, (ω : V)⟩ₖ, succ γ⟩ₖ r with hqdef
  have hqP : q ∈ levyCollapse κ :=
    levyCollapse_insert hr hn hω (ω_succ_closed hγω) hfresh
  have hrq : r ⊆ q := fun z hz ↦ mem_insert.mpr (Or.inr hz)
  have hqr : ⟨q, r⟩ₖ ∈ levyOrder κ :=
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hqP, hr, hrq⟩
  have hne : succ γ ≠ γ := by
    intro h
    have hmem := mem_succ_self γ
    rw [h] at hmem
    exact mem_irrefl γ hmem
  refine ⟨r₁, hr₁G, hr₁r, q, hqP,
    mem_coneRegular_of_le (levyCollapse_poset κ).1 hr hqP hqr, ?_⟩
  exact levy_not_mem_coneRegular_of_disagree hqP (mem_insert.mpr (Or.inl rfl)) hγ₁ hne

/-- The density half for a single regular set: below any condition there is an extension whose cone
does not contain all of a nonempty `a ⊆ P`. The row used is one that neither `r` nor a chosen
condition of `a` uses. -/
theorem levy_exists_extension_not_subset_coneRegular (hω : (ω : V) ∈ κ) {a r : V}
    (hr : r ∈ levyCollapse κ) (ha : a ⊆ levyCollapse κ) (hane : ∃ x, x ∈ a) :
    ∃ r₁ ∈ levyCollapse κ, r ⊆ r₁ ∧
      ¬ (a ⊆ coneRegular (levyCollapse κ) (levyOrder κ) r₁) := by
  obtain ⟨p, hpa⟩ := hane
  have hp : p ∈ levyCollapse κ := ha p hpa
  obtain ⟨n, hn, hnfresh⟩ := internallyFinite_fresh_natural
    (internallyFinite_union (columnRows_finite (β := (ω : V)) hr)
      (columnRows_finite (β := (ω : V)) hp))
  have hfreshr : ∀ δ, ⟨⟨n, (ω : V)⟩ₖ, δ⟩ₖ ∉ r := fun δ h ↦
    hnfresh (mem_union_iff.mpr (Or.inl (mem_sep_iff.mpr ⟨hn, δ, h⟩)))
  have hfreshp : ∀ δ, ⟨⟨n, (ω : V)⟩ₖ, δ⟩ₖ ∉ p := fun δ h ↦
    hnfresh (mem_union_iff.mpr (Or.inr (mem_sep_iff.mpr ⟨hn, δ, h⟩)))
  set r₁ : V := insert ⟨⟨n, (ω : V)⟩ₖ, (∅ : V)⟩ₖ r with hr₁def
  have hr₁ : r₁ ∈ levyCollapse κ := levyCollapse_insert hr hn hω empty_mem_ω hfreshr
  set t : V := insert ⟨⟨n, (ω : V)⟩ₖ, succ (∅ : V)⟩ₖ p with htdef
  have ht : t ∈ levyCollapse κ :=
    levyCollapse_insert hp hn hω (ω_succ_closed empty_mem_ω) hfreshp
  have hne : succ (∅ : V) ≠ (∅ : V) := by
    intro h
    have hmem := mem_succ_self (∅ : V)
    rw [h] at hmem
    exact not_mem_empty hmem
  have htnot : t ∉ coneRegular (levyCollapse κ) (levyOrder κ) r₁ :=
    levy_not_mem_coneRegular_of_disagree ht (mem_insert.mpr (Or.inl rfl))
      (mem_insert.mpr (Or.inl rfl)) hne
  refine ⟨r₁, hr₁, fun z hz ↦ mem_insert.mpr (Or.inr hz), fun hsub ↦ htnot ?_⟩
  -- `t` extends `p`, and the cone of `r₁` is downward closed, so `p ∈ a` would put `t` in it
  have hpt : p ⊆ t := fun z hz ↦ mem_insert.mpr (Or.inr hz)
  have htp : ⟨t, p⟩ₖ ∈ levyOrder κ :=
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨ht, hp, hpt⟩
  exact (coneRegular_regular (levyCollapse_poset κ).1 r₁).2.1 p (hsub p hpa) t ht htp

end LevyWitness

namespace ForcingContext

variable {A : ForcingContext V}

/-! ### Shrinking the pair on the side of the generic -/

/-- Shrinking the condition on the side of the generic. If `φ` is an isomorphism of the cone below
`b0` onto the cone below `c0` carrying the orbit filter to the generic below `b0` and fixing the
base support values relatively, and if `b1 ⊆ b0` is a condition met by the generic, then the
restriction of `φ` to the cone below `b1` is an isomorphism onto the cone below `c1 := φ ‘ b1`, the
check of `c1` is in the orbit filter, and both clauses hold for the pair `(b1, c1)`.

The isomorphism restricted is the one out of the cone on the side of the generic, that is, the
inverse of the isomorphism produced by `exists_orbit_cone_isomorphism_support`. -/
theorem coneShrink_data {b0 c0 b1 φ E : V} {H : A.Model}
    (hb0 : b0 ∈ booleanConditions A.P A.R) (hc0 : c0 ∈ booleanConditions A.P A.R)
    (hφ : IsForcingIsomorphism
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b0)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b0))
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) c0)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) c0)) φ)
    (hfilter : ∀ b ∈ booleanConditions A.P A.R, b ⊆ b0 →
      (A.check (φ ‘ b) ∈ H ↔ A.check b ∈ A.boolGenericSet))
    (hsupp : ∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) E,
      coneImage A.P A.R b0 φ (a ∩ b0) = a ∩ c0)
    (hb1 : b1 ∈ booleanConditions A.P A.R) (hb1b0 : b1 ⊆ b0) (hb1G : ∃ t ∈ A.G, t ∈ b1) :
    φ ‘ b1 ∈ booleanConditions A.P A.R ∧ A.check (φ ‘ b1) ∈ H ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b1)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b1))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) (φ ‘ b1))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) (φ ‘ b1)))
        (coneRestrictMap A.P A.R b1 φ) ∧
      (∀ b ∈ booleanConditions A.P A.R, b ⊆ b1 →
        (A.check ((coneRestrictMap A.P A.R b1 φ) ‘ b) ∈ H ↔ A.check b ∈ A.boolGenericSet)) ∧
      (∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) E,
        coneImage A.P A.R b1 (coneRestrictMap A.P A.R b1 φ) (a ∩ b1) = a ∩ φ ‘ b1) := by
  have hb1c : b1 ∈ forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b0 :=
    mem_forcingCone_of_subset hb1 hb0 hb1b0
  have hφb1 := function_value_mem hφ.1 hb1c
  have hφb1B := ((mem_forcingCone_iff _ _ _ _).mp hφb1).1
  have hb1gen : A.check b1 ∈ A.boolGenericSet :=
    (A.check_mem_boolGenericSet_iff _).mpr
      ⟨(mem_regularSets_iff _ _ _).mpr (booleanConditions_regular hb1), hb1G⟩
  refine ⟨hφb1B, (hfilter b1 hb1 hb1b0).mpr hb1gen,
    coneIsomorphism_restrict hφ hc0 hb0 hb1 hb1b0, fun b hb hbb1 ↦ ?_, fun a ha ↦ ?_⟩
  · rw [coneRestrictMap_value (mem_forcingCone_of_subset hb hb1 hbb1)]
    exact hfilter b hb (subset_trans hbb1 hb1b0)
  · have hareg : IsForcingRegular A.P A.R a :=
      (mem_regularSets_iff _ _ _).mp (supportValuesBase_subset_regularSets A.order _ _ _ a ha)
    exact coneIsomorphism_restrict_coneImage hφ hc0 hb0 hb1 hb1b0 hareg (hsupp a ha)

/-! ### The two trace conditions for the shrunk pair -/

/-- The image of a condition under a cone isomorphism is the whole poset only if the target cone
is: the isomorphism carries top to top and is injective on the cone. -/
theorem coneIsomorphism_value_ne_of_ne {b0 c0 b1 φ : V} (hb0 : b0 ∈ booleanConditions A.P A.R)
    (hc0 : c0 ∈ booleanConditions A.P A.R)
    (hφ : IsForcingIsomorphism
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b0)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b0))
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) c0)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) c0)) φ)
    (hb1 : b1 ∈ booleanConditions A.P A.R) (hb1b0 : b1 ⊆ b0) (hne : b1 ≠ b0) :
    φ ‘ b1 ≠ c0 := by
  intro h
  have hb0c : b0 ∈ forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b0 :=
    self_mem_forcingCone_boolean hb0
  have hb1c : b1 ∈ forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b0 :=
    mem_forcingCone_of_subset hb1 hb0 hb1b0
  have htop : φ ‘ b0 = c0 := coneIsomorphism_value_top hb0 hc0 hφ
  have hsub : b0 ⊆ b1 := by
    refine coneIsomorphism_subset_of_value_subset hφ hb0c hb1c ?_
    rw [h, htop]
  exact hne (SetTheory.subset_antisymm hb1b0 hsub)

/-- `(N1)` for the shrunk pair, from a single condition of `b0` outside `b1`: the witness makes
`¬b1` nonempty directly, and it makes `b1` a proper part of `b0`, so `c1 = φ ‘ b1` is not `c0` and
hence not the whole poset. -/
theorem forcingNegation_eq_empty_iff_of_shrink {b0 c0 b1 q φ : V}
    (hb0 : b0 ∈ booleanConditions A.P A.R) (hc0 : c0 ∈ booleanConditions A.P A.R)
    (hφ : IsForcingIsomorphism
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b0)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b0))
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) c0)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) c0)) φ)
    (hb1 : b1 ∈ booleanConditions A.P A.R) (hb1b0 : b1 ⊆ b0)
    (hq : q ∈ A.P) (hqb0 : q ∈ b0) (hqb1 : q ∉ b1) :
    forcingNegation A.P A.R b1 = (∅ : V) ↔ forcingNegation A.P A.R (φ ‘ b1) = (∅ : V) := by
  have hb1c : b1 ∈ forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b0 :=
    mem_forcingCone_of_subset hb1 hb0 hb1b0
  have hφb1 := function_value_mem hφ.1 hb1c
  have hφb1B := ((mem_forcingCone_iff _ _ _ _).mp hφb1).1
  have hleft : forcingNegation A.P A.R b1 ≠ (∅ : V) :=
    forcingNegation_ne_empty_of_not_mem A.order (booleanConditions_regular hb1) hq hqb1
  have hne : b1 ≠ b0 := fun h ↦ hqb1 (h ▸ hqb0)
  have hc1 : φ ‘ b1 ≠ c0 := coneIsomorphism_value_ne_of_ne hb0 hc0 hφ hb1 hb1b0 hne
  have hright : forcingNegation A.P A.R (φ ‘ b1) ≠ (∅ : V) := by
    rw [Ne, forcingNegation_eq_empty_iff A.order (booleanConditions_regular hφb1B)]
    intro htop
    exact hc1 (SetTheory.subset_antisymm (forcingCone_boolean_subset hφb1)
      (htop ▸ (booleanConditions_regular hc0).1))
  simp only [hleft, hright]

/-- The relative traces of the two conditions vanish together. This is what the support clause in
`coneImage` form gives on its own, in both directions. -/
theorem inter_eq_empty_iff_of_coneImage {b1 c1 f a : V} (hb1 : b1 ∈ booleanConditions A.P A.R)
    (hf : IsForcingIsomorphism
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b1)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b1))
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) c1)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) c1)) f)
    (ha : IsForcingRegular A.P A.R a) (hcone : coneImage A.P A.R b1 f (a ∩ b1) = a ∩ c1) :
    a ∩ b1 = (∅ : V) ↔ a ∩ c1 = (∅ : V) := by
  constructor
  · intro h
    rw [← hcone, h, coneImage_empty]
  · intro h
    have hinv := coneImage_inverse hf hb1 ha hcone
    rw [← hinv, h, coneImage_empty]

/-- `(N2)` at a support value that the shrunk condition misses. Both sides then say that the value
is zero. -/
theorem coneTrace_of_inter_empty {b1 c1 f a : V} (hb1 : b1 ∈ booleanConditions A.P A.R)
    (hc1 : c1 ∈ booleanConditions A.P A.R)
    (hf : IsForcingIsomorphism
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b1)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) b1))
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) c1)
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) c1)) f)
    (ha : IsForcingRegular A.P A.R a) (hcone : coneImage A.P A.R b1 f (a ∩ b1) = a ∩ c1)
    (hmiss : a ∩ b1 = (∅ : V)) :
    a ∩ forcingNegation A.P A.R b1 = (∅ : V) ↔
      a ∩ forcingNegation A.P A.R c1 = (∅ : V) := by
  have hmissc : a ∩ c1 = (∅ : V) :=
    (inter_eq_empty_iff_of_coneImage hb1 hf ha hcone).mp hmiss
  have key : ∀ d : V, d ∈ booleanConditions A.P A.R → a ∩ d = (∅ : V) →
      (a ∩ forcingNegation A.P A.R d = (∅ : V) ↔ a = (∅ : V)) := by
    intro d hd hmd
    rw [inter_forcingNegation_eq_empty_iff A.order ha (booleanConditions_regular hd)]
    constructor
    · intro hsub
      refine mem_ext (fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ absurd hz not_mem_empty⟩)
      have : z ∈ a ∩ d := mem_inter_iff.mpr ⟨hz, hsub z hz⟩
      rw [hmd] at this
      exact absurd this not_mem_empty
    · intro h z hz
      rw [h] at hz
      exact absurd hz not_mem_empty
  rw [key b1 hb1 hmiss, key c1 hc1 hmissc]

/-- `(N2)` at the top: both sides are false because both negations are nonempty. -/
theorem coneTrace_of_eq_top {b1 c1 a : V} (ha : a = A.P)
    (hb1 : forcingNegation A.P A.R b1 ≠ (∅ : V))
    (hc1 : forcingNegation A.P A.R c1 ≠ (∅ : V)) :
    a ∩ forcingNegation A.P A.R b1 = (∅ : V) ↔
      a ∩ forcingNegation A.P A.R c1 = (∅ : V) := by
  have key : ∀ d : V, A.P ∩ forcingNegation A.P A.R d = forcingNegation A.P A.R d := by
    intro d
    rw [inter_comm_set]
    exact inter_eq_left_of_subset (forcingNegation_subset A.P A.R d)
  subst ha
  simp only [key, hb1, hc1]

/-! ### The residue -/

/-- The statement that is left open. Below a condition `r` of the generic filter there is a
condition `r₁` of the generic filter with

* a condition of the cone of `r` outside the cone of `r₁`, which is what `(N1)` needs, and
* every base support value of `range s` either the whole poset or disjoint from the cone of `r₁`,
  which is what the proof of `(N2)` below uses.

The first clause always holds for the Levy collapse
(`levy_exists_generic_extension_witness`). The second is the residue. It asks one condition to
decide every base support value at once, and the base support values are indexed by
`(ω ×ˢ ω) ×ˢ range s`, so it is not the density statement for a single value that
`levy_exists_extension_not_subset_coneRegular` proves. -/
def NoSupportValueBelow (A : ForcingContext V) (s r : V) : Prop :=
  ∃ r₁ ∈ A.G, ⟨r₁, r⟩ₖ ∈ A.R ∧
    (∃ q ∈ A.P, q ∈ coneRegular A.P A.R r ∧ q ∉ coneRegular A.P A.R r₁) ∧
    ∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
      a = A.P ∨ a ∩ coneRegular A.P A.R r₁ = (∅ : V)

/-- `ConeTraceAligned` from the cone construction and the residue. The pair is the cone of the
shrunk condition `r₁` of the generic filter and its image under the inverse of the isomorphism that
`exists_orbit_cone_isomorphism_support` returns.

The side conditions of `exists_orbit_cone_isomorphism_support` are kept explicit: the support
sequence is a function with domain the index set, and the ground predicate at the parameter holds
only of checks. -/
theorem coneTraceAligned_of_noSupportValueBelow (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {s k : V} [IsFunction s] (hsdom : domain s = k) {p : A.Model}
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a)
    (hres : ∀ r ∈ A.G, A.NoSupportValueBelow s r) :
    A.ConeTraceAligned Pf s k p := by
  intro hE H hH
  have hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) (s ‘ i) := by
    intro i hi
    exact hE _ (mem_range_of_kpair_mem (kpair_value_mem (by rw [hsdom]; exact hi)))
  obtain ⟨r, hrG, q₀, hq₀B, ψ, hq₀H, hψ, hfilter, hsupp⟩ :=
    exists_orbit_cone_isomorphism_support hAC hsdom hs hH hPf
  have hrP : r ∈ A.P := A.generic.1.1 r hrG
  set b0 : V := coneRegular A.P A.R r with hb0def
  have hb0 : b0 ∈ booleanConditions A.P A.R := coneRegular_mem_booleanConditions A.order hrP
  set φ : V := converseGraph ψ with hφdef
  have hφ := isForcingIsomorphism_inverse hψ
  have hfilter' : ∀ b ∈ booleanConditions A.P A.R, b ⊆ b0 →
      (A.check (φ ‘ b) ∈ H ↔ A.check b ∈ A.boolGenericSet) :=
    filterTransfer_inverse hb0 hψ hfilter
  have hcone : ∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
      coneImage A.P A.R q₀ ψ (a ∩ q₀) = a ∩ b0 :=
    fun a ha ↦ coneImage_of_support_clause hq₀B hb0 hψ hsupp ha
  have hsupp' : ∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
      coneImage A.P A.R b0 φ (a ∩ b0) = a ∩ q₀ := by
    intro a ha
    have hareg : IsForcingRegular A.P A.R a :=
      (mem_regularSets_iff _ _ _).mp (supportValuesBase_subset_regularSets A.order _ _ _ a ha)
    exact coneImage_inverse hψ hq₀B hareg (hcone a ha)
  -- the shrunk condition of the generic filter
  obtain ⟨r₁, hr₁G, hr₁r, ⟨q, hqP, hqb0, hqb1⟩, hvals⟩ := hres r hrG
  have hr₁P : r₁ ∈ A.P := A.generic.1.1 r₁ hr₁G
  set b1 : V := coneRegular A.P A.R r₁ with hb1def
  have hb1 : b1 ∈ booleanConditions A.P A.R := coneRegular_mem_booleanConditions A.order hr₁P
  have hb1b0 : b1 ⊆ b0 := coneRegular_subset_coneRegular A.order hrP hr₁P hr₁r
  have hb1G : ∃ t ∈ A.G, t ∈ b1 := ⟨r₁, hr₁G, self_mem_coneRegular A.order hr₁P⟩
  obtain ⟨hc1B, hc1H, hiso, hfil, hsup⟩ :=
    coneShrink_data hb0 hq₀B hφ hfilter' hsupp' hb1 hb1b0 hb1G
  set c1 : V := φ ‘ b1 with hc1def
  -- `(N1)`
  have hN1 : forcingNegation A.P A.R b1 = (∅ : V) ↔ forcingNegation A.P A.R c1 = (∅ : V) :=
    forcingNegation_eq_empty_iff_of_shrink hb0 hq₀B hφ hb1 hb1b0 hqP hqb0 hqb1
  have hnb1 : forcingNegation A.P A.R b1 ≠ (∅ : V) :=
    forcingNegation_ne_empty_of_not_mem A.order (booleanConditions_regular hb1) hqP hqb1
  have hnc1 : forcingNegation A.P A.R c1 ≠ (∅ : V) := fun h ↦ hnb1 (hN1.mpr h)
  refine ⟨b1, hb1, c1, hc1B, coneRestrictMap A.P A.R b1 φ, hiso, hb1G, hc1H, hfil, hsup, hN1,
    fun a ha ↦ ?_⟩
  have hareg : IsForcingRegular A.P A.R a :=
    (mem_regularSets_iff _ _ _).mp (supportValuesBase_subset_regularSets A.order _ _ _ a ha)
  rcases hvals a ha with htop | hmiss
  · exact coneTrace_of_eq_top htop hnb1 hnc1
  · exact coneTrace_of_inter_empty hb1 hc1B hiso hareg (hsup a ha) hmiss

end ForcingContext

/-! ### The Levy exports -/

section Levy

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The first clause of `NoSupportValueBelow` always holds for the Levy collapse, so the residue is
only the clause about the base support values. -/
theorem levy_exists_shrink_witness (hω : (ω : V) ∈ κ) {r : V} (hrG : r ∈ (levyContext κ hG).G) :
    ∃ r₁ ∈ (levyContext κ hG).G, ⟨r₁, r⟩ₖ ∈ (levyContext κ hG).R ∧
      ∃ q ∈ (levyContext κ hG).P,
        q ∈ coneRegular (levyContext κ hG).P (levyContext κ hG).R r ∧
          q ∉ coneRegular (levyContext κ hG).P (levyContext κ hG).R r₁ :=
  levy_exists_generic_extension_witness hω hG hrG

include hAC hU hc hω hκ in
/-- `ConeTraceAligned` for the Levy collapse from the residue, for a support sequence that is a
function with domain the index set. -/
theorem levy_coneTraceAligned_of_noSupportValueBelow {s k : V} [IsFunction s]
    (hsdom : domain s = k)
    (hres : ∀ r ∈ (levyContext κ hG).G, (levyContext κ hG).NoSupportValueBelow s r) :
    (levyContext κ hG).ConeTraceAligned groundFormula s k (solovayParam κ hG) :=
  ForcingContext.coneTraceAligned_of_noSupportValueBelow hAC hsdom
    (levy_check_of_evalb_groundFormula hAC hU hc hω hκ hG) hres

end Levy

end ZFVP
