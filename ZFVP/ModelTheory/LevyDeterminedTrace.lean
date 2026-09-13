import ZFVP.ModelTheory.LevyDeterminedSubalgebra

/-! The trace of a set of conditions over the algebra of sets determined below `ξ`.

`levyDeterminedAlgebra κ ξ` (ZFVP/ModelTheory/LevyDeterminedSubalgebra.lean) is the complete
subalgebra of `RO(Coll(ω, <κ))` of the regular sets whose membership only depends on the part of
a condition below `ξ`. This module builds the projection of an arbitrary set of conditions `b`
to that subalgebra and computes it on cones.

The projection is the regular closure of the set of conditions extending the `ξ`-part of some
condition of `b`:

  `levyTraceBase κ ξ b = {q ∈ Coll(ω, <κ) ; ∃ p ∈ b, levyCut ξ p ⊆ q}`,
  `levyTrace κ ξ b = forcingClosure (levyTraceBase κ ξ b)`.

Taking the closure of the image `{levyCut ξ p ; p ∈ b}` itself would not work: that image is not
closed downward, and the forcing closure of a set that is not closed downward need not contain it.
Passing to the conditions below the image first repairs this, and the two closures the definition
could use agree once the image is closed downward.

`levyTrace_determined` and `levyTrace_regular` put the trace in the subalgebra,
`subset_levyTrace` and `levyTrace_subset_of_determined` say it is the smallest member of the
subalgebra above `b`, and `inter_determined_eq_empty_iff_levyTrace` is the projection property
that the cone alignment of ZFVP/ModelTheory/LevyConeTraceAlignment.lean compares against.
`levyTrace_coneRegular` computes the trace of a cone: it is the cone of the `ξ`-part. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Row permutations above `ξ` fix a `ξ`-part -/

/-- A row permutation above `ξ` fixes the part of a condition below `ξ`. This is
`levyPermutation_fixed` for the particular condition `levyCut ξ p`, and it needs neither that `ξ`
is an ordinal nor that `levyCut ξ p` lies in `levyCollapse ξ`. -/
theorem levyPermutation_levyCut {κ ξ s p : V} (hs : IsInternalPermutation (ω : V) s)
    (hξ : ξ ⊆ κ) (hp : p ∈ levyCollapse κ) :
    (levyPermutation κ ξ s) ‘ (levyCut ξ p) = levyCut ξ p := by
  have hc : levyCut ξ p ∈ levyCollapse κ := levyCollapse_subset hp (levyCut_subset ξ p)
  have hsub := ((mem_finitePartialFunctions _ _ _).mp (levyCollapse_finitePartialFunction hc)).1
  have hentry : ∀ z ∈ levyCut ξ p, permutedGraphEntry (levyRowPermutation κ ξ s) z = z := by
    intro z hz
    obtain ⟨x, hx, γ, -, rfl⟩ := mem_prod_iff.mp (hsub _ hz)
    have hxξ : x ∈ (ω : V) ×ˢ ξ := ((kpair_mem_levyCut_iff ξ p x γ).mp hz).2
    obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hxξ
    unfold permutedGraphEntry
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    rw [levyRowPermutation_value_below hs hn (hξ _ hα) hα]
  rw [levyPermutation_value hc]
  apply mem_ext
  intro z
  rw [mem_permutedGraph]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [hentry u hu]
    exact hu
  · intro hz
    exact ⟨z, hz, (hentry z hz).symm⟩

/-- A row permutation above `ξ` does not change whether a condition extends a `ξ`-part. -/
theorem levyCut_subset_value_iff {κ ξ s p q : V} (hs : IsInternalPermutation (ω : V) s)
    (hξ : ξ ⊆ κ) (hp : p ∈ levyCollapse κ) (hq : q ∈ levyCollapse κ) :
    levyCut ξ p ⊆ (levyPermutation κ ξ s) ‘ q ↔ levyCut ξ p ⊆ q := by
  have hπ := levyPermutation_automorphism (κ := κ) (β := ξ) hs
  have hc : levyCut ξ p ∈ levyCollapse κ := levyCollapse_subset hp (levyCut_subset ξ p)
  have hπq : (levyPermutation κ ξ s) ‘ q ∈ levyCollapse κ := function_value_mem hπ.1 hq
  have hfix := levyPermutation_levyCut hs hξ hp
  constructor
  · intro h
    have h1 : (⟨(levyPermutation κ ξ s) ‘ q,
        (levyPermutation κ ξ s) ‘ (levyCut ξ p)⟩ₖ : V) ∈ levyOrder κ := by
      rw [hfix]
      exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hπq, hc, h⟩
    exact ((pair_mem_reverseInclusionOrder _ _ _).mp ((hπ.2.2.2 q hq _ hc).mpr h1)).2.2
  · intro h
    have h1 : (⟨q, levyCut ξ p⟩ₖ : V) ∈ levyOrder κ :=
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hc, h⟩
    have h2 := (hπ.2.2.2 q hq _ hc).mp h1
    rw [hfix] at h2
    exact ((pair_mem_reverseInclusionOrder _ _ _).mp h2).2.2

/-! ### The trace -/

instance levyTraceBase_predicate (ξ b : V) :
    ℒₛₑₜ-predicate[V] (fun q ↦ ∃ p ∈ b, levyCut ξ p ⊆ q) := by
  unfold levyCut
  definability

/-- The conditions extending the `ξ`-part of some condition of `b`. -/
noncomputable def levyTraceBase (κ ξ b : V) : V :=
  {q ∈ levyCollapse κ ; ∃ p ∈ b, levyCut ξ p ⊆ q}

theorem mem_levyTraceBase_iff {κ ξ b q : V} :
    q ∈ levyTraceBase κ ξ b ↔ q ∈ levyCollapse κ ∧ ∃ p ∈ b, levyCut ξ p ⊆ q := mem_sep_iff

theorem levyTraceBase_subset (κ ξ b : V) : levyTraceBase κ ξ b ⊆ levyCollapse κ := sep_subset

theorem levyTraceBase_downward (κ ξ b : V) :
    IsForcingDownwardClosed (levyCollapse κ) (levyOrder κ) (levyTraceBase κ ξ b) := by
  intro q hq q' hq' hq'q
  obtain ⟨-, p, hp, hsub⟩ := mem_levyTraceBase_iff.mp hq
  exact mem_levyTraceBase_iff.mpr
    ⟨hq', p, hp, subset_trans hsub ((pair_mem_reverseInclusionOrder _ _ _).mp hq'q).2.2⟩

/-- The projection of a set of conditions to the algebra of sets determined below `ξ`. -/
noncomputable def levyTrace (κ ξ b : V) : V :=
  forcingClosure (levyCollapse κ) (levyOrder κ) (levyTraceBase κ ξ b)

theorem levyTrace_subset (κ ξ b : V) : levyTrace κ ξ b ⊆ levyCollapse κ :=
  forcingClosure_subset _ _ _

/-- The trace is a regular set. -/
theorem levyTrace_regular (κ ξ b : V) :
    IsForcingRegular (levyCollapse κ) (levyOrder κ) (levyTrace κ ξ b) :=
  forcingClosure_regular (levyCollapse_poset κ).1 (levyTraceBase_subset κ ξ b)

/-- A row permutation above `ξ` fixes the base of the trace as a set. -/
theorem imageAction_levyTraceBase {κ ξ b s : V} (hs : IsInternalPermutation (ω : V) s)
    (hξ : ξ ⊆ κ) (hb : b ⊆ levyCollapse κ) :
    ∀ q ∈ levyCollapse κ,
      (levyPermutation κ ξ s) ‘ q ∈ levyTraceBase κ ξ b ↔ q ∈ levyTraceBase κ ξ b := by
  have hπ := levyPermutation_automorphism (κ := κ) (β := ξ) hs
  intro q hq
  rw [mem_levyTraceBase_iff, mem_levyTraceBase_iff]
  constructor
  · rintro ⟨-, p, hp, hsub⟩
    exact ⟨hq, p, hp, (levyCut_subset_value_iff hs hξ (hb p hp) hq).mp hsub⟩
  · rintro ⟨-, p, hp, hsub⟩
    exact ⟨function_value_mem hπ.1 hq, p, hp,
      (levyCut_subset_value_iff hs hξ (hb p hp) hq).mpr hsub⟩

/-- The trace is determined below `ξ`. -/
theorem levyTrace_determined {κ ξ b : V} (hξ : ξ ⊆ κ) (hb : b ⊆ levyCollapse κ) :
    IsLevyDeterminedBelow κ ξ (levyTrace κ ξ b) := by
  refine (levy_determined_iff_permutations_fixed (levyTrace_regular κ ξ b)).mpr (fun s hs ↦ ?_)
  have hπ := levyPermutation_automorphism (κ := κ) (β := ξ) hs
  refine imageAction_eq_of_iff hπ (levyTrace_subset κ ξ b) (levyTrace_subset κ ξ b)
    (fun q hq ↦ ?_)
  exact forcingClosure_action_iff hπ (levyTraceBase_subset κ ξ b) (levyTraceBase_subset κ ξ b)
    (imageAction_levyTraceBase hs hξ hb) hq

/-- The trace is a member of the algebra of sets determined below `ξ`. -/
theorem levyTrace_mem_levyDeterminedAlgebra {κ ξ b : V} (hξ : ξ ⊆ κ) (hb : b ⊆ levyCollapse κ) :
    levyTrace κ ξ b ∈ levyDeterminedAlgebra κ ξ :=
  (mem_levyDeterminedAlgebra_iff _ _ _).mpr ⟨levyTrace_regular κ ξ b, levyTrace_determined hξ hb⟩

/-- The trace contains the set it is the trace of. -/
theorem subset_levyTrace {κ ξ b : V} (hb : b ⊆ levyCollapse κ) : b ⊆ levyTrace κ ξ b := by
  refine subset_trans (fun p hp ↦ mem_levyTraceBase_iff.mpr ⟨hb p hp, p, hp, levyCut_subset ξ p⟩)
    (subset_forcingClosure (levyCollapse_poset κ).1 (levyTraceBase_subset κ ξ b)
      (levyTraceBase_downward κ ξ b))

/-- The trace is the smallest determined regular set above `b`. -/
theorem levyTrace_subset_of_determined {κ ξ b d : V} (hd : d ∈ levyDeterminedAlgebra κ ξ)
    (hbd : b ⊆ d) : levyTrace κ ξ b ⊆ d := by
  obtain ⟨hdreg, hdet⟩ := (mem_levyDeterminedAlgebra_iff _ _ _).mp hd
  have hbase : levyTraceBase κ ξ b ⊆ d := by
    intro q hq
    obtain ⟨hqP, p, hp, hsub⟩ := mem_levyTraceBase_iff.mp hq
    have hpP : p ∈ levyCollapse κ := hdreg.1 p (hbd p hp)
    have hcut : levyCut ξ p ∈ d := (hdet p hpP).mp (hbd p hp)
    exact hdreg.2.1 _ hcut q hqP ((pair_mem_reverseInclusionOrder _ _ _).mpr
      ⟨hqP, levyCollapse_subset hpP (levyCut_subset ξ p), hsub⟩)
  intro x hx
  rw [← forcingClosure_eq (levyCollapse_poset κ).1 hdreg]
  exact forcingClosure_mono hbase x hx

/-! ### The projection property -/

/-- A determined regular set meets `b` exactly when it meets the trace of `b`.

The direction from left to right uses that `b` is closed downward: it replaces `b` by the forcing
negation of `a`, which is determined below `ξ`, and applies minimality. Without downward closure
it fails, and already for a one-point `b`: take `κ = ω`, `ξ = 3`, `b` the singleton of the
condition sending column `0` of row `5` to `0`, and `a` the cone of the condition sending column
`0` of row `2` to `0`. Then `a` is determined below `3`, the `3`-part of the condition of `b` is
empty so the trace of `b` is the whole poset and meets `a`, while `a` itself misses `b`.

The direction from right to left only uses `b ⊆ levyTrace κ ξ b`. -/
theorem inter_determined_eq_empty_iff_levyTrace {κ ξ b a : V}
    (ha : a ∈ levyDeterminedAlgebra κ ξ) (hb : b ⊆ levyCollapse κ)
    (hbd : IsForcingDownwardClosed (levyCollapse κ) (levyOrder κ) b) :
    a ∩ b = (∅ : V) ↔ a ∩ levyTrace κ ξ b = (∅ : V) := by
  constructor
  · intro h
    have hbneg : b ⊆ forcingNegation (levyCollapse κ) (levyOrder κ) a := by
      intro p hp
      refine (mem_forcingNegation_iff _ _ _ _).mpr ⟨hb p hp, fun q hq hqp hqa ↦ ?_⟩
      have hmem : q ∈ a ∩ b := mem_inter_iff.mpr ⟨hqa, hbd p hp q hq hqp⟩
      rw [h] at hmem
      exact not_mem_empty hmem
    have hneg : forcingNegation (levyCollapse κ) (levyOrder κ) a ∈ levyDeterminedAlgebra κ ξ :=
      (levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.1 a ha
    have hsub := levyTrace_subset_of_determined hneg hbneg
    apply mem_ext
    intro x
    constructor
    · intro hx
      obtain ⟨hxa, hxt⟩ := mem_inter_iff.mp hx
      exact absurd hxa (forcingNegation_disjoint (levyCollapse_poset κ).1 (hsub x hxt))
    · intro hx
      exact (not_mem_empty hx).elim
  · intro h
    apply mem_ext
    intro x
    constructor
    · intro hx
      obtain ⟨hxa, hxb⟩ := mem_inter_iff.mp hx
      have : x ∈ a ∩ levyTrace κ ξ b :=
        mem_inter_iff.mpr ⟨hxa, subset_levyTrace hb x hxb⟩
      rw [h] at this
      exact (not_mem_empty this).elim
    · intro hx
      exact (not_mem_empty hx).elim

/-! ### The trace of a cone -/

/-- The cone of a `ξ`-part is determined below `ξ`. -/
theorem coneRegular_levyCut_mem_levyDeterminedAlgebra {κ ξ r : V} (hξ : ξ ⊆ κ)
    (hr : r ∈ levyCollapse κ) :
    coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r) ∈ levyDeterminedAlgebra κ ξ := by
  have hcut : levyCut ξ r ∈ levyCollapse κ := levyCollapse_subset hr (levyCut_subset ξ r)
  refine (mem_levyDeterminedAlgebra_iff _ _ _).mpr
    ⟨coneRegular_regular (levyCollapse_poset κ).1 _, ?_⟩
  refine (levy_determined_iff_permutations_fixed
    (coneRegular_regular (levyCollapse_poset κ).1 (levyCut ξ r))).mpr (fun s hs ↦ ?_)
  have hπ := levyPermutation_automorphism (κ := κ) (β := ξ) hs
  rw [imageAction_coneRegular hπ hcut, levyPermutation_levyCut hs hξ hr]

/-- The trace of the cone of a condition is the cone of its `ξ`-part. -/
theorem levyTrace_coneRegular {κ ξ r : V} (hξ : ξ ⊆ κ) (hr : r ∈ levyCollapse κ) :
    levyTrace κ ξ (coneRegular (levyCollapse κ) (levyOrder κ) r) =
      coneRegular (levyCollapse κ) (levyOrder κ) (levyCut ξ r) := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hcut : levyCut ξ r ∈ levyCollapse κ := levyCollapse_subset hr (levyCut_subset ξ r)
  apply SetTheory.subset_antisymm
  · refine levyTrace_subset_of_determined
      (coneRegular_levyCut_mem_levyDeterminedAlgebra hξ hr) ?_
    exact coneRegular_mono hR hcut hr
      ((pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr, hcut, levyCut_subset ξ r⟩)
  · have hmono : {q ∈ levyCollapse κ ; ⟨q, levyCut ξ r⟩ₖ ∈ levyOrder κ} ⊆
        levyTraceBase κ ξ (coneRegular (levyCollapse κ) (levyOrder κ) r) := by
      intro q hq
      obtain ⟨hqP, hqR⟩ := mem_sep_iff.mp hq
      exact mem_levyTraceBase_iff.mpr ⟨hqP, r, self_mem_coneRegular hR hr,
        ((pair_mem_reverseInclusionOrder _ _ _).mp hqR).2.2⟩
    intro x hx
    exact forcingClosure_mono hmono x hx

/-- Two conditions with the same `ξ`-part have cones with the same trace. -/
theorem levyTrace_eq_of_agree {κ ξ r r' : V} (hξ : ξ ⊆ κ) (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) (h : levyCut ξ r = levyCut ξ r') :
    levyTrace κ ξ (coneRegular (levyCollapse κ) (levyOrder κ) r) =
      levyTrace κ ξ (coneRegular (levyCollapse κ) (levyOrder κ) r') := by
  rw [levyTrace_coneRegular hξ hr, levyTrace_coneRegular hξ hr', h]

end ZFVP
