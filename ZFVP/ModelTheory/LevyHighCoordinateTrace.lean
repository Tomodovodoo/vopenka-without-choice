import ZFVP.ModelTheory.LevyTraceProjection
import ZFVP.ModelTheory.BooleanConeCantorBernstein
import ZFVP.SetTheory.LevyCollapseSmallSets
import ZFVP.SetTheory.Hessenberg

/-! Cones of conditions that use a coordinate high above `ξ`.

Fix `ξ ⊆ κ` and a condition `r` of `Coll(ω, <κ)` that gives a value at a coordinate `⟨n, α⟩` with
`ξ ⊆ α` and `ω ⊆ α`. The column `α` then sits at or above `ξ` and has infinitely many admissible
values, so a condition whose domain lies inside `ω × ξ` is free at `⟨n, α⟩` and can be extended
there by a value different from the one `r` gives. Such an extension is incompatible with `r`.

Three consequences:

* every set determined below `ξ` that lies inside the regular cone of `r` is empty
  (`levy_determined_subset_coneRegular_empty`);
* the trace of the complement of a nonzero Boolean condition inside that cone is the whole poset
  (`levyTrace_forcingNegation_eq_top`);
* two such Boolean conditions have complements of equal trace
  (`levyTrace_forcingNegation_eq_of_highCoordinate`).

Every condition can be extended to one with such a coordinate as long as `ξ ∈ κ` and `ω ∈ κ`
(`levy_exists_highCoordinate_extension`). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Two small facts -/

/-- A regular set whose complement is empty is the whole poset. -/
theorem forcingRegular_eq_poset_of_forcingNegation_empty {P R A : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) (h : forcingNegation P R A = (∅ : V)) : A = P := by
  refine SetTheory.subset_antisymm hA.1 (fun p hp ↦ ?_)
  refine hA.2.2 p hp (fun q hq _ ↦ ?_)
  by_cases hqA : q ∈ A
  · exact ⟨q, hqA, hR.2.1 q hq⟩
  · obtain ⟨s, hs, _⟩ := exists_forcingNegation_of_not_mem hq hqA hA.2.2
    rw [h] at hs
    exact (not_mem_empty hs).elim

/-- Two conditions that give different values at one coordinate are incompatible, so neither is in
the regular cone of the other. This is `levy_not_mem_coneRegular_of_disagree` with an arbitrary
column in place of `ω`. -/
theorem levy_not_mem_coneRegular_of_disagree_column {κ n α γ δ p q : V}
    (hp : p ∈ levyCollapse κ) (hpv : ⟨⟨n, α⟩ₖ, γ⟩ₖ ∈ p) (hqv : ⟨⟨n, α⟩ₖ, δ⟩ₖ ∈ q) (hne : γ ≠ δ) :
    p ∉ coneRegular (levyCollapse κ) (levyOrder κ) q := by
  intro hmem
  obtain ⟨-, hh⟩ := mem_coneRegular_iff.mp hmem
  obtain ⟨s, hsP, hsq, hsp⟩ := hh _ hp ((levyCollapse_poset κ).1.2.1 _ hp)
  have hqs : q ⊆ s := ((pair_mem_reverseInclusionOrder _ _ _).mp hsq).2.2
  have hps : p ⊆ s := ((pair_mem_reverseInclusionOrder _ _ _).mp hsp).2.2
  have hfun : IsFunction s :=
    ((mem_finitePartialFunctions _ _ s).mp (levyCollapse_finitePartialFunction hsP)).2.1
  exact hne (IsFunction.unique (hps _ hpv) (hqs _ hqv))

/-! ### Extending a condition into a high column -/

/-- Every condition of `Coll(ω, <κ)` extends to one that uses a coordinate in a column at or above
`ξ` with infinitely many admissible values. The column is `ξ ∪ ω`, and the row is one that the
condition leaves free in that column. -/
theorem levy_exists_highCoordinate_extension {κ ξ p : V} [IsOrdinal κ] (hξ : ξ ⊆ κ) (hξκ : ξ ∈ κ)
    (hω : (ω : V) ∈ κ) (hp : p ∈ levyCollapse κ) :
    ∃ r, r ∈ levyCollapse κ ∧ p ⊆ r ∧ ∃ n α β, n ∈ (ω : V) ∧ α ∈ κ ∧ ξ ⊆ α ∧ (ω : V) ⊆ α ∧
      ⟨⟨n, α⟩ₖ, β⟩ₖ ∈ r := by
  have _ : IsOrdinal ξ := IsOrdinal.of_mem hξκ
  have hα : ξ ∪ (ω : V) ∈ κ := union_mem_of_ordinals hξκ hω
  have hξα : ξ ⊆ ξ ∪ (ω : V) := subset_union_left ξ (ω : V)
  have hωα : (ω : V) ⊆ ξ ∪ (ω : V) := subset_union_right ξ (ω : V)
  obtain ⟨n, hn, hnfresh⟩ :=
    internallyFinite_fresh_natural (columnRows_finite (β := ξ ∪ (ω : V)) hp)
  have hfresh : ∀ δ, ⟨⟨n, ξ ∪ (ω : V)⟩ₖ, δ⟩ₖ ∉ p := fun δ h ↦ hnfresh (mem_sep_iff.mpr ⟨hn, δ, h⟩)
  refine ⟨insert ⟨⟨n, ξ ∪ (ω : V)⟩ₖ, (∅ : V)⟩ₖ p,
    levyCollapse_insert hp hn hα (hωα _ empty_mem_ω) hfresh,
    fun z hz ↦ mem_insert.mpr (Or.inr hz),
    n, ξ ∪ (ω : V), (∅ : V), hn, hα, hξα, hωα, mem_insert.mpr (Or.inl rfl)⟩

/-! ### No determined set inside such a cone -/

/-- A set determined below `ξ` that lies inside the regular cone of a condition using a coordinate
in a column at or above `ξ` with at least two admissible values is empty.

If `p` is in the set, so is its part below `ξ`, which therefore lies in the cone. That part is free
at the coordinate `⟨n, α⟩`, because `ξ ⊆ α` forces `α ∉ ξ`. Extending it there by a value other
than the one `r` gives produces a condition of the cone that is incompatible with `r`. -/
theorem levy_determined_subset_coneRegular_empty {κ ξ r n α β : V} [IsOrdinal κ] (hξ : ξ ⊆ κ)
    (hr : r ∈ levyCollapse κ) (hn : n ∈ (ω : V)) (hα : α ∈ κ) (hξα : ξ ⊆ α) (hωα : (ω : V) ⊆ α)
    (hmem : ⟨⟨n, α⟩ₖ, β⟩ₖ ∈ r) {d : V} (hd : d ∈ levyDeterminedAlgebra κ ξ)
    (hsub : d ⊆ coneRegular (levyCollapse κ) (levyOrder κ) r) : d = (∅ : V) := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  obtain ⟨hdreg, hdet⟩ := (mem_levyDeterminedAlgebra_iff _ _ _).mp hd
  apply subset_empty_iff_eq_empty.mp
  intro p hp
  exfalso
  have hpP : p ∈ levyCollapse κ := hdreg.1 p hp
  have hcutd : levyCut ξ p ∈ d := (hdet p hpP).mp hp
  have hcutP : levyCut ξ p ∈ levyCollapse κ := levyCollapse_subset hpP (levyCut_subset ξ p)
  have hcone : levyCut ξ p ∈ coneRegular (levyCollapse κ) (levyOrder κ) r := hsub _ hcutd
  have hfresh : ∀ δ, ⟨⟨n, α⟩ₖ, δ⟩ₖ ∉ levyCut ξ p := by
    intro δ h
    have hαξ : α ∈ ξ := (kpair_mem_iff.mp ((kpair_mem_levyCut_iff ξ p _ δ).mp h).2).2
    exact mem_irrefl α (hξα α hαξ)
  obtain ⟨β', hβ'α, hne⟩ : ∃ β', β' ∈ α ∧ β' ≠ β := by
    by_cases hb : β = (∅ : V)
    · refine ⟨succ (∅ : V), hωα _ (ω_succ_closed empty_mem_ω), ?_⟩
      rw [hb]
      intro h
      have hmm := mem_succ_self (∅ : V)
      rw [h] at hmm
      exact not_mem_empty hmm
    · exact ⟨(∅ : V), hωα _ empty_mem_ω, fun h ↦ hb h.symm⟩
  have hqP : insert ⟨⟨n, α⟩ₖ, β'⟩ₖ (levyCut ξ p) ∈ levyCollapse κ :=
    levyCollapse_insert hcutP hn hα hβ'α hfresh
  have hqle : ⟨insert ⟨⟨n, α⟩ₖ, β'⟩ₖ (levyCut ξ p), levyCut ξ p⟩ₖ ∈ levyOrder κ :=
    (pair_mem_reverseInclusionOrder _ _ _).mpr
      ⟨hqP, hcutP, fun z hz ↦ mem_insert.mpr (Or.inr hz)⟩
  have hqcone : insert ⟨⟨n, α⟩ₖ, β'⟩ₖ (levyCut ξ p) ∈
      coneRegular (levyCollapse κ) (levyOrder κ) r :=
    (coneRegular_regular hR r).2.1 _ hcone _ hqP hqle
  exact levy_not_mem_coneRegular_of_disagree_column hqP (mem_insert.mpr (Or.inl rfl)) hmem hne
    hqcone

/-! ### The trace of the complement -/

/-- For a nonzero Boolean condition inside the regular cone of a condition with such a coordinate,
the trace of the complement is the whole poset.

If the trace `T` were not the whole poset, its complement `e` would be a nonzero set determined
below `ξ`. The complement of `b` lies in `T`, so `e` misses it, so `e ⊆ b` and `e` lies in the
cone, and the previous theorem makes `e` empty. -/
theorem levyTrace_forcingNegation_eq_top {κ ξ r n α β b : V} [IsOrdinal κ] (hξ : ξ ⊆ κ)
    (hr : r ∈ levyCollapse κ) (hn : n ∈ (ω : V)) (hα : α ∈ κ) (hξα : ξ ⊆ α) (hωα : (ω : V) ⊆ α)
    (hmem : ⟨⟨n, α⟩ₖ, β⟩ₖ ∈ r)
    (hb : b ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hbr : b ⊆ coneRegular (levyCollapse κ) (levyOrder κ) r) :
    levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b) = levyCollapse κ := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hbreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) b := booleanConditions_regular hb
  have hNreg : IsForcingRegular (levyCollapse κ) (levyOrder κ)
      (forcingNegation (levyCollapse κ) (levyOrder κ) b) :=
    forcingNegation_regular hR hbreg.2.1
  have hT : levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b) ∈
      levyDeterminedAlgebra κ ξ :=
    levyTrace_mem_levyDeterminedAlgebra hξ hNreg.1
  have he : forcingNegation (levyCollapse κ) (levyOrder κ)
      (levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b)) ∈
      levyDeterminedAlgebra κ ξ :=
    (levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.1 _ hT
  have hereg : IsForcingRegular (levyCollapse κ) (levyOrder κ)
      (forcingNegation (levyCollapse κ) (levyOrder κ)
        (levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b))) :=
    ((mem_levyDeterminedAlgebra_iff _ _ _).mp he).1
  have hNT : forcingNegation (levyCollapse κ) (levyOrder κ) b ⊆
      levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b) :=
    subset_levyTrace hNreg.1
  have hTe : levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b) ∩
      forcingNegation (levyCollapse κ) (levyOrder κ)
        (levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b)) = (∅ : V) :=
    inter_forcingNegation_eq_empty hR (levyTrace_subset κ ξ _)
  have h1 : forcingNegation (levyCollapse κ) (levyOrder κ)
      (levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b)) ∩
      forcingNegation (levyCollapse κ) (levyOrder κ) b = (∅ : V) := by
    refine subset_empty_iff_eq_empty.mp (fun x hx ↦ ?_)
    obtain ⟨hxe, hxN⟩ := mem_inter_iff.mp hx
    rw [← hTe]
    exact mem_inter_iff.mpr ⟨hNT x hxN, hxe⟩
  have h2 : forcingNegation (levyCollapse κ) (levyOrder κ)
      (levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b)) ⊆ b :=
    sb_subset_of_inter_negation_empty hR hereg hbreg h1
  have h3 : forcingNegation (levyCollapse κ) (levyOrder κ)
      (levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b)) = (∅ : V) :=
    levy_determined_subset_coneRegular_empty hξ hr hn hα hξα hωα hmem he
      (subset_trans h2 hbr)
  exact forcingRegular_eq_poset_of_forcingNegation_empty hR (levyTrace_regular κ ξ _) h3

/-- Two nonzero Boolean conditions, each inside the regular cone of a condition using a coordinate
in a column at or above `ξ` with infinitely many admissible values, have complements of equal
trace: both traces are the whole poset. -/
theorem levyTrace_forcingNegation_eq_of_highCoordinate {κ ξ r n α β b r' n' α' β' c : V}
    [IsOrdinal κ] (hξ : ξ ⊆ κ)
    (hr : r ∈ levyCollapse κ) (hn : n ∈ (ω : V)) (hα : α ∈ κ) (hξα : ξ ⊆ α) (hωα : (ω : V) ⊆ α)
    (hmem : ⟨⟨n, α⟩ₖ, β⟩ₖ ∈ r)
    (hb : b ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hbr : b ⊆ coneRegular (levyCollapse κ) (levyOrder κ) r)
    (hr' : r' ∈ levyCollapse κ) (hn' : n' ∈ (ω : V)) (hα' : α' ∈ κ) (hξα' : ξ ⊆ α')
    (hωα' : (ω : V) ⊆ α') (hmem' : ⟨⟨n', α'⟩ₖ, β'⟩ₖ ∈ r')
    (hc : c ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hcr : c ⊆ coneRegular (levyCollapse κ) (levyOrder κ) r') :
    levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b) =
      levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) c) := by
  rw [levyTrace_forcingNegation_eq_top hξ hr hn hα hξα hωα hmem hb hbr,
    levyTrace_forcingNegation_eq_top hξ hr' hn' hα' hξα' hωα' hmem' hc hcr]

end ZFVP
