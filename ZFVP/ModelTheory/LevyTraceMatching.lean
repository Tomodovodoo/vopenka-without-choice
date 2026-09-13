import ZFVP.ModelTheory.LevyTraceProjection
import ZFVP.ModelTheory.LevySupportValueBound
import ZFVP.ModelTheory.LevyComplementRefutation

/-! Bridges between the trace vocabulary and the support value vocabulary.

The Solovay corollary chain states its hypotheses as "the same determined sets meet `b` and `b'`",
while ZFVP/ModelTheory/LevyTraceProjection.lean works with the projection `levyTrace κ ξ`. The two
say the same thing:

* `levyTrace_eq_of_inter_determined_iff`: matching over `levyDeterminedAlgebra κ ξ` gives equal
  traces.
* `inter_eq_empty_iff_of_levyTrace_eq`: equal traces give matching over the algebra.

`supportValuesBase_subset_levyDeterminedAlgebra` puts the base support values of a family in the
algebra once they are determined below `ξ`, which is what
`levy_exists_determined_below_finite_support` supplies.

`exists_coneIsomorphism_of_both_empty` settles the degenerate case of a cone isomorphism: when
both complements are zero the empty function works.

The clause `forcingNegation P R b = ∅ ↔ forcingNegation P R c = ∅` does not follow from
`levyTrace κ ξ b = levyTrace κ ξ b'`; see the comment on
`forcingNegation_eq_empty_iff_of_levyTrace_forcingNegation_eq` for the counterexample. It does
follow from equality of the traces of the two complements, and that is what is proved here. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Missing the negation of a regular set -/

/-- A downward closed set of conditions that misses the negation of a regular set is contained in
that regular set. A condition of `A` outside `B` has an extension in the negation of `B`, and that
extension is still in `A`. -/
theorem subset_of_inter_forcingNegation_eq_empty {P R A B : V} (hA : A ⊆ P)
    (hAd : IsForcingDownwardClosed P R A) (hB : IsForcingRegular P R B)
    (h : A ∩ forcingNegation P R B = (∅ : V)) : A ⊆ B := by
  intro x hx
  by_contra hxB
  obtain ⟨q, hq, hqx⟩ := exists_forcingNegation_of_not_mem (hA x hx) hxB hB.2.2
  have hqA : q ∈ A := hAd x hx q (forcingNegation_subset _ _ _ q hq) hqx
  have hmem : q ∈ A ∩ forcingNegation P R B := mem_inter_iff.mpr ⟨hqA, hq⟩
  rw [h] at hmem
  exact not_mem_empty hmem

/-- Comparison inside the algebra of sets determined below `ξ`: if every determined set missing
`Y` also misses `X`, then `X` is below `Y`. The witness is `X ∩ ¬Y`, which is determined. -/
theorem levy_subset_of_inter_eq_empty_imp {κ ξ X Y : V} (hX : X ∈ levyDeterminedAlgebra κ ξ)
    (hY : Y ∈ levyDeterminedAlgebra κ ξ)
    (h : ∀ a, a ∈ levyDeterminedAlgebra κ ξ → a ∩ Y = (∅ : V) → a ∩ X = (∅ : V)) : X ⊆ Y := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  obtain ⟨hXreg, -⟩ := (mem_levyDeterminedAlgebra_iff _ _ _).mp hX
  obtain ⟨hYreg, -⟩ := (mem_levyDeterminedAlgebra_iff _ _ _).mp hY
  have hN : forcingNegation (levyCollapse κ) (levyOrder κ) Y ∈ levyDeterminedAlgebra κ ξ :=
    (levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.1 Y hY
  have halg : X ∩ forcingNegation (levyCollapse κ) (levyOrder κ) Y ∈ levyDeterminedAlgebra κ ξ :=
    inter_mem_levyDeterminedAlgebra hX hN
  have hmissY : (X ∩ forcingNegation (levyCollapse κ) (levyOrder κ) Y) ∩ Y = (∅ : V) := by
    refine mem_ext (fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ (not_mem_empty hz).elim⟩)
    obtain ⟨hz1, hzY⟩ := mem_inter_iff.mp hz
    exact absurd hzY (forcingNegation_disjoint hR (mem_inter_iff.mp hz1).2)
  have hmissX := h _ halg hmissY
  refine subset_of_inter_forcingNegation_eq_empty hXreg.1 hXreg.2.1 hYreg ?_
  refine subset_empty_iff_eq_empty.mp (fun z hz ↦ ?_)
  have hmem : z ∈ (X ∩ forcingNegation (levyCollapse κ) (levyOrder κ) Y) ∩ X :=
    mem_inter_iff.mpr ⟨hz, (mem_inter_iff.mp hz).1⟩
  rw [hmissX] at hmem
  exact hmem

/-! ### Matching over the algebra and equality of traces -/

/-- If the same determined sets meet `b` and `b'`, the two have the same trace. -/
theorem levyTrace_eq_of_inter_determined_iff {κ ξ b b' : V} (hξ : ξ ⊆ κ)
    (hb : IsForcingRegular (levyCollapse κ) (levyOrder κ) b)
    (hb' : IsForcingRegular (levyCollapse κ) (levyOrder κ) b')
    (h : ∀ a, a ∈ levyDeterminedAlgebra κ ξ → (a ∩ b = (∅ : V) ↔ a ∩ b' = (∅ : V))) :
    levyTrace κ ξ b = levyTrace κ ξ b' := by
  have hT : levyTrace κ ξ b ∈ levyDeterminedAlgebra κ ξ :=
    levyTrace_mem_levyDeterminedAlgebra hξ hb.1
  have hT' : levyTrace κ ξ b' ∈ levyDeterminedAlgebra κ ξ :=
    levyTrace_mem_levyDeterminedAlgebra hξ hb'.1
  have key : ∀ a, a ∈ levyDeterminedAlgebra κ ξ →
      (a ∩ levyTrace κ ξ b = (∅ : V) ↔ a ∩ levyTrace κ ξ b' = (∅ : V)) := by
    intro a ha
    rw [← inter_determined_eq_empty_iff_levyTrace ha hb.1 hb.2.1,
      ← inter_determined_eq_empty_iff_levyTrace ha hb'.1 hb'.2.1]
    exact h a ha
  refine SetTheory.subset_antisymm ?_ ?_
  · exact levy_subset_of_inter_eq_empty_imp hT hT' (fun a ha h1 ↦ (key a ha).mpr h1)
  · exact levy_subset_of_inter_eq_empty_imp hT' hT (fun a ha h1 ↦ (key a ha).mp h1)

/-- The converse: equal traces make every determined set meet `b` and `b'` alike. -/
theorem inter_eq_empty_iff_of_levyTrace_eq {κ ξ b b' a : V} (hξ : ξ ⊆ κ)
    (hb : IsForcingRegular (levyCollapse κ) (levyOrder κ) b)
    (hb' : IsForcingRegular (levyCollapse κ) (levyOrder κ) b')
    (ha : a ∈ levyDeterminedAlgebra κ ξ)
    (htr : levyTrace κ ξ b = levyTrace κ ξ b') : a ∩ b = (∅ : V) ↔ a ∩ b' = (∅ : V) := by
  rw [inter_determined_eq_empty_iff_levyTrace ha hb.1 hb.2.1,
    inter_determined_eq_empty_iff_levyTrace ha hb'.1 hb'.2.1, htr]

/-! ### The degenerate clauses -/

/-- Equal traces mean the two sets are empty together. -/
theorem eq_empty_iff_of_levyTrace_eq {κ ξ b b' : V} (hb : b ⊆ levyCollapse κ)
    (hb' : b' ⊆ levyCollapse κ) (htr : levyTrace κ ξ b = levyTrace κ ξ b') :
    b = (∅ : V) ↔ b' = (∅ : V) := by
  rw [← levyTrace_eq_empty_iff hb, ← levyTrace_eq_empty_iff hb', htr]

/-- The complements are empty together as soon as they have the same trace.

The hypothesis has to be about the traces of the complements. From `levyTrace κ ξ b =
levyTrace κ ξ b'` alone the conclusion fails: take `ξ = ∅`, so that a condition has empty
`ξ`-part and every nonempty set of conditions has trace the whole poset. With `b` the whole
collapse and `b'` the cone of a nontrivial condition the traces agree, while `¬b` is empty and
`¬b'` is not. The trace is a projection, and a projection does not commute with negation. -/
theorem forcingNegation_eq_empty_iff_of_levyTrace_forcingNegation_eq {κ ξ b b' : V}
    (htr : levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b) =
      levyTrace κ ξ (forcingNegation (levyCollapse κ) (levyOrder κ) b')) :
    forcingNegation (levyCollapse κ) (levyOrder κ) b = (∅ : V) ↔
      forcingNegation (levyCollapse κ) (levyOrder κ) b' = (∅ : V) :=
  eq_empty_iff_of_levyTrace_eq (forcingNegation_subset _ _ _) (forcingNegation_subset _ _ _) htr

/-! ### Base support values are determined sets -/

/-- Base support values are regular, so once they are determined below `ξ` they are members of the
algebra of sets determined below `ξ`. -/
theorem supportValuesBase_subset_levyDeterminedAlgebra {κ ξ K E : V}
    (hdet : ∀ a, a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E →
      IsLevyDeterminedBelow κ ξ a) :
    supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E ⊆
      levyDeterminedAlgebra κ ξ := by
  intro a ha
  exact (mem_levyDeterminedAlgebra_iff _ _ _).mpr
    ⟨(mem_regularSets_iff _ _ _).mp
      (supportValuesBase_subset_regularSets (levyCollapse_poset κ).1 _ K E a ha), hdet a ha⟩

/-! ### The empty case of a cone isomorphism -/

/-- If both complements are zero, the empty function is an isomorphism of the two complement cones
and transports the parts below the complements correctly, both being empty. -/
theorem exists_coneIsomorphism_of_both_empty {P R b c : V}
    (hb : forcingNegation P R b = (∅ : V)) (hc : forcingNegation P R c = (∅ : V)) :
    ∃ g, IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R b))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R b)))
      (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R c))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R c))) g ∧
      ∀ a, coneImage P R (forcingNegation P R b) g (a ∩ forcingNegation P R b) =
        a ∩ forcingNegation P R c := by
  refine ⟨(∅ : V), ?_, ?_⟩
  · rw [hb, hc, forcingCone_booleanOrder_empty]
    refine ⟨mem_function_iff.mpr ⟨empty_subset _, fun x hx ↦ (not_mem_empty hx).elim⟩,
      fun x₁ x₂ y h _ ↦ (not_mem_empty h).elim, range_empty_eq,
      fun p hp ↦ (not_mem_empty hp).elim⟩
  · intro a
    rw [hb, hc, inter_empty, coneImage_empty]

end ZFVP
