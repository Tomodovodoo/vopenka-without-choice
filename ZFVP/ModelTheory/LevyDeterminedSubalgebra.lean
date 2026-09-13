import ZFVP.ModelTheory.LevyGaloisStep
import ZFVP.ModelTheory.BooleanAntichainClosure
import ZFVP.SetTheory.LevyCollapseSmallSets

/-! The algebra of regular sets of the Levy collapse determined below an ordinal `ξ`.

`IsLevyDeterminedBelow κ ξ d` says membership in `d` only depends on the part of a condition
below `ξ`. The regular sets with this property form a complete subalgebra of `RO(Coll(ω, <κ))`
(`levyDeterminedAlgebra_isCompleteSubalgebra`), and for `ξ ∈ κ` with `κ` measurable it has size
below `κ` (`levyDeterminedAlgebra_small`), because a determined regular set is recovered from its
trace on the subcollapse `Coll(ω, <ξ)`.

Completeness runs through the row permutations above `ξ`: a regular set is determined below `ξ`
exactly when every such permutation fixes it (`levy_determined_iff_permutations_fixed`), and the
action of a permutation commutes with negation and with regular joins. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Tail homogeneity without an ordinality hypothesis on `ξ` -/

/-- Variant of `levyCut_mem_of_rowPermutations_fixed` that needs neither `ξ ⊆ κ` nor that `ξ` is
an ordinal: the part below `ξ` of a condition of `d` is again in `d`. -/
theorem levyCut_mem_of_rowPermutations_fixed' {κ ξ d : V}
    (hd : IsForcingRegular (levyCollapse κ) (levyOrder κ) d)
    (hfix : ∀ s, IsInternalPermutation (ω : V) s → imageAction (levyPermutation κ ξ s) d = d)
    {p : V} (hp : p ∈ d) : levyCut ξ p ∈ d := by
  have hpP : p ∈ levyCollapse κ := hd.1 p hp
  have hcutP : levyCut ξ p ∈ levyCollapse κ := levyCollapse_subset hpP (levyCut_subset ξ p)
  refine hd.2.2 _ hcutP (fun q hq hqcut ↦ ?_)
  have hqsub : levyCut ξ p ⊆ q := ((pair_mem_reverseInclusionOrder _ _ _).mp hqcut).2.2
  obtain ⟨s, hs, hmove⟩ := exists_permutation_moving (levyRows_finite (β := ξ) hpP)
    (levyRows_subset ξ p) (levyRows_finite (β := ξ) hq) (levyRows_subset ξ q)
  have hπ := levyPermutation_automorphism (κ := κ) (β := ξ) hs
  have hπp : (levyPermutation κ ξ s) ‘ p ∈ levyCollapse κ := function_value_mem hπ.1 hpP
  have hcompat : ∀ x y z, ⟨x, y⟩ₖ ∈ (levyPermutation κ ξ s) ‘ p → ⟨x, z⟩ₖ ∈ q → y = z := by
    rw [levyPermutation_value hpP]
    exact levyPermutation_compatible hs hpP hq hqsub hmove
  have hu : (levyPermutation κ ξ s) ‘ p ∪ q ∈ levyCollapse κ :=
    levyCollapse_union hπp hq hcompat
  have hπpd : (levyPermutation κ ξ s) ‘ p ∈ d := by
    rw [← hfix s hs]
    exact (mem_imageAction_iff _ _ _).mpr ⟨p, hp, rfl⟩
  refine ⟨(levyPermutation κ ξ s) ‘ p ∪ q, hd.2.1 _ hπpd _ hu ?_, ?_⟩
  · exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hπp, subset_union_left _ _⟩
  · exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hq, subset_union_right _ _⟩

/-- A regular set is determined below `ξ` exactly when every row permutation above `ξ` fixes it. -/
theorem levy_determined_iff_permutations_fixed {κ ξ d : V}
    (hd : IsForcingRegular (levyCollapse κ) (levyOrder κ) d) :
    IsLevyDeterminedBelow κ ξ d ↔
      ∀ s, IsInternalPermutation (ω : V) s → imageAction (levyPermutation κ ξ s) d = d := by
  refine ⟨fun h s hs ↦ levyPermutation_imageAction_eq_self_of_determined hs hd.1 h, fun h ↦ ?_⟩
  intro p hp
  refine ⟨fun hpd ↦ levyCut_mem_of_rowPermutations_fixed' hd h hpd, fun hcut ↦ ?_⟩
  have hcutP : levyCut ξ p ∈ levyCollapse κ := levyCollapse_subset hp (levyCut_subset ξ p)
  exact hd.2.1 _ hcut p hp
    ((pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hcutP, levyCut_subset ξ p⟩)

/-! ### The algebra of sets determined below `ξ` -/

instance isLevyDeterminedBelow_definable (κ ξ : V) :
    ℒₛₑₜ-predicate[V] (IsLevyDeterminedBelow κ ξ) := by
  unfold IsLevyDeterminedBelow levyCut
  definability

/-- The regular sets of `Coll(ω, <κ)` that are determined below `ξ`. -/
noncomputable def levyDeterminedAlgebra (κ ξ : V) : V :=
  {d ∈ regularSets (levyCollapse κ) (levyOrder κ) ; IsLevyDeterminedBelow κ ξ d}

theorem mem_levyDeterminedAlgebra_iff (κ ξ d : V) :
    d ∈ levyDeterminedAlgebra κ ξ ↔
      IsForcingRegular (levyCollapse κ) (levyOrder κ) d ∧ IsLevyDeterminedBelow κ ξ d := by
  rw [levyDeterminedAlgebra, mem_sep_iff, mem_regularSets_iff]

theorem levyDeterminedAlgebra_subset (κ ξ : V) :
    levyDeterminedAlgebra κ ξ ⊆ regularSets (levyCollapse κ) (levyOrder κ) := sep_subset

/-- Members of the algebra are sets of conditions. -/
theorem levyDeterminedAlgebra_subset_poset {κ ξ d : V} (hd : d ∈ levyDeterminedAlgebra κ ξ) :
    d ⊆ levyCollapse κ := ((mem_levyDeterminedAlgebra_iff κ ξ d).mp hd).1.1

/-! ### It is a complete subalgebra -/

theorem levyDeterminedAlgebra_isCompleteSubalgebra (κ ξ : V) :
    IsCompleteSubalgebra (levyCollapse κ) (levyOrder κ) (levyDeterminedAlgebra κ ξ) := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  refine ⟨levyDeterminedAlgebra_subset κ ξ, ?_, ?_, ?_⟩
  · refine (mem_levyDeterminedAlgebra_iff _ _ _).mpr ⟨forcingRegular_top _ _, fun p hp ↦ ?_⟩
    exact ⟨fun _ ↦ levyCollapse_subset hp (levyCut_subset ξ p), fun _ ↦ hp⟩
  · intro d hd
    obtain ⟨hdreg, hdet⟩ := (mem_levyDeterminedAlgebra_iff _ _ _).mp hd
    have hfix := (levy_determined_iff_permutations_fixed hdreg).mp hdet
    refine (mem_levyDeterminedAlgebra_iff _ _ _).mpr
      ⟨forcingNegation_regular hR hdreg.2.1, ?_⟩
    refine (levy_determined_iff_permutations_fixed
      (forcingNegation_regular hR hdreg.2.1)).mpr (fun s hs ↦ ?_)
    rw [forcingNegation_image (levyPermutation_automorphism hs) hdreg.1, hfix s hs]
  · intro X hX
    have hXreg : ∀ A ∈ X, IsForcingRegular (levyCollapse κ) (levyOrder κ) A := fun A hA ↦
      ((mem_levyDeterminedAlgebra_iff _ _ _).mp (hX A hA)).1
    have hjreg : IsForcingRegular (levyCollapse κ) (levyOrder κ)
        (regularJoin (levyCollapse κ) (levyOrder κ) X) :=
      regularJoin_regular hR (fun A hA ↦ (hXreg A hA).1)
    refine (mem_levyDeterminedAlgebra_iff _ _ _).mpr ⟨hjreg, ?_⟩
    refine (levy_determined_iff_permutations_fixed hjreg).mpr (fun s hs ↦ ?_)
    have hfam : imageFamily (levyPermutation κ ξ s) X = X := by
      refine imageFamily_eq_self (fun A hA ↦ ?_)
      exact (levy_determined_iff_permutations_fixed (hXreg A hA)).mp
        ((mem_levyDeterminedAlgebra_iff _ _ _).mp (hX A hA)).2 s hs
    rw [regularJoin_image (levyPermutation_automorphism hs) (fun A hA ↦ (hXreg A hA).1), hfam]

/-! ### It is small -/

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hAC hU hc hω hκ in
/-- The algebra of sets determined below `ξ ∈ κ` has size below `κ`: a determined regular set is
recovered from its trace on the subcollapse `Coll(ω, <ξ)`. -/
theorem levyDeterminedAlgebra_small {ξ : V} (hξ : ξ ∈ κ) :
    ∃ μ ∈ κ, levyDeterminedAlgebra κ ξ ≤# μ := by
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  obtain ⟨μ₀, hμ₀, h0⟩ := levyCollapse_small hAC hU hc hω hκ hξ
  obtain ⟨μ, hμ, h1⟩ := measurable_power_bounded hAC hU hc hμ₀
  refine ⟨μ, hμ, ?_⟩
  have htrace : levyDeterminedAlgebra κ ξ ≤# ℘ (levyCollapse ξ) := by
    refine cardLE_of_injective_map (fun d ↦ d ∩ levyCollapse ξ) (by definability)
      (fun d _ ↦ mem_power_iff.mpr (fun x hx ↦ (mem_inter_iff.mp hx).2)) ?_
    intro d hd d' hd' heq
    obtain ⟨hdreg, hdet⟩ := (mem_levyDeterminedAlgebra_iff _ _ _).mp hd
    obtain ⟨hd'reg, hd'det⟩ := (mem_levyDeterminedAlgebra_iff _ _ _).mp hd'
    apply mem_ext
    intro p
    constructor
    · intro hp
      have hpP : p ∈ levyCollapse κ := hdreg.1 p hp
      have h2 : levyCut ξ p ∈ d ∩ levyCollapse ξ :=
        mem_inter_iff.mpr ⟨(hdet p hpP).mp hp, levyCut_mem hpP⟩
      rw [heq] at h2
      exact (hd'det p hpP).mpr (mem_inter_iff.mp h2).1
    · intro hp
      have hpP : p ∈ levyCollapse κ := hd'reg.1 p hp
      have h2 : levyCut ξ p ∈ d' ∩ levyCollapse ξ :=
        mem_inter_iff.mpr ⟨(hd'det p hpP).mp hp, levyCut_mem hpP⟩
      rw [← heq] at h2
      exact (hdet p hpP).mpr (mem_inter_iff.mp h2).1
  exact htrace.trans ((power_cardLE_of_cardLE h0).trans h1)

end

/-! ### Monotonicity in `ξ` -/

theorem levyCut_levyCut_of_subset {ξ ξ' p : V} (h : ξ ⊆ ξ') :
    levyCut ξ (levyCut ξ' p) = levyCut ξ p := by
  unfold levyCut
  rw [restrict_restrict_eq_restrict_inter, inter_eq_right_of_subset
    (prod_subset_prod_of_subset (subset_refl (ω : V)) h)]

theorem levyDeterminedAlgebra_mono {κ ξ ξ' : V} (h : ξ ⊆ ξ') :
    levyDeterminedAlgebra κ ξ ⊆ levyDeterminedAlgebra κ ξ' := by
  intro d hd
  obtain ⟨hdreg, hdet⟩ := (mem_levyDeterminedAlgebra_iff _ _ _).mp hd
  refine (mem_levyDeterminedAlgebra_iff _ _ _).mpr ⟨hdreg, fun p hp ↦ ?_⟩
  have hcutP : levyCut ξ' p ∈ levyCollapse κ := levyCollapse_subset hp (levyCut_subset ξ' p)
  rw [hdet p hp, ← levyCut_levyCut_of_subset (p := p) h, ← hdet _ hcutP]

end ZFVP
