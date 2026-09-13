import ZFVP.ModelTheory.LevyNameSupportBound
import ZFVP.ModelTheory.LevyGaloisFactor

/-! One ordinal `ξ < κ` below which every base support value of a small family is determined.

`ZFVP/ModelTheory/LevyNameSupportBound.lean` bounds the conditions occurring in a set of nice
names, and needs the names to be single valued for that: a nice name over the Boolean completion
has downward closed fibers, so it can be as large as the completion and its conditions need not
be few.

The Solovay argument does not need the conditions of the names. The lifting lemma
`booleanLift_mem_forcedStabilizer_of_fixes_supportValuesBase` asks only that the base
automorphism fix the base support values `supportValuesBase P R one K E`, one regular set of `P`
per pair in `K ×ˢ E`. There are at most `|K| * |E|` of them whatever the names look like, so for
`K` and `E` small below `κ` a single `ξ < κ` determines all of them, and every row permutation
above that `ξ` fixes them. That makes the route to the forced stabilizer unconditional for small
supports, with no hypothesis on the fibers of the names.

The base support values are regular sets, not conditions of the completion: one of them can be
empty. `levy_exists_determined_below_of_small_regular` is therefore the variant of
`levy_exists_determined_below_of_small` for a small set of regular sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Finite sets are small -/

/-- An internally finite set injects into a natural number. -/
theorem cardLE_natural_of_internallyFinite {E : V} (hE : IsInternallyFinite E) :
    ∃ n ∈ (ω : V), E ≤# n := by
  obtain ⟨n, hn, hEn⟩ := hE
  exact ⟨n, hn, hEn.le⟩

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

/-! ### The base support values of a small family are few -/

include hAC hU hc hω hκ in
/-- The base support values of `K` and `E` are indexed by `K ×ˢ E`, so for `K` and `E` of size
below `κ` there are fewer than `κ` of them. -/
theorem supportValuesBase_small {K E ν μ : V} (hν : ν ∈ κ) (hμ : μ ∈ κ)
    (hK : K ≤# ν) (hE : E ≤# μ) :
    ∃ θ ∈ κ, supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E ≤# θ := by
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  obtain ⟨θ, hθ, hle⟩ := regularCardinal_ordinal_prod_small hreg hμ hν
  refine ⟨θ, hθ, ?_⟩
  have hrepl : supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E ≤# K ×ˢ E := by
    unfold supportValuesBase
    exact repl_cardLE hAC _ _ _
  exact hrepl.trans ((prod_cardLE_prod hK hE).trans hle)

/-! ### One ordinal determining a small set of regular sets -/

include hAC hU hc hω hκ in
/-- A set of regular sets of the Levy collapse of size below `κ` is determined below one ordinal
`ξ < κ`. Same selector argument as `levy_exists_determined_below_of_small`, but for regular sets
rather than conditions of the completion, so the empty regular set is allowed. -/
theorem levy_exists_determined_below_of_small_regular {D μ : V}
    (hD : D ⊆ regularSets (levyCollapse κ) (levyOrder κ)) (hμ : μ ∈ κ) (hDμ : D ≤# μ) :
    ∃ ξ ∈ κ, ∀ d ∈ D, IsLevyDeterminedBelow κ ξ d := by
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  have hne : ∀ d ∈ D, IsNonempty (levyDeterminingOrdinals κ d) := by
    intro d hd
    obtain ⟨ξ, hξ, hdet⟩ := levy_regular_exists_determined_below hAC hU hc hω hκ
      ((mem_regularSets_iff _ _ _).mp (hD d hd))
    exact ⟨ξ, (mem_levyDeterminingOrdinals_iff κ d ξ).mpr ⟨hξ, hdet⟩⟩
  obtain ⟨f, hf, hdom, hval⟩ := choice_for_definable_family hAC D _
    (levyDeterminingOrdinals_definable_one κ) hne
  have hS : range f ⊆ κ := by
    intro ξ hξ
    obtain ⟨d, hdξ⟩ := mem_range_iff.mp hξ
    have hd : d ∈ D := hdom ▸ mem_domain_of_kpair_mem hdξ
    have hv := hval d hd
    rw [value_eq_of_kpair_mem hdξ] at hv
    exact ((mem_levyDeterminingOrdinals_iff _ _ _).mp hv).1
  have hSle : range f ≤# μ :=
    (cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC D)
      (function_mem_of_isFunction' hdom rfl) rfl).trans hDμ
  obtain ⟨ξ, hξ, hsub⟩ := regular_small_subset_bounded hreg hS hμ hSle
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  refine ⟨ξ, hξ, fun d hd ↦ ?_⟩
  have hfd := (mem_levyDeterminingOrdinals_iff _ _ _).mp (hval d hd)
  have hmem : f ‘ d ∈ ξ := hsub _ (mem_range_of_kpair_mem (kpair_value_mem (hdom ▸ hd)))
  exact levy_determinedBelow_mono (IsOrdinal.toIsTransitive.transitive _ hmem) hfd.2

include hAC hU hc hω hκ in
/-- One ordinal `ξ < κ` below which every base support value of a small `K` and a small `E` is
determined. No hypothesis on the names in `E`. -/
theorem levy_exists_determined_below_supportValuesBase {K E ν μ : V} (hν : ν ∈ κ) (hμ : μ ∈ κ)
    (hK : K ≤# ν) (hE : E ≤# μ) :
    ∃ ξ ∈ κ, ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E,
      IsLevyDeterminedBelow κ ξ a := by
  obtain ⟨θ, hθ, hle⟩ := supportValuesBase_small hAC hU hc hω hκ hν hμ hK hE
  exact levy_exists_determined_below_of_small_regular hAC hU hc hω hκ
    (supportValuesBase_subset_regularSets (levyCollapse_poset κ).1 _ K E) hθ hle

include hAC hU hc hω hκ in
/-- The case used in the Solovay argument: codes `ω × ω` and an internally finite set of names.
The base support values are regular whatever the names are, so nothing else is assumed. -/
theorem levy_exists_determined_below_finite_support {E : V} (hEfin : IsInternallyFinite E) :
    ∃ ξ ∈ κ, ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
      ((ω : V) ×ˢ (ω : V)) E, IsLevyDeterminedBelow κ ξ a := by
  obtain ⟨n, hn, hEn⟩ := cardLE_natural_of_internallyFinite hEfin
  have hprod : (ω : V) ×ˢ (ω : V) ≤# (ω : V) := by
    have h := ordinal_prod_cardLE_union_omega (V := V) (ω : V)
    rwa [ordinal_union_omega_eq (subset_refl (ω : V))] at h
  exact levy_exists_determined_below_supportValuesBase hAC hU hc hω hκ hω
    (IsOrdinal.toIsTransitive.mem_trans hn hω) hprod hEn

end

/-! ### From determined support values to the forced stabilizer -/

/-- If every base support value of `K` and `E` is determined below `ξ`, then the lift of every row
permutation above `ξ` lies in the forced stabilizer of `E`. -/
theorem levy_rowPermutations_in_forcedStabilizer_of_determined {κ ξ K E : V}
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) K σ)
    (hdet : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ) K E,
      IsLevyDeterminedBelow κ ξ a)
    {s : V} (hs : IsInternalPermutation (ω : V) s) :
    booleanLift (levyCollapse κ) (levyOrder κ) (levyPermutation κ ξ s) ∈
      forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))) E := by
  refine booleanLift_mem_forcedStabilizer_of_fixes_supportValuesBase
    ⟨∅, empty_mem_levyCollapse κ⟩ (levyCollapse_poset κ).1 (levyPermutation_automorphism hs)
    hE (fun a ha ↦ ?_)
  have hareg : IsForcingRegular (levyCollapse κ) (levyOrder κ) a :=
    (mem_regularSets_iff _ _ _).mp
      (supportValuesBase_subset_regularSets (levyCollapse_poset κ).1 _ K E a ha)
  exact levyPermutation_imageAction_eq_self_of_determined hs hareg.1 (hdet a ha)

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hAC hU hc hω hκ in
/-- For a finite set of saturated nice names over `ω × ω` there is an ordinal `ξ < κ` at which
every row permutation lifts into the forced stabilizer of the names. The names are arbitrary
apart from being saturated nice names, which is what the lifting lemma itself asks for. -/
theorem levy_exists_rowPermutations_in_forcedStabilizer_finite {E : V}
    (hEfin : IsInternallyFinite E)
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ) :
    ∃ ξ ∈ κ, ∀ s, IsInternalPermutation (ω : V) s →
      booleanLift (levyCollapse κ) (levyOrder κ) (levyPermutation κ ξ s) ∈
        forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ))) E := by
  obtain ⟨ξ, hξ, hdet⟩ := levy_exists_determined_below_finite_support hAC hU hc hω hκ hEfin
  exact ⟨ξ, hξ, fun s hs ↦ levy_rowPermutations_in_forcedStabilizer_of_determined hE hdet hs⟩

end

end ZFVP
