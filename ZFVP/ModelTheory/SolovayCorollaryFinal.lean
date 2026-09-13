import ZFVP.ModelTheory.SolovaySymmetricRange
import ZFVP.ModelTheory.SolovayHODInRange

/-! The paper's `cor:Solovay` with the reverse inclusion discharged.

`cor:Solovay` is now proved with no open hypothesis at all, as
`ZFVP.Unconditional.solovay_corollary` in `ZFVP/ModelTheory/SolovayCorollaryUnconditional.lean`;
the conditional export here is kept as the record of the reduction, so the notes below say where
that reduction stood, not what is still missing.

`ZFVP.ModelTheory.SolovaySymmetricRange` states `lem:Solovay-symmetric` and its corollary with two
open hypotheses, `hpt` for the forward inclusion and `hnm` for the reverse one.
`ZFVP.ModelTheory.SolovayHODInRange` proves the reverse inclusion outright, as `hod_subset_range`.
This module reassembles the range equality, the Vopěnka instance and the corollary from that proof,
leaving `hpt` as the only hypothesis.

The reverse hypothesis is not discharged in the form `hnm` has in `SolovaySymmetricRange`, because
that form is false. `hnm` asks that every set of the extension definable from ground sets, reals and
ordinals be in the range. The double power set of `ω̌` computed in the extension is definable with no
parameters, and under choice in the ground model it has members, for instance a well ordering of the
reals, that are not in the symmetric model; the range is transitive, so the double power set is not
in it either. What is true, and what `hod_subset_range` proves, is the hereditary form: a set all of
whose members in the transitive closure are so definable is in the range. That is the form `IsHOD`
supplies, so nothing is lost.

### What is left

`hpt` is the only remaining hypothesis of `solovay_corollary_final`:

  `∀ x : (levySolovayContext κ hG).Model,
     (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x)`

Mathematically it is the forward half of Karagila and Schilhan, Lemma 9.3: the value of a
hereditarily symmetric name is definable in the extension from the reals in a finite support of the
name, the name itself as a ground set, and ordinals.

Two concrete steps are missing for it. `niceSymmetric_exists_support` gives a hereditarily symmetric
name a finite support of saturated nice names, and `supportAlgebra_fixed_of_forcedStabilizer` says
the support group fixes the complete subalgebra those names generate elementwise. Turning that into
a definition of the value needs, first, the Galois closure of the finitely generated support
subalgebra of the Levy Boolean completion, that is the statement that the elements fixed by the
support group are exactly the elements of that subalgebra; and second, the restriction of the name
valuation to that subalgebra, so that the value of the name is computed by the forcing relation read
inside the subalgebra alone. Neither is in the library yet. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- `lem:Solovay-symmetric` from the forward hypothesis alone: the range of the comparison map is
exactly the `IsHOD` sets. The forward inclusion is `range_subset_hod_of_pointwise`, the reverse one
is `hod_subset_range`. -/
theorem solovay_symmetric_range_of_pointwise
    (hpt : ∀ x : (levySolovayContext κ hG).Model,
      (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x)) :
    Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)} :=
  Set.Subset.antisymm (range_subset_hod_of_pointwise hAC hU hc hω hκ hG hpt)
    (hod_subset_range hAC hU hc hω hκ hG)

include hAC hU hc hω hκ in
/-- Vopěnka's Principle in `Sol`, from the forward hypothesis alone. -/
theorem solovay_vopenkaInstance_of_pointwise
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (hpt : ∀ x : (levySolovayContext κ hG).Model,
      (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x))
    (φ : SetTheorySemisentence 2) :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    VopenkaInstance (V := SolovayHOD κ hG) φ :=
  solovay_vopenkaInstance_of_range hAC hU hc hω hκ hG hVP
    (solovay_symmetric_range_of_pointwise hAC hU hc hω hκ hG hpt) φ

include hAC hU hc hω hκ in
/-- `cor:Solovay` with the forward hypothesis `hpt` as its only open assumption. Clauses are in the
order of the paper's statement. -/
theorem solovay_corollary_final
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (hpt : ∀ x : (levySolovayContext κ hG).Model,
      (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x)) :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    (SolovayHOD κ hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 ∧
    (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := SolovayHOD κ hG) φ) ∧
    InternalDependentChoice (SolovayHOD κ hG) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → IsLebesgueMeasurable X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → BaireProperty X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → PerfectSetProperty X) ∧
    ¬ InternalChoice (SolovayHOD κ hG) ∧
    hartogsNumber (ω : SolovayHOD κ hG) = solovayCheck hAC hU hc hω hκ hG κ ∧
    IsNonprincipalSetUltrafilter (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) ∧
    IsOrdinalComplete (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) :=
  solovay_corollary hAC hU hc hω hκ hG hVP
    (solovay_symmetric_range_of_pointwise hAC hU hc hω hκ hG hpt)

end

end ZFVP
