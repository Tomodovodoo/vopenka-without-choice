import ZFVP.ModelTheory.LevyHighConeTransfer

/-! The full Solovay model package from the stated Levy ground data.

Every earlier statement of the corollary carried one assumption about the Levy collapse that the
library could not yet prove: `solovay_corollary_of_transfer`, `solovay_corollary_of_aligned`,
`solovay_corollary_of_complement`, `solovay_corollary_of_cone_transfer`,
`solovay_corollary_of_traceAligned`, `solovay_corollary_of_swapConeData` and
`solovay_corollary_of_conePairAgrees` are the successive reductions of that assumption, and
`solovay_corollary_final` is the top of the chain, taking the forward hypothesis `hpt` directly.

`ZFVP.ModelTheory.LevyHighConeTransfer` closes the last of them: `levy_coneOrbitTransfer_finite`
proves the cone hypothesis for a finite support sequence outright, by arranging a high condition on
each side of the pair and building the positive isomorphism from the value map and the
complementary one from relative homogeneity below a `ξ < κ` that determines all base support
values. Feeding it to `groundRealDefinable_booleanReal_of_finite_cone` gives `hpt`, and the
corollary follows from `solovay_corollary_final`.

The exports here take the Levy block (`hAC`, `hU`, `hc`, `hω`, `hκ`, `hG`)
and Vopěnka's Principle in the ground model. The consistency implication from ZF + VP still
requires a separate construction of these ground data. The older conditional exports record
earlier proof attempts; their hypotheses are not all discharged. In particular,
`LevyComplementRefutation` refutes the hypothesis of `solovay_corollary_of_complement`.
The final proof here uses the finite high-cone construction instead. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace Unconditional

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- The forward hypothesis `hpt` of `solovay_corollary_final`, with nothing open: the value of a
hereditarily symmetric name of the Solovay system is definable in the extension from ground sets,
reals and ordinals. The cone hypothesis it needs for finite support sequences is
`levy_coneOrbitTransfer_finite`. -/
theorem groundRealDefinable_solovayInclusion (x : (levySolovayContext κ hG).Model) :
    (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x) := by
  obtain ⟨τ, rfl⟩ := (levySolovayContext κ hG).ofName_surjective x
  refine ForcingContext.groundRealDefinable_booleanReal_of_finite_cone (levyContext κ hG)
    groundFormula (p := solovayParam κ hG) ?_ ?_ (fun s n hn hsf hsdom _ ↦ ?_) τ
  · rw [solovayParam_eq_check]
    exact ForcingContext.groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
  · intro a
    exact (eval_groundFormula _ _).mpr (levy_isGround_check hAC hU hc hω hκ hG a)
  · exact levy_coneOrbitTransfer_finite hAC hU hc hω hκ hG hn hsf hsdom

include hAC hU hc hω hκ in
/-- `lem:Solovay-symmetric` with no open hypothesis: the range of the comparison map is exactly the
`IsHOD` sets. -/
theorem solovay_symmetric_range :
    Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)} :=
  solovay_symmetric_range_of_pointwise hAC hU hc hω hκ hG
    (groundRealDefinable_solovayInclusion hAC hU hc hω hκ hG)

include hAC hU hc hω hκ in
/-- Each Vopěnka instance holds in `Sol`, from ground VP and the stated Levy data. -/
theorem solovay_vopenkaInstance
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (φ : SetTheorySemisentence 2) :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    VopenkaInstance (V := SolovayHOD κ hG) φ :=
  solovay_vopenkaInstance_of_pointwise hAC hU hc hω hκ hG hVP
    (groundRealDefinable_solovayInclusion hAC hU hc hω hκ hG) φ

include hAC hU hc hω hκ in
/-- `cor:Solovay` with no open hypothesis beyond the Levy block and Vopěnka's
Principle in the ground model. Clauses are in the order of the paper's statement. -/
theorem solovay_corollary
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ) :
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
  solovay_corollary_final hAC hU hc hω hκ hG hVP
    (groundRealDefinable_solovayInclusion hAC hU hc hω hκ hG)

end

end Unconditional

end ZFVP
