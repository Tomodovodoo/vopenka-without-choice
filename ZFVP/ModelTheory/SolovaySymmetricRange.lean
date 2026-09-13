import ZFVP.ModelTheory.SolovayCorollary
import ZFVP.ModelTheory.SolovaySymmetricReals
import ZFVP.ModelTheory.SolovaySymmetricSupport
import ZFVP.ModelTheory.SolovayHODIdentification

/-! The paper's Lemma `lem:Solovay-symmetric`, cut down to two open statements.

`cor:Solovay` is now proved with no open hypothesis at all, as
`ZFVP.Unconditional.solovay_corollary` in `ZFVP/ModelTheory/SolovayCorollaryUnconditional.lean`,
where `hpt` is discharged by `ZFVP.Unconditional.groundRealDefinable_solovayInclusion`; the
conditional exports here are kept as the record of the reduction, so the notes below on the two
hypotheses say where that reduction stood, not what is still missing.

`ZFVP.ModelTheory.SolovayCorollary` assumes the whole set equality

  `Set.range (solovaySymmetricInclusion hG) = {y | IsHOD solovayPf y (solovayParam κ hG)}`

as a single hypothesis `hrange`. Here that equality is split into its two inclusions and each one
is reduced, by a complete proof, to a single statement about one point at a time:

* forward, `hpt`: the image of every element of the symmetric model is definable in the Levy
  extension from ground sets, reals and ordinals;
* backward, `hnm`: every set of the Levy extension so definable is in the range.

Everything around those two is proved. The forward reduction is the interesting one: `hpt` only
says that single images are definable, while `IsHOD` asks for hereditary definability. The gap is
closed by transitivity of the range. For `x` in the symmetric model take the transitive closure of
`{x}` computed inside the symmetric model and push it into the extension. Because the inclusion is
injective, preserves membership and is a membership end extension (`solovay_range_transitive`),
that image is a transitive set of the extension, it contains the image of `x`, and each of its
members is again an image, so `hpt` applies to all of them. Then
`hereditarilyGroundRealDefinable_of_transitive` upgrades to hereditary definability and
`solovay_isHOD_iff` converts to `IsHOD`. The definable-class variant
`hereditarilyGroundRealDefinable_of_definable_transitive` is not usable here: the range is a
`Set` of the ambient type theory, not a class of the extension given by a set formula.

The backward reduction is immediate: `solovay_isHOD_iff` turns `IsHOD` into hereditary
definability and `groundRealDefinable_of_hereditarily` drops "hereditary".

What is known about the two hypotheses is recorded at the end: `hpt` holds for the values of
saturated nice names, for checks and for the ordinals of the symmetric model; `hnm` holds for all
Solovay parameters, that is for checks, for subsets of `ω̌` and for ordinals.

The two statements that stay open, and why:

* `hpt`. A general element of the symmetric model is the value of an arbitrary hereditarily
  symmetric name, not of a saturated nice name. `niceSymmetric_exists_support` gives such a name a
  finite support `E` of saturated nice names, and `supportAlgebra_fixed_of_forcedStabilizer` says
  the support group fixes the complete subalgebra those names generate elementwise. Turning that
  into a definition of the value from the name, the reals in the support and ordinals is the Galois
  step for the Levy Boolean completion (the value is computed by the forcing relation restricted to
  the fixed subalgebra), which is not available in the library yet.
* `hnm`. Going the other way needs, for a set of the extension defined by a formula with ground,
  real and ordinal parameters, a name that is hereditarily symmetric for the nice-name filter. The
  only construction available produces names for subsets of a checked ground set
  (`exists_saturatedNiceName`); an arbitrary definable set needs a class-name construction together
  with an induction on rank inside the extension, which the present definability tools do not
  support.

Neither is asserted anywhere in this file: both appear only as ordinary hypotheses of the exported
theorems, so a later module can discharge them and the corollary becomes unconditional. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable (A : ForcingContext V)

/-! ### A transitive witness inside the range -/

/-- The transitive closure of `{x}` computed in the Solovay symmetric model, read as a set of the
extension. -/
noncomputable def solovayWitness (x : A.solovayContext.Model) : A.Model :=
  A.solovayInclusion (transitiveClosure ({x} : A.solovayContext.Model))

/-- The members of the witness are exactly the images of the members of the transitive closure.
This is the end extension property of the inclusion. -/
theorem mem_solovayWitness_iff (x : A.solovayContext.Model) (w : A.Model) :
    w ∈ A.solovayWitness x ↔ ∃ z : A.solovayContext.Model,
      z ∈ transitiveClosure ({x} : A.solovayContext.Model) ∧ w = A.solovayInclusion z := by
  constructor
  · intro hw
    obtain ⟨z, rfl⟩ := A.solovay_range_transitive _ ⟨_, rfl⟩ w hw
    exact ⟨z, (A.solovayInclusion_mem_iff z _).mp hw, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact (A.solovayInclusion_mem_iff z _).mpr hz

/-- The witness is a transitive set of the extension. -/
theorem solovayWitness_transitive (x : A.solovayContext.Model) :
    IsTransitive (A.solovayWitness x) := by
  refine ⟨fun u hu v hv ↦ ?_⟩
  obtain ⟨z, hz, rfl⟩ := (A.mem_solovayWitness_iff x u).mp hu
  obtain ⟨w, rfl⟩ := A.solovay_range_transitive _ ⟨z, rfl⟩ v hv
  refine (A.mem_solovayWitness_iff x _).mpr ⟨w, ?_, rfl⟩
  exact (transitiveClosure_transitive _).mem_trans ((A.solovayInclusion_mem_iff w z).mp hv) hz

theorem solovayInclusion_mem_solovayWitness (x : A.solovayContext.Model) :
    A.solovayInclusion x ∈ A.solovayWitness x :=
  (A.mem_solovayWitness_iff x _).mpr
    ⟨x, subset_transitiveClosure _ _ (mem_singleton_iff.mpr rfl), rfl⟩

/-! ### From pointwise to hereditary definability -/

/-- If every element of the Solovay symmetric model has a definable image, then every image is
hereditarily definable from ground sets, reals and ordinals. The transitive set that carries the
induction is `solovayWitness`. -/
theorem hereditarilyGroundRealDefinable_solovayInclusion
    (hpt : ∀ x : A.solovayContext.Model, A.IsGroundRealDefinable (A.solovayInclusion x))
    (x : A.solovayContext.Model) :
    A.IsHereditarilyGroundRealDefinable (A.solovayInclusion x) :=
  hereditarilyGroundRealDefinable_of_transitive A (A.solovayWitness x)
    (A.solovayWitness_transitive x)
    (fun y hy ↦ by
      obtain ⟨z, -, rfl⟩ := (A.mem_solovayWitness_iff x y).mp hy
      exact hpt z)
    (A.solovayInclusion_mem_solovayWitness x)

/-- Ground sets are images of their own checks. -/
theorem solovayInclusion_check (a : V) :
    A.solovayInclusion (A.solovayContext.check a) = A.check a :=
  A.niceInclusion_check _ a

end ForcingContext

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

omit [IsOrdinal κ] in
/-- The comparison map of `SolovayCorollary` is the inclusion of the Solovay symmetric model of
`ZFVP.ModelTheory.SolovayNiceNameValues`. -/
theorem solovaySymmetricInclusion_eq :
    solovaySymmetricInclusion (κ := κ) (hG := hG) = (levyContext κ hG).solovayInclusion := rfl

/-! ### The forward inclusion -/

include hAC hU hc hω hκ in
/-- Forward half of `lem:Solovay-symmetric`, reduced to pointwise definability: if the image of
every element of the symmetric model is definable in the Levy extension from ground sets, reals
and ordinals, then every element of the range is in `Sol`. -/
theorem range_subset_hod_of_pointwise
    (hpt : ∀ x : (levySolovayContext κ hG).Model,
      (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x)) :
    Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) ⊆
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)} := by
  rintro _ ⟨x, rfl⟩
  exact (solovay_isHOD_iff hAC hU hc hω hκ hG _).mpr
    ((levyContext κ hG).hereditarilyGroundRealDefinable_solovayInclusion hpt x)

/-! ### The reverse inclusion -/

include hAC hU hc hω hκ in
/-- Reverse half of `lem:Solovay-symmetric`, reduced to the missing name construction: if every
set of the Levy extension that is definable from ground sets, reals and ordinals is in the range,
then every element of `Sol` is in the range. -/
theorem hod_subset_range_of_names
    (hnm : ∀ x : (levyContext κ hG).Model, (levyContext κ hG).IsGroundRealDefinable x →
      x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG))) :
    {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)} ⊆
      Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) := by
  intro y hy
  exact hnm y (ForcingContext.groundRealDefinable_of_hereditarily
    ((solovay_isHOD_iff hAC hU hc hω hκ hG y).mp hy))

/-! ### The lemma -/

include hAC hU hc hω hκ in
/-- `lem:Solovay-symmetric` from the two pointwise hypotheses: the range of the comparison map is
exactly the `IsHOD` sets. -/
theorem solovay_symmetric_range
    (hpt : ∀ x : (levySolovayContext κ hG).Model,
      (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x))
    (hnm : ∀ x : (levyContext κ hG).Model, (levyContext κ hG).IsGroundRealDefinable x →
      x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG))) :
    Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)} :=
  Set.Subset.antisymm (range_subset_hod_of_pointwise hAC hU hc hω hκ hG hpt)
    (hod_subset_range_of_names hAC hU hc hω hκ hG hnm)

/-! ### The corollary, with the two hypotheses in place of the range equality -/

include hAC hU hc hω hκ in
/-- Vopěnka's Principle in `Sol`, from the two pointwise hypotheses. -/
theorem solovay_vopenkaInstance
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (hpt : ∀ x : (levySolovayContext κ hG).Model,
      (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x))
    (hnm : ∀ x : (levyContext κ hG).Model, (levyContext κ hG).IsGroundRealDefinable x →
      x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)))
    (φ : SetTheorySemisentence 2) :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    VopenkaInstance (V := SolovayHOD κ hG) φ :=
  solovay_vopenkaInstance_of_range hAC hU hc hω hκ hG hVP
    (solovay_symmetric_range hAC hU hc hω hκ hG hpt hnm) φ

include hAC hU hc hω hκ in
/-- `cor:Solovay` with the range equality replaced by the two pointwise hypotheses. Clauses are in
the order of the paper's statement. -/
theorem solovay_corollary_gapped
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (hpt : ∀ x : (levySolovayContext κ hG).Model,
      (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x))
    (hnm : ∀ x : (levyContext κ hG).Model, (levyContext κ hG).IsGroundRealDefinable x →
      x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG))) :
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
  solovay_corollary hAC hU hc hω hκ hG hVP (solovay_symmetric_range hAC hU hc hω hκ hG hpt hnm)

/-! ### What is already known about the two hypotheses -/

omit [IsOrdinal κ] in
/-- `hpt` for the values of saturated nice names: those are subsets of the checked `ω × ω`, so
they are definable from ground sets, reals and ordinals. -/
theorem groundRealDefinable_of_saturated_range_element
    (τ : (levySolovayContext κ hG).Name)
    (hτ : IsSaturatedNiceName
      (booleanConditions (levyContext κ hG).P (levyContext κ hG).R)
      (booleanOrder (levyContext κ hG).P (levyContext κ hG).R)
      (levyContext κ hG).P ((ω : V) ×ˢ (ω : V)) τ.val) :
    (levyContext κ hG).IsGroundRealDefinable
      (solovaySymmetricInclusion hG ((levySolovayContext κ hG).ofName τ)) :=
  (levyContext κ hG).groundRealDefinable_of_saturatedNiceName τ hτ

omit [IsOrdinal κ] in
/-- Since every element of the symmetric model is the value of a hereditarily symmetric name, `hpt`
is exactly the statement that all those values are definable. This is the shape the open forward
half has. -/
theorem pointwise_of_names
    (h : ∀ τ : (levySolovayContext κ hG).Name, (levyContext κ hG).IsGroundRealDefinable
      (solovaySymmetricInclusion hG ((levySolovayContext κ hG).ofName τ)))
    (x : (levySolovayContext κ hG).Model) :
    (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x) := by
  obtain ⟨τ, rfl⟩ := (levySolovayContext κ hG).ofName_surjective x
  exact h τ

omit [IsOrdinal κ] in
/-- `hpt` for ground sets: the image of a check is that check. -/
theorem groundRealDefinable_range_check (a : V) :
    (levyContext κ hG).IsGroundRealDefinable
      (solovaySymmetricInclusion hG ((levySolovayContext κ hG).check a)) := by
  have h : solovaySymmetricInclusion hG ((levySolovayContext κ hG).check a) =
      (levyContext κ hG).check a := (levyContext κ hG).solovayInclusion_check a
  rw [h]
  exact ForcingContext.groundRealDefinable_of_parameter (Or.inl ⟨a, rfl⟩)

omit [IsOrdinal κ] in
/-- `hpt` for the ordinals of the symmetric model: they are checks. -/
theorem groundRealDefinable_range_ordinal (x : (levySolovayContext κ hG).Model) [IsOrdinal x] :
    (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x) := by
  obtain ⟨β, -, rfl⟩ := (levySolovayContext κ hG).ordinal_eq_check x
  exact groundRealDefinable_range_check hG β

omit [IsOrdinal κ] in
/-- `hnm` for the Solovay parameters: checks, subsets of `ω̌` and ordinals are all in the range. -/
theorem parameters_in_range {x : (levyContext κ hG).Model}
    (hx : (levyContext κ hG).IsSolovayParameter x) :
    x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) :=
  (levyContext κ hG).solovay_parameters_mem_range hx

omit [IsOrdinal κ] in
/-- `hnm` for ground sets. -/
theorem check_in_range (a : V) :
    (levyContext κ hG).check a ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) :=
  (levyContext κ hG).solovay_check_mem_range a

omit [IsOrdinal κ] in
/-- `hnm` for the ordinals of the extension. -/
theorem ordinal_in_range (x : (levyContext κ hG).Model) [IsOrdinal x] :
    x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) :=
  (levyContext κ hG).solovay_ordinal_mem_range x

omit [IsOrdinal κ] in
/-- `hnm` for the reals of the extension. -/
theorem real_in_range {x : (levyContext κ hG).Model} (hx : x ⊆ (levyContext κ hG).check (ω : V)) :
    x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) :=
  (levyContext κ hG).subset_check_omega_mem_range hx

end

end ZFVP
