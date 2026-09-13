import ZFVP.ModelTheory.SolovayHODSequences
import ZFVP.ModelTheory.SolovayHODNoChoice
import ZFVP.ModelTheory.SolovayHODUltrafilter
import ZFVP.ModelTheory.LevyGroundDefinable
import ZFVP.ModelTheory.LevySmallSetLocalization
import ZFVP.ModelTheory.LevyODLocalized
import ZFVP.ModelTheory.LevyODParameterTree
import ZFVP.ModelTheory.LevyInternalLocalization
import ZFVP.SetTheory.HODModelsZF
import ZFVP.SetTheory.HODReals

/-! The Solovay model, as one class model with one parameter.

`V` models `ZFC`, `κ` carries a nonprincipal `κ`-complete ultrafilter `U`, `G` is generic for the
Levy collapse of `κ` and `M = V[G]` is the extension. The paper's model (eq. full-Solovay) is
`Sol = HOD_{V ∪ R}^{V[G]}`, and here it is the class `HODDom solovayPf (solovayParam κ hG)`: the
sets hereditarily ordinal definable in `V[G]` from the parameter class named by `solovayPf` at the
single parameter `solovayParam κ hG`.

`solovayPf x p` is the disjunction of three clauses: `x` satisfies the ground predicate at `p`
(by Laver's theorem for the Levy collapse this says exactly that `x` is a check), `x` is a subset
of `ω`, and `x` is a member of the Cantor space. The last two are the two codings of a real; both
are needed because the landed modules ask for different ones.

The section below discharges, for this one choice of formula and parameter, every hypothesis the
landed Solovay modules carry, and then states each clause of the paper as a theorem about `Sol`
whose only hypotheses are `hAC`, `hU`, `hc`, `hω`, `hκ`, `hG` (and countability of `V` for the
perfect set property). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The parameter class -/

/-- The formula naming the Solovay parameter class: `x` lies in the ground model named by `p`, or
`x` is a subset of `ω`, or `x` is a real. -/
def solovayPf : SetTheorySemisentence 2 :=
  f“x p. !groundFormula x p ∨ x ⊆ !isω ∨ x ∈ !cantorSpaceFormula”

theorem eval_solovayPf (x p : V) :
    solovayPf.Evalb ![x, p] ↔ IsGround x p ∨ x ⊆ (ω : V) ∨ x ∈ cantorSpace V := by
  simp [solovayPf]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The single parameter of the Solovay class: the parameter of Laver's ground definability
theorem for the Levy collapse. It is itself the check of a ground set. -/
noncomputable def solovayParam (κ : V) {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G) :
    (levyContext κ hG).Model :=
  levyGroundParameter κ hG

omit [IsOrdinal κ] in
theorem solovayParam_eq_check :
    solovayParam κ hG = (levyContext κ hG).check
      ⟨hartogsNumber κ, ⟨℘ (hartogsNumber κ ×ˢ hartogsNumber κ), ℘ (hartogsNumber κ)⟩ₖ⟩ₖ := rfl

/-- The Solovay class model `Sol = HOD_{V ∪ R}^{V[G]}` of the paper. -/
abbrev SolovayHOD (κ : V) {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G) : Type _ :=
  HODDom solovayPf (solovayParam κ hG)

/-! ### Discharging the hypotheses of the landed modules -/

include hAC hU hc hω hκ in
/-- Every ground set satisfies the class formula: clause (i), by Laver's theorem. -/
theorem solovayPf_check (a : V) :
    solovayPf.Evalb ![(levyContext κ hG).check a, solovayParam κ hG] :=
  (eval_solovayPf _ _).mpr (Or.inl (levy_isGround_check hAC hU hc hω hκ hG a))

omit [IsOrdinal κ] in
/-- Every subset of `ω̌` satisfies the class formula: clause (ii). -/
theorem solovayPf_real (c : (levyContext κ hG).Model)
    (hcω : c ⊆ (levyContext κ hG).check (ω : V)) :
    solovayPf.Evalb ![c, solovayParam κ hG] := by
  refine (eval_solovayPf _ _).mpr (Or.inr (Or.inl ?_))
  rwa [(levyContext κ hG).check_omega_eq] at hcω

omit [IsOrdinal κ] in
/-- Every real of the extension is an allowed parameter: clause (iii). -/
theorem solovayPf_allowed_real (x : (levyContext κ hG).Model)
    (hx : x ∈ cantorSpace (levyContext κ hG).Model) :
    IsAllowed solovayPf x (solovayParam κ hG) :=
  Or.inr (Or.inr ((eval_solovayPf _ _).mpr (Or.inr (Or.inr hx))))

include hAC hU hc hω hκ in
/-- The parameter is allowed at itself: it is a check, so clause (i) applies to it. -/
theorem solovayPf_allowed_param :
    IsAllowed solovayPf (solovayParam κ hG) (solovayParam κ hG) :=
  Or.inr (Or.inr (solovayPf_check hAC hU hc hω hκ hG _))

include hAC hU hc hω hκ in
/-- A real of the extension lies in a bounded stage: it is a subset of the check of `ω ×ˢ 2`, a
ground set of size `ω < κ`. -/
theorem levy_cantorSpace_localized (x : (levyContext κ hG).Model)
    (hx : x ∈ cantorSpace (levyContext κ hG).Model) : IsLocalized hG x := by
  have h2ω : ((2 : ℕ) : V) ⊆ (ω : V) := IsTransitive.transitive _ two_mem_omega
  have hsub : (ω : V) ×ˢ ((2 : ℕ) : V) ⊆ (ω : V) ×ˢ (ω : V) := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    exact mem_prod_iff.mpr ⟨a, ha, b, h2ω b hb, rfl⟩
  have hQ : ((ω : V) ×ˢ ((2 : ℕ) : V)) ≤# (ω : V) :=
    CardLE.trans (cardLE_of_subset hsub) omega_prod_cardLE_omega
  refine levy_subset_check_localized hAC hU hc hω hκ hG hQ hω x ?_
  have hprod : (levyContext κ hG).check ((ω : V) ×ˢ ((2 : ℕ) : V)) =
      (levyContext κ hG).check (ω : V) ×ˢ (levyContext κ hG).check ((2 : ℕ) : V) :=
    (levyContext κ hG).checkEmbedding.map_prod _ _
  have hωc : (levyContext κ hG).check (ω : V) = (ω : (levyContext κ hG).Model) :=
    (levyContext κ hG).check_omega_eq
  have h2c : (levyContext κ hG).check ((2 : ℕ) : V) = (((2 : ℕ) : (levyContext κ hG).Model)) :=
    (levyContext κ hG).checkEmbedding.map_numeral 2
  rw [hprod, hωc, h2c]
  exact (mem_function_iff.mp hx).1

include hAC hU hc hω hκ in
/-- Every member of the parameter class lies in a bounded stage. -/
theorem solovayPf_localized (y : (levyContext κ hG).Model)
    (hy : solovayPf.Evalb ![y, solovayParam κ hG]) : IsLocalized hG y := by
  rcases (eval_solovayPf _ _).mp hy with hg | hsub | hcs
  · obtain ⟨a, rfl⟩ := levy_check_of_isGround hAC hU hc hω hκ hG hg
    exact isLocalized_check hG hω a
  · refine levy_real_localized hAC hU hc hω hκ hG y ?_
    rwa [(levyContext κ hG).check_omega_eq]
  · exact levy_cantorSpace_localized hAC hU hc hω hκ hG y hcs

include hAC hU hc hω hκ in
/-- The converse direction of the Solovay bridge for this class: an ordinal definable set of the
extension is definable from ground sets, reals and ordinals. -/
theorem solovayPf_groundRealDefinable (x : (levyContext κ hG).Model)
    (hx : IsOD solovayPf x (solovayParam κ hG)) :
    (levyContext κ hG).IsGroundRealDefinable x := by
  have hall : ∀ y : (levyContext κ hG).Model,
      IsAllowed solovayPf y (solovayParam κ hG) → IsLocalized hG y :=
    isAllowed_localized hG solovayPf (solovayParam κ hG) hω
      (solovayPf_localized hAC hU hc hω hκ hG)
  obtain ⟨n, φ, v, hv, hxb⟩ :=
    isLocalized_isOD_parameters_of_allowed hAC hU hc hω hκ hG solovayPf (solovayParam κ hG)
      hall hx
  exact ForcingContext.groundRealDefinable_of_definable_from_definables v
    (fun i ↦ groundRealDefinable_of_isLocalized hAC hU hc hω hG (hv i)) φ hxb

/-- `Sol` is nonempty. -/
instance solovayHOD_nonempty : Nonempty (SolovayHOD κ hG) := hod_nonempty _ _

/-! ### The paper's claims about `Sol` -/

include hAC hU hc hω hκ in
/-- `Sol` is a model of `ZF` (`lem:Solovay-ZF`). -/
theorem solovay_models_zf : (SolovayHOD κ hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  hod_models_zf solovayPf (solovayParam κ hG) (solovayPf_allowed_param hAC hU hc hω hκ hG)

include hAC hU hc hω hκ in
/-- Dependent choice holds in `Sol` (`lem:Solovay-regularity`, clause `DC`). -/
theorem solovay_dependentChoice :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    InternalDependentChoice (SolovayHOD κ hG) := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact hod_internalDependentChoice_of_ground hAC hU hc hω hκ hG solovayPf
    (solovayPf_localized hAC hU hc hω hκ hG) (solovayPf_check hAC hU hc hω hκ hG)
    (solovayPf_real hG)

include hAC hU hc hω hκ in
/-- The ground set `a`, read as an element of `Sol`. -/
noncomputable def solovayCheck (a : V) : SolovayHOD κ hG :=
  haveI := solovay_models_zf hAC hU hc hω hκ hG
  hodCheck hG solovayPf (solovayPf_check hAC hU hc hω hκ hG) (solovayPf_real hG) a

theorem solovayCheck_val (a : V) :
    (solovayCheck hAC hU hc hω hκ hG a).val = (levyContext κ hG).check a := rfl

include hAC hU hc hω hκ in
/-- `κ` is the first uncountable ordinal of `Sol` (`lem:Solovay-regularity`, clause
`κ = ω₁^{Sol}`). -/
theorem solovay_hartogsNumber_omega :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    hartogsNumber (ω : SolovayHOD κ hG) = solovayCheck hAC hU hc hω hκ hG κ := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact hod_hartogsNumber_omega_eq_check_kappa hAC hU hc hω hκ hG solovayPf
    (solovayPf_check hAC hU hc hω hκ hG) (solovayPf_real hG)

include hAC hU hc hω hκ in
/-- Choice fails in `Sol` (`lem:Solovay-choice-failure`). -/
theorem solovay_not_internalChoice :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    ¬ InternalChoice (SolovayHOD κ hG) := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact hod_not_internalChoice hAC hU hc hω hκ hG solovayPf
    (solovayPf_check hAC hU hc hω hκ hG) (solovayPf_real hG)
    (solovayPf_groundRealDefinable hAC hU hc hω hκ hG)

include hAC hU hc hω hκ in
/-- Every set of reals of `Sol` is Lebesgue measurable (`lem:Solovay-regularity`, clause LM). -/
theorem solovay_lebesgueMeasurable :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    ∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → IsLebesgueMeasurable X := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact fun X hX ↦ hod_lebesgueMeasurable hAC hU hc hω hκ hG solovayPf
    (solovayPf_check hAC hU hc hω hκ hG) (solovayPf_allowed_real hG)
    (solovayPf_groundRealDefinable hAC hU hc hω hκ hG) hX

include hAC hU hc hω hκ in
/-- Every set of reals of `Sol` has the Baire property (`lem:Solovay-regularity`, clause BP). -/
theorem solovay_baireProperty :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    ∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → BaireProperty X := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact fun X hX ↦ hod_baireProperty hAC hU hc hω hκ hG solovayPf
    (solovayPf_check hAC hU hc hω hκ hG) (solovayPf_allowed_real hG)
    (solovayPf_groundRealDefinable hAC hU hc hω hκ hG) hX

include hAC hU hc hω hκ in
/-- Every set of reals of `Sol` has the perfect set property, over an arbitrary ground model
(`lem:Solovay-regularity`, clause PSP). -/
theorem solovay_perfectSetProperty :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    ∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → PerfectSetProperty X := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact fun X hX ↦ hod_perfectSetProperty hAC hU hc hω hκ hG solovayPf
    (solovayPf_check hAC hU hc hω hκ hG) (solovayPf_allowed_real hG)
    (solovayPf_groundRealDefinable hAC hU hc hω hκ hG) hX

include hAC hU hc hω hκ in
/-- The trace of the filter generated by `U` on `Sol`. -/
noncomputable def solovayUltrafilter : SolovayHOD κ hG :=
  haveI := solovay_models_zf hAC hU hc hω hκ hG
  solovayTrace hG solovayPf (solovayPf_check hAC hU hc hω hκ hG) (solovayPf_real hG) U

include hAC hU hc hω hκ in
/-- `lem:Solovay-measure`: the trace of the filter generated by `U` is a nonprincipal
`κ̌`-complete ultrafilter on `κ̌` inside `Sol`. -/
theorem solovay_ultrafilter :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    IsNonprincipalSetUltrafilter (solovayCheck hAC hU hc hω hκ hG κ)
        (solovayUltrafilter hAC hU hc hω hκ hG) ∧
      IsOrdinalComplete (solovayCheck hAC hU hc hω hκ hG κ)
        (solovayUltrafilter hAC hU hc hω hκ hG) := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact hod_solovayTrace_nonprincipalSetUltrafilter hG solovayPf
    (solovayPf_check hAC hU hc hω hκ hG) (solovayPf_real hG) U hAC hU hc hω hκ
    (solovayPf_groundRealDefinable hAC hU hc hω hκ hG)

end

end ZFVP
