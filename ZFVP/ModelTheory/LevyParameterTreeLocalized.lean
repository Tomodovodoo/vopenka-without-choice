import ZFVP.ModelTheory.LevyInternalLocalization
import ZFVP.ModelTheory.LevyStageDefinable

/-! Ordinal definability over the Solovay parameter class in the Levy extension.

The class parameters here are the ones the Solovay model allows: ground sets, reals of the
extension and ordinals. Together with the ordinals and the two-variable membership formula codes
they make up the allowed parameters of `IsAllowed`, and each of them lies in a bounded stage
`V[G_ξ]`, `ξ < κ`.

Localization is a definable class of the extension (`isLocalized_iff_internal`), so the rank
induction of `isLocalized_parameterTree` runs over the closure set of a parameter tree with no
restriction on its depth. A parameter tree is therefore localized, hence definable from ground
sets, reals and ordinals, and so is every set that is ordinal definable through such a tree. The
hypothesis of `LevyODParameterTree`, that every parameter tree has externally finite depth, is not
needed.

The set defined over `V_α` by a code `φ` with a parameter `P` is read here from two parameters
only: `P` and the pair `⟨α, φ⟩`. Both `α` and `φ` are checks, so their pair is a check as well,
and one substitution of the definition of `P` gives the conclusion.

The module does not import `LevyODParameterTree`: that module and `LevyInternalLocalization` both
declare `isLocalized_parameterTree`, so they cannot be imported together. The one lemma about
transitive closures needed from it is proved again below. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Reading the decoded set from two parameters -/

/-- `b ∈ decode α φ P`, with the ordinal and the formula code packed into the single parameter
`q = ⟨α, φ⟩`. -/
def odMemPairFormula : SetTheorySemisentence 3 :=
  f“b P q. ∃ α φ, q = !kpair.dfn α φ ∧ b ∈ !decodeFormula α φ P”

theorem odMemPairFormula_evalb (b P α φ : V) :
    odMemPairFormula.Evalb ![b, P, (⟨α, φ⟩ₖ : V)] ↔ b ∈ decode α φ P := by
  simp only [odMemPairFormula, Semiformula.Evalb]
  simp

/-- The transitive closure of a singleton sits inside the set together with its own transitive
closure. -/
theorem singleton_transitiveClosure_subset_insert (x : V) :
    transitiveClosure ({x} : V) ⊆ insert x (transitiveClosure x) := by
  refine transitiveClosure_minimal _ _ ?_ ⟨fun u hu z hz ↦ ?_⟩
  · rw [singleton_subset_iff_mem]
    exact mem_insert.mpr (Or.inl rfl)
  · rcases mem_insert.mp hu with rfl | hu
    · exact mem_insert.mpr (Or.inr (subset_transitiveClosure u z hz))
    · exact mem_insert.mpr (Or.inr ((transitiveClosure_transitive x).mem_trans hz hu))

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  (Pf : SetTheorySemisentence 2) (p : (levyContext κ hG).Model)

include hAC hU hc hω hκ in
/-- If every member of the parameter class is a ground set, a real or an ordinal, then every
allowed parameter lies in a bounded stage. -/
theorem isAllowed_localized_of_solovayParameter
    (hPf_class : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] →
      (levyContext κ hG).IsSolovayParameter y)
    (y : (levyContext κ hG).Model) (hy : IsAllowed Pf y p) : IsLocalized hG y :=
  isAllowed_localized hG Pf p hω
    (fun z hz ↦ isLocalized_parameter hAC hU hc hω hκ hG (hPf_class z hz)) y hy

include hAC hU hc hω hκ in
/-- A parameter tree over the Solovay parameter class lies in a bounded stage `V[G_ξ]`, `ξ < κ`.
No bound on the depth of the tree is assumed. -/
theorem isLocalized_parameterTree_of_solovayParameter
    (hPf_class : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] →
      (levyContext κ hG).IsSolovayParameter y)
    {P : (levyContext κ hG).Model} (h : IsParameterTree Pf P p) : IsLocalized hG P :=
  isLocalized_parameterTree hAC hU hc hω hκ hG Pf p
    (isAllowed_localized_of_solovayParameter hAC hU hc hω hκ hG Pf p hPf_class) h

include hAC hU hc hω hκ in
/-- A parameter tree over the Solovay parameter class is definable in the extension from ground
sets, reals and ordinals. -/
theorem groundRealDefinable_parameterTree
    (hPf_class : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] →
      (levyContext κ hG).IsSolovayParameter y)
    {P : (levyContext κ hG).Model} (h : IsParameterTree Pf P p) :
    (levyContext κ hG).IsGroundRealDefinable P :=
  groundRealDefinable_of_isLocalized hAC hU hc hω hG
    (isLocalized_parameterTree_of_solovayParameter hAC hU hc hω hκ hG Pf p hPf_class h)

include hAC hU hc hω hκ in
/-- A set of the Levy extension that is ordinal definable over the Solovay parameter class is
definable from ground sets, reals and ordinals. This is `groundRealDefinable_of_isOD` of
`LevyODParameterTree` without its hypothesis that every parameter tree has externally finite
depth. -/
theorem groundRealDefinable_of_isOD'
    (hPf_class : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] →
      (levyContext κ hG).IsSolovayParameter y)
    {x : (levyContext κ hG).Model} (hx : IsOD Pf x p) :
    (levyContext κ hG).IsGroundRealDefinable x := by
  obtain ⟨α, φ₀, P, hα, hcode, hP, -, rfl⟩ := hx
  have hαord : IsOrdinal α := hα
  obtain ⟨α₀, -, rfl⟩ := (levyContext κ hG).ordinal_eq_check α
  obtain ⟨φ₁, rfl⟩ := (levyContext κ hG).check_membershipFormulaCode hcode
  refine ForcingContext.groundRealDefinable_of_definable_from₂
    (groundRealDefinable_parameterTree hAC hU hc hω hκ hG Pf p hPf_class hP)
    (Or.inl ⟨(⟨α₀, φ₁⟩ₖ : V), ((levyContext κ hG).checkEmbedding.map_kpair α₀ φ₁).symm⟩)
    odMemPairFormula (fun b ↦ ?_)
  exact (odMemPairFormula_evalb b P ((levyContext κ hG).check α₀)
    ((levyContext κ hG).check φ₁)).symm

include hAC hU hc hω hκ in
/-- A hereditarily ordinal definable set of the Levy extension, over the Solovay parameter class,
is hereditarily definable from ground sets, reals and ordinals. This is
`hereditarilyGroundRealDefinable_of_isHOD` of `LevyODParameterTree` without its hypothesis that
every parameter tree has externally finite depth. -/
theorem hereditarilyGroundRealDefinable_of_isHOD'
    (hPf_class : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] →
      (levyContext κ hG).IsSolovayParameter y)
    {x : (levyContext κ hG).Model} (hx : IsHOD Pf x p) :
    (levyContext κ hG).IsHereditarilyGroundRealDefinable x := by
  intro y hy
  rcases mem_insert.mp (singleton_transitiveClosure_subset_insert x y hy) with rfl | hy'
  · exact groundRealDefinable_of_isOD' hAC hU hc hω hκ hG Pf p hPf_class hx.1
  · exact groundRealDefinable_of_isOD' hAC hU hc hω hκ hG Pf p hPf_class (hx.2 y hy')

end

end ZFVP
