import ZFVP.ModelTheory.LevyConeAlgebraProperties
import ZFVP.SetTheory.LevyCollapseSmallSets

/-! The collapsing property of a cone of the Boolean completion of the Levy collapse.

Write `B` for `booleanConditions (levyCollapse κ) (levyOrder κ)` and `B↾a` for the cone of a
nonzero `a` of `B`. `ZFVP/ModelTheory/LevyConeAlgebraProperties.lean` proves two of the three
properties that pin down the Levy algebra: `B↾a` has a dense subset of size at most `κ`
(`levy_cone_dense_cardLE`) and no antichain of `B↾a` has size `κ` (`levy_cone_chainCondition`).
This file proves the third, that `B↾a` collapses every `lam < κ`, and puts the three together.

* `levy_cone_surjection_dense`: below every nonzero `b ⊆ a` of `B` and for every `gam ∈ lam ∈ κ`
  there is a row `n ∈ ω` and a condition `p` of the collapse whose regular cone is inside `b` and
  which sends `⟨n, lam⟩` to `gam`. Since `gam` ranges over all of `lam`, the generic column at
  `lam` is a surjection of `ω` onto `lam`, so `B↾a` collapses `lam` to `ω`.

* `levy_cone_three_properties`: the three properties in one statement.

The proof of the first is short. A nonzero Boolean condition `b` contains the regular cone of some
condition `q` of the collapse (`exists_coneRegular_subset`). A condition has finite domain, so it
uses only finitely many rows of the column `lam` (`columnRows_finite`) and some row `n ∈ ω` is
free (`internallyFinite_fresh_natural`). Putting the value `gam` at that row gives a condition
`p ⊇ q` (`levyCollapse_insert`, which needs `gam ∈ lam`), and cones shrink as conditions grow
(`coneRegular_mono`), so `coneRegular p ⊆ coneRegular q ⊆ b`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section Collapsing

variable {κ : V} [IsOrdinal κ] {a b lam gam : V}

/-- Below every nonzero element `b` of the cone of `a` some condition cone forces the generic
column at `lam` to send a row `n` of `ω` to `gam`. As `gam` ranges over `lam`, this says that the
cone of `a` collapses `lam` to `ω`. -/
theorem levy_cone_surjection_dense
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hb : b ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) (hba : b ⊆ a)
    (hlam : lam ∈ κ) (hgam : gam ∈ lam) :
    ∃ n ∈ (ω : V), ∃ p ∈ levyCollapse κ,
      coneRegular (levyCollapse κ) (levyOrder κ) p ⊆ b ∧ ⟨⟨n, lam⟩ₖ, gam⟩ₖ ∈ p := by
  obtain ⟨q, hq, hqb⟩ := exists_coneRegular_subset (levyCollapse_poset κ).1 hb
  obtain ⟨n, hn, hnfresh⟩ := internallyFinite_fresh_natural (columnRows_finite (β := lam) hq)
  have hfresh : ∀ δ, ⟨⟨n, lam⟩ₖ, δ⟩ₖ ∉ q := fun δ h ↦ hnfresh (mem_sep_iff.mpr ⟨hn, δ, h⟩)
  have hp : insert ⟨⟨n, lam⟩ₖ, gam⟩ₖ q ∈ levyCollapse κ :=
    levyCollapse_insert hq hn hlam hgam hfresh
  have hpq : ⟨insert ⟨⟨n, lam⟩ₖ, gam⟩ₖ q, q⟩ₖ ∈ levyOrder κ :=
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hq, fun z hz ↦ mem_insert.mpr (Or.inr hz)⟩
  refine ⟨n, hn, insert ⟨⟨n, lam⟩ₖ, gam⟩ₖ q, hp, ?_, mem_insert.mpr (Or.inl rfl)⟩
  exact subset_trans (coneRegular_mono (levyCollapse_poset κ).1 hq hp hpq) hqb

end Collapsing

section ThreeProperties

variable {κ U a : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hAC hU hc hω hκ in
/-- The three properties of the cone of a nonzero condition `a` of the Boolean completion of
`Coll(ω, <κ)`: a dense subset of size at most `κ`, no antichain of size `κ`, and the collapse of
every `lam ∈ κ`. The first two are `levy_cone_dense_cardLE` and `levy_cone_chainCondition`, the
third is `levy_cone_surjection_dense`. -/
theorem levy_cone_three_properties
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) :
    (∃ D, ForcingDense
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) a)
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) a)) D ∧ D ≤# κ) ∧
      (∀ A, IsForcingAntichain
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) a)
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) a)) A → ¬κ ≤# A) ∧
      (∀ b ∈ booleanConditions (levyCollapse κ) (levyOrder κ), b ⊆ a →
        ∀ lam ∈ κ, ∀ gam ∈ lam, ∃ n ∈ (ω : V), ∃ p ∈ levyCollapse κ,
          coneRegular (levyCollapse κ) (levyOrder κ) p ⊆ b ∧ ⟨⟨n, lam⟩ₖ, gam⟩ₖ ∈ p) :=
  ⟨levy_cone_dense_cardLE hAC hU hc hω hκ ha,
    fun _ hA ↦ levy_cone_chainCondition hAC hU hc hω hκ ha hA,
    fun _ hb hba _ hlam _ hgam ↦ levy_cone_surjection_dense ha hb hba hlam hgam⟩

end ThreeProperties

end ZFVP
