import ZFVP.ModelTheory.WoodinCollapseRestorationForcing
import ZFVP.ModelTheory.WoodinPrefixSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinPrefix_iterand_of_ordinal {P R one κ δ : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ])) :
    IsForcingIterand P R (woodinPrefixPosetName P R one κ δ) (woodinPrefixOrderName P R one κ δ)
      (forcedEmptyName P R) :=
  woodinCollapse_iterand_of_ordinal hR htop
    ⟨checkName one κ, checkName_isName htop.1 κ⟩
    ⟨checkName one δ, checkName_isName htop.1 δ⟩ hκ
    (fun _p hp ↦ forces_checked_ordinal hR htop inferInstance hp)

/-- Woodin's ground cutoff condition uses the whole successor forcing.
The collapse iterand is constructed from regularity and ordinality before
either side of this equivalence is assumed. -/
theorem woodinPrefixCutoff_iff_successor_forces {P R one κ δ : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ])) :
    IsWoodinPrefixCutoff P R one κ δ ↔ κ ∈ δ ∧ IsChoicelessInaccessible δ ∧
      ∀ p ∈ twoStepConditions P R (woodinPrefixPosetName P R one κ δ) (forcedEmptyName P R),
        p ∈ forcingFormula
          (twoStepConditions P R (woodinPrefixPosetName P R one κ δ) (forcedEmptyName P R))
          (twoStepOrder P R (woodinPrefixPosetName P R one κ δ)
            (woodinPrefixOrderName P R one κ δ) (forcedEmptyName P R)) dependentChoiceBelowFormula
          (standardTuple ![checkName ⟨one, forcedEmptyName P R⟩ₖ δ]) := by
  let cκ : ForcingName P := ⟨checkName one κ, checkName_isName htop.1 κ⟩
  let cδ : ForcingName P := ⟨checkName one δ, checkName_isName htop.1 δ⟩
  have hiter := woodinPrefix_iterand_of_ordinal (δ := δ) hR htop hκ
  have he := twoStep_checked_forcing (a := δ) hR htop hiter dependentChoiceBelowFormula
  have hl (p : V) (hp : p ∈ P) := woodinCollapse_restoration_forcing_iff hR htop hp cκ cδ
    (forces_checked_ordinal hR htop (inferInstance : IsOrdinal δ) hp)
  constructor
  · intro h
    exact ⟨h.1, h.2.1, he.mp (fun p hp ↦ (hl p hp).mp (h.2.2 p hp))⟩
  · rintro ⟨hκδ, hδ, h⟩
    exact ⟨hκδ, hδ, fun p hp ↦ (hl p hp).mpr (he.mpr h p hp)⟩

end ZFVP
