import ZFVP.SetTheory.PiOneInitialOrdinal
import ZFVP.SetTheory.ChoicelessInaccessibleRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOneRegularCardinalFormula : SetTheorySemisentence 1 :=
  “κ. !piOneInitialOrdinalFormula κ ∧
    (∀ w, !boundedOmegaFormula w → !isSubsetOf w κ) ∧
    ∀ β ∈ κ, ∀ f, ¬!boundedCofinalMapFormula κ β f”

theorem piOneRegularCardinalFormula_piOne : IsPiFormula 1 piOneRegularCardinalFormula :=
  .and (piOneInitialOrdinalFormula_piOne.subst _)
    (.and (.all (.bounded (.or (boundedOmegaFormula_bounded.subst _).neg
      (isSubsetOf_bounded.subst _))))
      (.boundedAll (.bvar 0) (.all (.bounded (boundedCofinalMapFormula_bounded.subst _).neg))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem regularCardinal_iff_no_short_cofinalMap (κ : V) :
    IsRegularCardinal κ ↔ IsInitialOrdinal κ ∧ (ω : V) ⊆ κ ∧
      ∀ β ∈ κ, ∀ f, ¬IsCofinalMap κ β f := by
  constructor
  · intro hκ
    let := hκ.1.1
    refine ⟨hκ.1, hκ.2.1, ?_⟩
    intro β hβ f hf
    exact no_cofinalMap_below_cofinality (hκ.2.2.symm ▸ hβ) ⟨f, hf⟩
  · rintro ⟨hκ, hω, hn⟩
    let := hκ.1
    refine ⟨hκ, hω, ?_⟩
    rcases IsOrdinal.subset_iff.mp (internalCofinality_subset κ) with he | hlt
    · exact he
    · obtain ⟨f, hf⟩ := cofinalMap_exists κ
      exact False.elim (hn _ hlt f hf)

instance piOneRegularCardinalFormula_defined :
    ℒₛₑₜ-predicate[V] IsRegularCardinal via piOneRegularCardinalFormula :=
  ⟨fun v ↦ by
    rw [regularCardinal_iff_no_short_cofinalMap]
    simp [piOneRegularCardinalFormula]⟩

theorem IsRankCriterionHeight.choicelessInaccessible {κ : V} (hκ : IsRankCriterionHeight κ) :
    IsChoicelessInaccessible κ := by
  let := hκ.1
  exact ⟨hκ.1, hκ.2.1, fun α hα g ↦ hκ.2.2.2 _ (hierarchy_mem hα) g⟩

theorem rankCriterionHeight_iff_choicelessInaccessible (κ : V) :
    IsRankCriterionHeight κ ↔ IsChoicelessInaccessible κ :=
  ⟨IsRankCriterionHeight.choicelessInaccessible, IsChoicelessInaccessible.rankCriterion⟩

/-- The existing Pi1 rank criterion defines the source's choiceless inaccessibility. -/
theorem eval_rankCriterionFormula_iff_choicelessInaccessible (v : Fin 1 → V) :
    rankCriterionFormula.Evalb v ↔ IsChoicelessInaccessible (v 0) :=
  (Defined.eval_iff v).trans (rankCriterionHeight_iff_choicelessInaccessible (v 0))

end ZFVP
