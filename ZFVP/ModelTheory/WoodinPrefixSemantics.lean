import ZFVP.SetTheory.WoodinPrefixCutoff
import ZFVP.ModelTheory.ForcingSemanticConsequence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinLocalRestoration.dependentChoice {κ δ : V}
    (hδ : IsWoodinLocalRestoration κ δ) (hκ : IsRegularCardinal κ) {G : Set V}
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    ∀ η ∈ (woodinCollapseContext hκ δ G hG).check δ, InternalDependentChoiceAt η := by
  let A := woodinCollapseContext hκ δ G hG
  let c : ForcingName A.P := ⟨checkName ∅ δ, checkName_isName A.top.1 δ⟩
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have ht := (A.formula_truth dependentChoiceBelowFormula ![c]).mpr
    ⟨p, hp, hδ.2 p (A.generic.1.1 p hp)⟩
  exact (Defined.eval_iff _).mp ht

theorem woodinLocalRestoration_iff_all_generics [Countable V] {κ δ : V}
    (hκ : IsRegularCardinal κ) [IsOrdinal δ] :
    IsWoodinLocalRestoration κ δ ↔
      ∀ (G : Set V) (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G),
        ∀ η ∈ (woodinCollapseContext hκ δ G hG).check δ, InternalDependentChoiceAt η := by
  constructor
  · intro h G hG
    exact h.dependentChoice hκ hG
  · intro h
    refine ⟨inferInstance, ?_⟩
    intro p hp
    let ht := woodinCollapse_top (hκ.2.1 ∅ (by simp)) δ
    let c : ForcingName (woodinCollapse κ δ) := ⟨checkName ∅ δ, checkName_isName ht.1 δ⟩
    apply forcingFormula_of_all_generics (woodinCollapse_poset κ δ).1 ht hp dependentChoiceBelowFormula ![c]
    intro G hG _hpG
    exact (Defined.eval_iff _).mpr (h G hG)

/-- For countable grounds, the internal prefix predicate is equivalent to
restoration in every first-stage generic extension. Its definition itself
makes sense in arbitrary ZF models and does not postulate external generics. -/
theorem woodinPrefixCutoff_iff_all_generics [Countable V] {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) :
    IsWoodinPrefixCutoff P R one κ δ ↔ κ ∈ δ ∧ IsChoicelessInaccessible δ ∧
      ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
        IsWoodinLocalRestoration ((ForcingContext.mk P R one G hR htop hG).check κ)
          ((ForcingContext.mk P R one G hR htop hG).check δ) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, fun G hG ↦ h.localRestoration ⟨P, R, one, G, hR, htop, hG⟩⟩
  · rintro ⟨hκδ, hδ, h⟩
    refine ⟨hκδ, hδ, ?_⟩
    intro p hp
    let cκ : ForcingName P := ⟨checkName one κ, checkName_isName htop.1 κ⟩
    let cδ : ForcingName P := ⟨checkName one δ, checkName_isName htop.1 δ⟩
    apply forcingFormula_of_all_generics hR htop hp woodinLocalRestorationFormula ![cκ, cδ]
    intro G hG _hpG
    exact (Defined.eval_iff _).mpr (h G hG)

end ZFVP
