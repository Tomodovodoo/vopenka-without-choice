import ZFVP.ModelTheory.WoodinSuccessorIterand
import ZFVP.ModelTheory.TwoStepQuotient

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem forcedEmptyName_value (A : ForcingContext V) :
    A.ofName ⟨forcedEmptyName A.P A.R, forcedEmptyName_isName A.P A.R⟩ = ∅ := by
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have he := (A.formula_truth isEmpty ![⟨forcedEmptyName A.P A.R, forcedEmptyName_isName A.P A.R⟩]).mpr
    ⟨p, hp, forcedEmptyName_forces A.order A.top (A.generic.1.1 p hp)⟩
  simpa using he

theorem dependentChoice_of_restorationCutoff (A : ForcingContext V) {κ δ : V}
    (hδ : IsWoodinRestorationCutoff κ δ) (hP : A.P = woodinCollapse κ δ)
    (hR : A.R = woodinCollapseOrder κ δ) (ho : A.one = ∅) :
    ∀ η ∈ A.check δ, InternalDependentChoiceAt η := by
  let c : ForcingName A.P := ⟨checkName A.one δ, checkName_isName A.top.1 δ⟩
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have hpP : p ∈ woodinCollapse κ δ := hP ▸ A.generic.1.1 p hp
  have hf : p ∈ forcingFormula A.P A.R dependentChoiceBelowFormula (standardTuple ![c.val]) := by
    change p ∈ forcingFormula A.P A.R dependentChoiceBelowFormula (standardTuple ![checkName A.one δ])
    rw [hP, hR, ho]
    exact hδ.2.2 p hpP
  have ht := (A.formula_truth dependentChoiceBelowFormula ![c]).mpr ⟨p, hp, hf⟩
  exact (Defined.eval_iff _).mp ht

end ForcingContext

namespace WoodinSuccessorModel
variable (A : ForcingContext V) (κ : ForcingName A.P)
  (hκ : ∀ p ∈ A.P, p ∈ forcingFormula A.P A.R regularCardinalFormula (standardTuple ![κ.val]))
  {H : Set A.Model}
  (hH : IsExternalForcingGeneric (A.ofName (A.successorPosetName κ))
    (A.ofName (A.reverseOrderName (A.successorPosetName κ))) H)

noncomputable def context : ForcingContext A.Model :=
  TwoStepModel.iterandContext A (woodinSuccessor_iterand A.order A.top κ hκ) hH

theorem context_poset : (context A κ hκ hH).P =
    woodinCollapse (A.ofName κ) (woodinRestorationCutoff (A.ofName κ)) := A.successorPosetName_value κ

theorem context_order : (context A κ hκ hH).R =
    woodinCollapseOrder (A.ofName κ) (woodinRestorationCutoff (A.ofName κ)) := by
  change A.ofName (A.reverseOrderName (A.successorPosetName κ)) = _
  rw [A.reverseOrderName_value, A.successorPosetName_value]
  rfl

theorem context_top : (context A κ hκ hH).one = ∅ := A.forcedEmptyName_value

include hκ in
theorem regular : IsRegularCardinal (A.ofName κ) := by
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have ht := (A.formula_truth regularCardinalFormula ![κ]).mpr
    ⟨p, hp, hκ p (A.generic.1.1 p hp)⟩
  exact (Defined.eval_iff _).mp ht

theorem restores {δ : A.Model} (hδ : IsWoodinRestorationCutoff (A.ofName κ) δ) :
    ∀ η ∈ (context A κ hκ hH).check (woodinRestorationCutoff (A.ofName κ)),
      InternalDependentChoiceAt η :=
  (context A κ hκ hH).dependentChoice_of_restorationCutoff (woodinRestorationCutoff_spec hδ).2.1
    (context_poset A κ hκ hH) (context_order A κ hκ hH) (context_top A κ hκ hH)

theorem restores_of_supercompact {δ : A.Model} (hδ : IsWoodinSupercompact δ)
    (hκδ : A.ofName κ ∈ δ) (hDC : ∀ α ∈ A.ofName κ, InternalDependentChoiceAt α) :
    ∀ η ∈ (context A κ hκ hH).check (woodinRestorationCutoff (A.ofName κ)),
      InternalDependentChoiceAt η :=
  restores A κ hκ hH (hδ.restorationCutoff (regular A κ hκ) hκδ hDC)

end WoodinSuccessorModel
end ZFVP
