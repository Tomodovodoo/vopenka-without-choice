import ZFVP.SetTheory.BoundedStarDependentChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedStarDCBelowFormula : SetTheorySemisentence 3 :=
  “κ D H. ∀ η ∈ κ, !boundedStarDCFormula η D H”

theorem boundedStarDCBelowFormula_bounded : IsBoundedSetFormula boundedStarDCBelowFormula :=
  .all (.bvar 0) (boundedStarDCFormula_bounded.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_boundedStarDCBelowFormula (κ D H : V) :
    boundedStarDCBelowFormula.Evalb ![κ, D, H] ↔
      ∀ η ∈ κ, boundedStarDCFormula.Evalb ![η, D, H] := by
  simp [boundedStarDCBelowFormula, Semiformula.eval_substs]

theorem boundedStarDCBelow_iff {δ γ κ : V} (hδ : IsWoodinSupercompact δ)
    (hγ : IsSigmaOneStarCorrect γ) (hκ : κ ∈ γ) :
    boundedStarDCBelowFormula.Evalb ![κ, hierarchy (succ κ), hierarchy γ] ↔
      ∀ η ∈ κ, InternalDependentChoiceAt η := by
  rw [eval_boundedStarDCBelowFormula]
  apply forall_congr'
  intro η
  apply forall_congr'
  intro hη
  exact boundedStarDC_iff_at hδ hγ (hγ.1.successor_closed κ hκ) (mem_succ_iff.mpr (Or.inr hη))

end ZFVP
