import ZFVP.ModelTheory.WoodinCollapseForcesRestoration
import ZFVP.SetTheory.WoodinSupercompactInaccessible

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSupercompact_collapse_forces_restoration {κ δ p : V}
    (hκ : IsRegularCardinal κ) (hδ : IsWoodinSupercompact δ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) (hp : p ∈ woodinCollapse κ δ) :
    p ∈ forcingFormula (woodinCollapse κ δ) (woodinCollapseOrder κ δ) dependentChoiceBelowFormula
      (standardTuple ![checkName ∅ δ]) :=
  woodinCollapse_forces_restoration hκ hδ.regular hδ.highCritical hκδ hDC hp

theorem woodinSupercompact_collapse_dependentChoice {κ δ : V}
    (hκ : IsRegularCardinal κ) (hδ : IsWoodinSupercompact δ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) {G : Set V}
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    ∀ η ∈ (woodinCollapseContext hκ δ G hG).check δ, InternalDependentChoiceAt η :=
  WoodinCollapseModel.dependentChoice_below_restored hκ hδ.regular hδ.highCritical hκδ hDC hG

end ZFVP
