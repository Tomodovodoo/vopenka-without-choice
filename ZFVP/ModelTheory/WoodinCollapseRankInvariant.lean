import ZFVP.ModelTheory.WoodinCollapseRankSuccessor
import ZFVP.SetTheory.RankEnumerations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.rankEnumerations_of_collapse (B : ForcingContext V) {κ δ θ : V}
    (hκ : IsRegularCardinal κ) (hδ : IsRegularCardinal δ) (hκδ : κ ∈ δ) (hθ : θ ∈ δ)
    (hDC : ∀ γ ∈ κ, InternalDependentChoiceAt γ) (henum : HasShortRankEnumerations θ κ)
    (hP : B.P = woodinCollapse κ δ) (hR : B.R = woodinCollapseOrder κ δ) (ho : B.one = ∅) :
    HasShortRankEnumerations (B.check (succ θ)) (B.check δ) := by
  have hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) B.G := by
    rw [← hP, ← hR]
    exact B.generic
  have he : B = woodinCollapseContext hκ δ B.G hG := by
    cases B
    cases hP
    cases hR
    cases ho
    rfl
  exact he ▸ WoodinCollapseModel.hierarchy_enumeration_successor hκ hG hδ hκδ hθ hDC henum

end ZFVP
