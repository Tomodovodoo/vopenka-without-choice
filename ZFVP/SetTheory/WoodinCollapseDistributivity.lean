import ZFVP.SetTheory.WoodinCollapse
import ZFVP.SetTheory.ForcingClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCollapse_closedBelow {κ : V} (hκ : IsRegularCardinal κ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) (δ : V) :
    IsForcingClosedBelow (woodinCollapse κ δ) (woodinCollapseOrder κ δ) κ := by
  intro α hα f hf
  exact woodinCollapse_closed hκ hα (hDC α hα) hf.1 hf.2

theorem woodinCollapse_denseIntersection {κ δ γ D : V} (hκ : IsRegularCardinal κ)
    (hγ : γ ∈ κ) (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α)
    (hD : ∀ i ∈ γ, ForcingDense (woodinCollapse κ δ) (woodinCollapseOrder κ δ) (D ‘ i) ∧
      IsForcingDownwardClosed (woodinCollapse κ δ) (woodinCollapseOrder κ δ) (D ‘ i)) :
    ForcingDense (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      {q ∈ woodinCollapse κ δ ; ∀ i ∈ γ, q ∈ D ‘ i} := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  apply forcingClosed_denseIntersection (woodinCollapse_poset κ δ).1 (hDC γ hγ) ?_ hD
  intro α hαord hα
  let := hαord
  have hακ : α ∈ κ := ordinal_mem_of_subset_mem hα hγ
  exact woodinCollapse_closedBelow hκ hDC δ α hακ

end ZFVP
