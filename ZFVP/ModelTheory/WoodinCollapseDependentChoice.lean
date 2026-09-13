import ZFVP.ModelTheory.ForcingDependentChoiceTransfer
import ZFVP.ModelTheory.WoodinCollapsePreservation

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinCollapseModel

variable {κ δ : V} (hκ : IsRegularCardinal κ) {G : Set V}
  (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)

theorem dependentChoiceAt_check {γ : V} (hγ : γ ∈ κ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) :
    InternalDependentChoiceAt ((woodinCollapseContext hκ δ G hG).check γ) := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  apply ForcingContext.dependentChoiceAt_of_closed _ (hDC γ hγ)
  intro α hαord hαγ
  let := hαord
  exact woodinCollapse_closedBelow hκ hDC δ α (ordinal_mem_of_subset_mem hαγ hγ)

theorem dependentChoice_below (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) :
    ∀ γ ∈ (woodinCollapseContext hκ δ G hG).check κ, InternalDependentChoiceAt γ := by
  intro γ hγ
  obtain ⟨α, hα, rfl⟩ := ((woodinCollapseContext hκ δ G hG).mem_check_iff κ γ).mp hγ
  exact dependentChoiceAt_check hκ hG hα hDC

end WoodinCollapseModel
end ZFVP
