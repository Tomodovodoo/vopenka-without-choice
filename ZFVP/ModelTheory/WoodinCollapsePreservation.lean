import ZFVP.ModelTheory.ForcingClosedCardinals
import ZFVP.ModelTheory.WoodinCollapseModel
import ZFVP.SetTheory.WoodinCollapseDistributivity

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinCollapseModel

variable {κ δ : V} (hκ : IsRegularCardinal κ) {G : Set V}
  (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)
  (hDC : ∀ γ ∈ κ, InternalDependentChoiceAt γ)

include hDC

theorem function_eq_check {γ X : V} (hγ : γ ∈ κ)
    {z : (woodinCollapseContext hκ δ G hG).Model}
    (hz : z ∈ (woodinCollapseContext hκ δ G hG).check X ^
      (woodinCollapseContext hκ δ G hG).check γ) :
    ∃ f ∈ X ^ γ, (woodinCollapseContext hκ δ G hG).check f = z := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  apply ForcingContext.function_eq_check_of_closed _ (hDC γ hγ) ?_ hz
  intro α hαord hαγ
  let := hαord
  exact woodinCollapse_closedBelow hκ hDC δ α (ordinal_mem_of_subset_mem hαγ hγ)

theorem check_functionSet {γ X : V} (hγ : γ ∈ κ) :
    (woodinCollapseContext hκ δ G hG).check (X ^ γ) =
      (woodinCollapseContext hκ δ G hG).check X ^
      (woodinCollapseContext hκ δ G hG).check γ := by
  let S := woodinCollapseContext hκ δ G hG
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨f, hf, rfl⟩ := (S.mem_check_iff (X ^ γ) z).mp hz
    exact (S.check_function_iff f γ X).mpr hf
  · intro hz
    obtain ⟨f, hf, he⟩ := function_eq_check hκ hG hDC hγ hz
    exact (S.mem_check_iff (X ^ γ) z).mpr ⟨f, hf, he.symm⟩

theorem check_regular : IsRegularCardinal ((woodinCollapseContext hκ δ G hG).check κ) :=
  ForcingContext.check_regular_of_closed _ hκ hDC (woodinCollapse_closedBelow hκ hDC δ)

end WoodinCollapseModel
end ZFVP
