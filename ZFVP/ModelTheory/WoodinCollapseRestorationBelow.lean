import ZFVP.ModelTheory.WoodinCollapseRestoration
import ZFVP.SetTheory.WellOrderedSurjection
import ZFVP.SetTheory.DependentChoiceCardinal

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinCollapseModel

theorem check_ordinal_cardLE {κ δ η : V} (hκ : IsRegularCardinal κ) (hδ : IsRegularCardinal δ)
    (hη : η ∈ δ) {G : Set V}
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    (woodinCollapseContext hκ δ G hG).check η ≤# (woodinCollapseContext hκ δ G hG).check κ := by
  let S := woodinCollapseContext hκ δ G hG
  let := hκ.1.1
  let := hδ.1.1
  let := IsOrdinal.of_mem hη
  let : IsOrdinal (1 : V) := IsOrdinal.of_mem (show (1 : V) ∈ (ω : V) by simp)
  obtain ⟨hf, hr⟩ := rowFunction_surjective_of_regular hκ hG hδ hη
  have hcard := cardLE_of_surjective_function (ordinal_wellOrderable (S.check κ)) hf hr
  have hsub : η ⊆ hierarchy (ordinalAdd (1 : V) η) := subset_trans (ordinal_subset_hierarchy η)
    (hierarchy_mono (ordinal_subset_add_right (1 : V) η))
  exact (cardLE_of_subset ((S.checkEmbedding.subset_iff _ _).mpr hsub)).trans hcard

theorem dependentChoice_below_restored {κ δ : V} (hκ : IsRegularCardinal κ)
    (hδreg : IsRegularCardinal δ) (hδ : HasHighCriticalWoodinWitnesses δ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) {G : Set V}
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    ∀ η ∈ (woodinCollapseContext hκ δ G hG).check δ, InternalDependentChoiceAt η := by
  let S := woodinCollapseContext hκ δ G hG
  let := hκ.1.1
  let := hδreg.1.1
  intro η hη
  obtain ⟨α, hα, rfl⟩ := (S.mem_check_iff δ η).mp hη
  let := IsOrdinal.of_mem hα
  exact (dependentChoiceAt_restored hκ hδ hκδ hDC hG).of_cardLE (check_ordinal_cardLE hκ hδreg hα hG)

end WoodinCollapseModel
end ZFVP
