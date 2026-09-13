import ZFVP.ModelTheory.WoodinCollapseModel
import ZFVP.SetTheory.OrdinalLeftOne
import ZFVP.SetTheory.WellOrderedSurjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace WoodinCollapseModel
variable {κ δ : V} (hκ : IsRegularCardinal κ) {G : Set V}
  (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)

/-- Every old bounded rank has cardinal at most the lower collapse index. -/
theorem check_hierarchy_cardLE (hδ : IsRegularCardinal δ) {α : V} (hα : α ∈ δ) :
    (woodinCollapseContext hκ δ G hG).check (hierarchy α) ≤#
      (woodinCollapseContext hκ δ G hG).check κ := by
  let := hκ.1.1
  let := hδ.1.1
  let := IsOrdinal.of_mem hα
  let : IsOrdinal (1 : V) := IsOrdinal.of_mem (show (1 : V) ∈ (ω : V) by simp)
  let A := woodinCollapseContext hκ δ G hG
  have hs : A.check (hierarchy α) ⊆ A.check (hierarchy (ordinalAdd (1 : V) α)) :=
    (A.checkEmbedding.subset_iff _ _).mpr (hierarchy_mono (ordinal_subset_add_right (1 : V) α))
  obtain ⟨hf, hr⟩ := rowFunction_surjective_of_regular hκ hG hδ hα
  exact (cardLE_of_subset hs).trans (cardLE_of_surjective_function (ordinal_wellOrderable _) hf hr)

/-- The old bounded rank has an enumeration shorter than the upper endpoint. -/
theorem check_hierarchy_enumeration_below_upper (hδ : IsRegularCardinal δ) (hκδ : κ ∈ δ)
    {α : V} (hα : α ∈ δ) :
    let A := woodinCollapseContext hκ δ G hG
    ∃ γ ∈ A.check δ, ∃ e ∈ A.check (hierarchy α) ^ γ, range e = A.check (hierarchy α) := by
  let := hκ.1.1
  let := hδ.1.1
  let := IsOrdinal.of_mem hα
  let A := woodinCollapseContext hκ δ G hG
  change ∃ γ ∈ A.check δ, ∃ e ∈ A.check (hierarchy α) ^ γ, range e = A.check (hierarchy α)
  by_cases h0 : α = ∅
  · subst α
    refine ⟨∅, ?_, ∅, ?_, ?_⟩
    · have hz : (∅ : V) ∈ δ := IsOrdinal.toIsTransitive.mem_trans (hκ.2.1 ∅ (by simp)) hκδ
      simpa only [show A.check ∅ = ∅ from A.checkEmbedding.map_empty] using (A.check_mem_iff ∅ δ).mpr hz
    · simp [hierarchy_empty, show A.check ∅ = ∅ from A.checkEmbedding.map_empty]
    · simp [hierarchy_empty, show A.check ∅ = ∅ from A.checkEmbedding.map_empty]
  · have hz : (∅ : V) ∈ α := (IsOrdinal.subset_iff.mp (empty_subset α)).resolve_left (fun he ↦ h0 he.symm)
    have hne : IsNonempty (A.check (hierarchy α)) := by
      refine ⟨A.check ∅, (A.check_mem_iff _ _).mpr ?_⟩
      exact (mem_hierarchy_iff_of_ordinal α ∅).mpr ⟨∅, hz, empty_subset _⟩
    obtain ⟨e, he, hr⟩ := surjection_of_injection (check_hierarchy_cardLE hκ hG hδ hα) hne
    exact ⟨A.check κ, (A.check_mem_iff _ _).mpr hκδ, e, he, hr⟩

end WoodinCollapseModel
end ZFVP
