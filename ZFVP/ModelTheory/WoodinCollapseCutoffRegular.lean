import ZFVP.ModelTheory.WoodinCollapseBoundedFunctions
import ZFVP.SetTheory.EndExtensionFinite

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinCollapseModel

theorem check_cutoff_regular {κ δ : V} (hκ : IsRegularCardinal κ)
    (hδ : IsChoicelessInaccessible δ) (hκδ : κ ∈ δ) {G : Set V}
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    IsRegularCardinal ((woodinCollapseContext hκ δ G hG).check δ) := by
  let A := woodinCollapseContext hκ δ G hG
  let := hδ.1
  have hcf : internalCofinality (A.check δ) = A.check δ := by
    rcases IsOrdinal.subset_iff.mp (internalCofinality_subset (A.check δ)) with he | hlt
    · exact he
    obtain ⟨γ, hγ, he⟩ := (A.mem_check_iff δ _).mp hlt
    let := IsOrdinal.of_mem hγ
    obtain ⟨f, hf⟩ := cofinalMap_exists (A.check δ)
    rw [he] at hf
    obtain ⟨β, hβ, hb⟩ := function_values_bounded hκ hδ hκδ hγ hG hf.1
    obtain ⟨a, ha, hβa⟩ := hf.2 (A.check β) ((A.check_mem_iff _ _).mpr hβ)
    exact False.elim (mem_irrefl (f ‘ a) (hβa _ (hb a ha)))
  refine ⟨hcf ▸ internalCofinality_initial (A.check δ), ?_, hcf⟩
  have hh := (A.checkEmbedding.subset_iff (ω : V) δ).mpr hδ.regular.2.1
  change A.check ω ⊆ A.check δ at hh
  rwa [show A.check ω = (ω : A.Model) from A.checkEmbedding.map_omega] at hh

end WoodinCollapseModel
end ZFVP
