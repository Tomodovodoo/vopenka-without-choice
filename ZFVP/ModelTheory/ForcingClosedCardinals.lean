import ZFVP.ModelTheory.ForcingClosedSequences
import ZFVP.SetTheory.CofinalityDictionary
import ZFVP.SetTheory.EndExtensionFinite
import ZFVP.SetTheory.FormulaReflection

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem check_regular_of_closed (S : ForcingContext V) {κ : V} (hκ : IsRegularCardinal κ)
    (hDC : ∀ γ ∈ κ, InternalDependentChoiceAt γ)
    (hclosed : IsForcingClosedBelow S.P S.R κ) : IsRegularCardinal (S.check κ) := by
  let := hκ.1.1
  have hcf : internalCofinality (S.check κ) = S.check κ := by
    rcases IsOrdinal.subset_iff.mp (internalCofinality_subset (S.check κ)) with he | hlt
    · exact he
    obtain ⟨γ, hγ, he⟩ := (S.mem_check_iff κ _).mp hlt
    let := IsOrdinal.of_mem hγ
    obtain ⟨f, hf⟩ := cofinalMap_exists (S.check κ)
    rw [he] at hf
    obtain ⟨g, hg, rfl⟩ := S.function_eq_check_of_closed (hDC γ hγ) (by
      intro α hαord hαγ
      let := hαord
      exact hclosed α (ordinal_mem_of_subset_mem hαγ hγ)) hf.1
    let := IsFunction.of_mem hg
    obtain ⟨ξ, hξ, hb⟩ := regularCardinal_maps_bounded hκ hγ hg
    obtain ⟨a, ha, hξa⟩ := hf.2 (S.check ξ) ((S.check_mem_iff _ _).mpr hξ)
    obtain ⟨i, hi, rfl⟩ := (S.mem_check_iff γ a).mp ha
    rw [S.check_value (by rw [domain_eq_of_mem_function hg]; exact hi)] at hξa
    have hξi : ξ ⊆ g ‘ i := (S.checkEmbedding.subset_iff _ _).mp hξa
    exact False.elim (mem_irrefl (g ‘ i) (hξi _ (hb i hi)))
  refine ⟨hcf ▸ internalCofinality_initial (S.check κ), ?_, hcf⟩
  have hh := (S.checkEmbedding.subset_iff (ω : V) κ).mpr hκ.2.1
  change S.check ω ⊆ S.check κ at hh
  rwa [show S.check ω = (ω : S.Model) from S.checkEmbedding.map_omega] at hh

end ForcingContext
end ZFVP
