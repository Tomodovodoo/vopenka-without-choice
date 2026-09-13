import ZFVP.SetTheory.WoodinCollapse
import ZFVP.SetTheory.RegularSmallRank

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCollapse_condition_mem_hierarchy {κ β p : V} (hβ : IsRegularCardinal β)
    (hκβ : κ ⊆ β) (hp : p ∈ woodinCollapse κ β) : p ∈ hierarchy β := by
  let := hβ.1.1
  obtain ⟨hs, hf, hsmall, _⟩ := (mem_woodinCollapse _ _ _).mp hp
  let := hf
  have hpSmall : IsCardinalSmall β p := by
    obtain ⟨α, hα, hinj⟩ := hsmall.of_cardLE (function_cardLE_domain p)
    exact ⟨α, hκβ α hα, hinj⟩
  apply regularCardinal_small_subset_hierarchy hβ hpSmall
  intro z hz
  obtain ⟨a, ha, x, hx, rfl⟩ := mem_prod_iff.mp (hs z hz)
  obtain ⟨α, hα, η, hη, rfl⟩ := mem_prod_iff.mp ha
  let := IsOrdinal.of_mem (hκβ α hα)
  let := IsOrdinal.of_mem hη
  exact kpair_mem_hierarchy_limit (fun _ hξ ↦ regularCardinal_succ_closed hβ hξ)
    (kpair_mem_hierarchy_limit (fun _ hξ ↦ regularCardinal_succ_closed hβ hξ)
      (ordinal_mem_hierarchy_iff.mpr (hκβ α hα)) (ordinal_mem_hierarchy_iff.mpr hη)) hx

end ZFVP

