import ZFVP.SetTheory.WeaklyLSNoSmallSurjection
import ZFVP.SetTheory.SmallSurjectionProduct
import ZFVP.ModelTheory.ElementaryCofinalProductSurjection
import ZFVP.ModelTheory.ElementaryParameterClosure

/-! Small sets do not map cofinally into successors of cardinals above a weakly LS cardinal. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWeaklyLSCardinal.no_small_cofinalMap {κ x lam f : V}
    (hκ : IsWeaklyLSCardinal κ) (hx : x ∈ hierarchy κ) (hκlam : κ ⊆ lam)
    (hlam : IsInitialOrdinal lam) : ¬IsCofinalMap (hartogsNumber lam) x f := by
  intro hf
  let := hκ.1.1
  let := hlam.1
  let := IsFunction.of_mem hf.1
  let θ := hartogsNumber lam
  have hωκ : (ω : V) ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hκ.2.1
  have hωlam : (ω : V) ⊆ lam := subset_trans hωκ hκlam
  have hlamθ : lam ∈ θ := ordinal_cardLE_iff_mem_hartogsNumber.mp (CardLE.refl lam)
  have hωθ : (ω : V) ⊆ θ := subset_trans hωlam (IsOrdinal.toIsTransitive.transitive _ hlamθ)
  let p := ⟨f, lam⟩ₖ
  let α := rank ({p, θ ^ lam, κ} : V)
  let := hierarchy_transitive α
  have hpα : p ∈ hierarchy α := (mem_hierarchy_iff_rank_mem _ _).mpr
    (rank_mem (show p ∈ ({p, θ ^ lam, κ} : V) by simp))
  have hpowα : θ ^ lam ∈ hierarchy α := (mem_hierarchy_iff_rank_mem _ _).mpr
    (rank_mem (show θ ^ lam ∈ ({p, θ ^ lam, κ} : V) by simp))
  have hκα : κ ∈ α := by
    simpa only [rank_of_ordinal] using rank_mem (show κ ∈ ({p, θ ^ lam, κ} : V) by simp)
  have hrκ : rank x ∈ κ := (mem_hierarchy_iff_rank_mem _ _).mp hx
  obtain ⟨X, hX, hγX, hpX, C, hC, e, he⟩ := hκ.2.2 (rank x) hrκ α inferInstance
    (IsOrdinal.toIsTransitive.transitive _ hκα) p hpα
  obtain ⟨hfX, hlamX⟩ := hX.kpair_components_mem hpX
  have hcof : ∀ z ∈ θ, ∃ η ∈ X, η ∈ θ ∧ z ∈ η := by
    intro z hz
    have hsz : succ z ∈ θ := initial_succ_mem (hartogsNumber_initial lam) hωθ hz
    obtain ⟨a, ha, hbound⟩ := hf.2 (succ z) hsz
    have haX := hγX a (subset_hierarchy_rank x a ha)
    have hvaX := hX.function_value_mem hfX haX (domain_eq_of_mem_function hf.1 |>.symm ▸ ha)
    exact ⟨f ‘ a, hvaX, function_value_mem hf.1 ha, hbound z (by simp)⟩
  obtain ⟨g, hg, hgr⟩ := elementaryCofinal_product_surjection hX he hlamX hpowα
    (hωθ ∅ empty_mem_ω)
    (fun η hη hne ↦ surjection_of_injection (cardLE_of_mem_hartogsNumber hη) hne) hcof
  exact no_surjection_prod_hartogs ⟨ω, hκ.2.1⟩ hκlam hlam hωlam
    (fun q hq ↦ hκ.no_small_surjection hC hq) hg hgr

end ZFVP
