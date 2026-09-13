import ZFVP.ModelTheory.SchmerlCodedRubinSource
import ZFVP.SetTheory.LevyCollapseSmallSets
import ZFVP.SetTheory.HartogsRegularChoice
import ZFVP.SetTheory.CountableSets

/-! Internal countable subsets of a cofinal chain have a common upper bound. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The least chain index above `x`, formed by internal separation and intersection. -/
noncomputable def cofinalChainIndex (κ R c x : V) : V :=
  ⋂ˢ {i ∈ κ ; ⟨x, c ‘ i⟩ₖ ∈ R}

theorem cofinalChainIndex_definable (κ R c : V) :
    ℒₛₑₜ-function₁[V] (cofinalChainIndex κ R c) := by
  have hS : ℒₛₑₜ-function₁[V] (fun x ↦ {i ∈ κ ; ⟨x, c ‘ i⟩ₖ ∈ R}) := by
    have hd : ℒₛₑₜ-relation[V] (fun S x ↦
        ∀ i, i ∈ S ↔ i ∈ κ ∧ ⟨x, c ‘ i⟩ₖ ∈ R) := by definability
    apply Language.Definable.of_iff hd
    intro v
    rw [mem_ext_iff]
    simp only [mem_sep_iff]
    rfl
  unfold cofinalChainIndex
  definability

theorem cofinalChainIndex_spec {κ P R c x : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ P R c) (hx : x ∈ P) :
    cofinalChainIndex κ R c x ∈ κ ∧ ⟨x, c ‘ (cofinalChainIndex κ R c x)⟩ₖ ∈ R := by
  let S := {i ∈ κ ; ⟨x, c ‘ i⟩ₖ ∈ R}
  obtain ⟨i, hi, hxi⟩ := hc.2.2 x hx
  have : IsNonempty S := ⟨i, mem_sep_iff.mpr ⟨hi, hxi⟩⟩
  exact mem_sep_iff.mp (IsOrdinal.sInter_mem (X := S)
    (fun j hj ↦ IsOrdinal.of_mem (mem_sep_iff.mp hj).1))

/-- This uses actual internal indices; no enumeration or externally chosen map is assumed. -/
theorem exists_countable_cofinalChain_upperBound {κ P R F c U : V}
    (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hR : IsForcingPreorder P R) (hFP : F ⊆ P)
    (hc : IsInternalCofinalStrictChain κ F R c)
    (hU : IsInternallyCountable U) (hUF : U ⊆ F) :
    ∃ e ∈ F, ∀ u ∈ U, ⟨u, e⟩ₖ ∈ R := by
  have := hκ.1.1
  let J := cofinalChainIndex κ R c
  have hJ := cofinalChainIndex_definable κ R c
  let g := definableGraph U J hJ
  have hg : g ∈ κ ^ U :=
    definableGraph_mem_function_of_mapsTo U κ J hJ
      (fun u hu ↦ (cofinalChainIndex_spec hc (hUF u hu)).1)
  have hgr : IsInternallyCountable (range g) := internallyCountable_range
    (internallyCountable_function (by simpa only [g, domain_definableGraph] using hU))
  obtain ⟨ξ, hξ, hb⟩ := regular_small_subset_bounded hκ
    (range_subset_of_mem_function hg) hω hgr
  refine ⟨c ‘ ξ, function_value_mem hc.1 hξ, fun u hu ↦ ?_⟩
  have hgu : g ‘ u = J u := value_definableGraph U J hJ hu
  have hi : g ‘ u ∈ κ := function_value_mem hg hu
  have hui : ⟨u, c ‘ (g ‘ u)⟩ₖ ∈ R := by
    rw [hgu]
    exact (cofinalChainIndex_spec hc (hUF u hu)).2
  exact hR.2.2 u (hFP u (hUF u hu)) (c ‘ (g ‘ u))
    (hFP _ (function_value_mem hc.1 hi)) (c ‘ ξ)
    (hFP _ (function_value_mem hc.1 hξ)) hui
    (hc.2.1 _ hi ξ hξ (hb _ (value_mem_range hg hu))).1

theorem exists_hartogsOmega_cofinalChain_upperBound (hAC : InternalChoice V)
    {P R F c U : V} (hR : IsForcingPreorder P R) (hFP : F ⊆ P)
    (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V)) F R c)
    (hU : IsInternallyCountable U) (hUF : U ⊆ F) :
    ∃ e ∈ F, ∀ u ∈ U, ⟨u, e⟩ₖ ∈ R :=
  exists_countable_cofinalChain_upperBound (hartogsNumber_regular hAC (CardLE.refl _))
    omega_mem_hartogs_omega hR hFP hc hU hUF

end ZFVP.Schmerl
