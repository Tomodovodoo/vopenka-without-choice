import ZFVP.ModelTheory.WoodinCollapseBoundedGeneric
import ZFVP.ModelTheory.WoodinCollapseModel
import ZFVP.ModelTheory.ForcingFunctionDecisionDensity
import ZFVP.ModelTheory.ForcingSmallFunctions

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinCollapseModel

theorem function_values_bounded {κ δ γ : V} (hκ : IsRegularCardinal κ)
    (hδ : IsChoicelessInaccessible δ) (hκδ : κ ∈ δ) (hγ : γ ∈ δ) {G : Set V}
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)
    {f : (woodinCollapseContext hκ δ G hG).Model}
    (hf : f ∈ (woodinCollapseContext hκ δ G hG).check δ ^
      (woodinCollapseContext hκ δ G hG).check γ) :
    ∃ ξ ∈ δ, ∀ a ∈ (woodinCollapseContext hκ δ G hG).check γ,
      f ‘ a ∈ (woodinCollapseContext hκ δ G hG).check ξ := by
  let A := woodinCollapseContext hκ δ G hG
  let := hδ.1
  let := IsOrdinal.of_mem hγ
  obtain ⟨τ, rfl⟩ := A.ofName_surjective f
  let E := checkedValueDecisions A.P A.R A.one τ.val δ
  have hE (i : V) : E i ⊆ A.P := sep_subset
  let D := fun i ↦ E i ∪ forcingNegation A.P A.R (E i)
  have hD : ℒₛₑₜ-function₁ D := by unfold D E; definability
  have hd (i : V) (_hi : i ∈ γ) : ForcingDense A.P A.R (D i) :=
    forcing_decisions_dense A.order (hE i)
  obtain ⟨β, hβ, ho, hb⟩ := woodinCollapse_generic_bounded_dense_family
    hδ hκ hκδ hγ D hD hd hG
  let := ho
  have hdec : ∀ i ∈ γ, ∃ p ∈ G, p ∈ hierarchy β ∧
      ∃ y ∈ δ, ForcesCheckedFunctionValue A.P A.R A.one τ.val p i y := by
    intro i hi
    obtain ⟨y, hy, hey⟩ := (A.mem_check_iff δ _).mp
      (function_value_mem hf ((A.check_mem_iff _ _).mpr hi))
    let := IsFunction.of_mem hf
    obtain ⟨p₀, hp₀, hp₀y⟩ := (A.checkedFunctionValue_truth τ i y).mpr ⟨inferInstance, hey⟩
    have hmeet : GenericMeets G (E i) :=
      ⟨p₀, hp₀, mem_sep_iff.mpr ⟨A.generic.1.1 p₀ hp₀, y, hy, hp₀y⟩⟩
    obtain ⟨p, hpG, hpD, hpV⟩ := hb i hi
    rcases mem_union_iff.mp hpD with hpE | hpN
    · exact ⟨p, hpG, hpV, (mem_sep_iff.mp hpE).2⟩
    · exact False.elim ((genericMeets_negation A.order A.generic (hE i)
        (checkedValueDecisions_downward A.order)).mp ⟨p, hpG, hpN⟩ hmeet)
  let g := {z ∈ (γ ×ˢ hierarchy β) ×ˢ δ ;
    ForcesCheckedFunctionValue A.P A.R A.one τ.val (kpair.π₂ (kpair.π₁ z))
      (kpair.π₁ (kpair.π₁ z)) (kpair.π₂ z)}
  have hgmem (z y : V) : ⟨z, y⟩ₖ ∈ g ↔ z ∈ γ ×ˢ hierarchy β ∧ y ∈ δ ∧
      ForcesCheckedFunctionValue A.P A.R A.one τ.val (kpair.π₂ z) (kpair.π₁ z) y := by
    simp [g, and_assoc]
  have hgfun : g ∈ δ ^ domain g := by
    apply mem_function.intro
    · intro c hc
      obtain ⟨z, hz, y, hy, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hc).1
      exact mem_prod_iff.mpr ⟨z, mem_domain_of_kpair_mem hc, y, hy, rfl⟩
    · intro z hz
      obtain ⟨y, hzy⟩ := mem_domain_iff.mp hz
      refine ⟨y, hzy, fun w hzw ↦ ?_⟩
      exact forcesCheckedFunctionValue_unique A.order A.top τ.property
        ((hgmem z w).mp hzw).2.2 ((hgmem z y).mp hzy).2.2
  let := IsFunction.of_mem hgfun
  have hdsub : domain g ⊆ γ ×ˢ hierarchy β := by
    intro z hz
    obtain ⟨y, hzy⟩ := mem_domain_iff.mp hz
    exact ((hgmem z y).mp hzy).1
  have hs : ∀ ξ ∈ δ, succ ξ ∈ δ := fun _ hξ ↦ regularCardinal_succ_closed hδ.regular hξ
  have hdg : domain g ∈ hierarchy δ := subset_mem_hierarchy_limit hs
    (prod_mem_hierarchy_limit hs (ordinal_mem_hierarchy_iff.mpr hγ) (hierarchy_mem hβ)) hdsub
  have hn : NoLowRankCofinalMaps δ := fun _ ha _ ↦ hδ.no_rank_cofinalMap ha
  obtain ⟨ξ, hξ, hh⟩ := hn.map_bounded hdg hgfun
  refine ⟨ξ, hξ, ?_⟩
  intro a ha
  obtain ⟨i, hi, rfl⟩ := (A.mem_check_iff γ a).mp ha
  obtain ⟨p, hpG, hpV, y, hy, hpy⟩ := hdec i hi
  have hey := (A.checkedFunctionValue_truth τ i y).mp ⟨p, hpG, hpy⟩
  have hiy : ⟨⟨i, p⟩ₖ, y⟩ₖ ∈ g := (hgmem _ _).mpr
    ⟨kpair_mem_iff.mpr ⟨hi, hpV⟩, hy, by simpa using hpy⟩
  have hyξ : y ∈ ξ := by
    simpa only [value_eq_of_kpair_mem hiy] using hh _ (mem_domain_of_kpair_mem hiy)
  exact hey.2 ▸ (A.check_mem_iff y ξ).mpr hyξ

end WoodinCollapseModel
end ZFVP
