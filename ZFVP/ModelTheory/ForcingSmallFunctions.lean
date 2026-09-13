import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.ModelTheory.ForcingModelChecks
import ZFVP.SetTheory.ChoicelessInaccessibleRank
import ZFVP.SetTheory.RankCollection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- A small forcing cannot add an unbounded function from a checked low-rank
set into a ground inaccessible. Possible values are indexed by ground pairs
of inputs and conditions; uniqueness gives a partial function without choice. -/
theorem function_values_bounded_of_small (A : ForcingContext V) {δ X : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hX : X ∈ hierarchy δ)
    {f : A.Model} (hf : f ∈ A.check δ ^ A.check X) :
    ∃ β ∈ δ, ∀ a ∈ A.check X, f ‘ a ∈ A.check β := by
  let := hδ.1
  obtain ⟨τ, rfl⟩ := A.ofName_surjective f
  let g := {z ∈ (X ×ˢ A.P) ×ˢ δ ;
    ForcesCheckedFunctionValue A.P A.R A.one τ.val (kpair.π₂ (kpair.π₁ z))
      (kpair.π₁ (kpair.π₁ z)) (kpair.π₂ z)}
  have hgmem (z y : V) : ⟨z, y⟩ₖ ∈ g ↔ z ∈ X ×ˢ A.P ∧ y ∈ δ ∧
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
  have hdsub : domain g ⊆ X ×ˢ A.P := by
    intro z hz
    obtain ⟨y, hzy⟩ := mem_domain_iff.mp hz
    exact ((hgmem z y).mp hzy).1
  have hs : ∀ β ∈ δ, succ β ∈ δ := fun _ hb ↦ regularCardinal_succ_closed hδ.regular hb
  have hd : domain g ∈ hierarchy δ := subset_mem_hierarchy_limit hs
    (prod_mem_hierarchy_limit hs hX hP) hdsub
  have hn : NoLowRankCofinalMaps δ := fun _ ha _ ↦ hδ.no_rank_cofinalMap ha
  obtain ⟨β, hβ, hb⟩ := hn.map_bounded hd hgfun
  refine ⟨β, hβ, ?_⟩
  intro a ha
  obtain ⟨x, hx, rfl⟩ := (A.mem_check_iff X a).mp ha
  let := IsFunction.of_mem hf
  obtain ⟨y, hy, hey⟩ := (A.mem_check_iff δ _).mp
    (function_value_mem hf ((A.check_mem_iff _ _).mpr hx))
  obtain ⟨p, hp, hpxy⟩ := (A.checkedFunctionValue_truth τ x y).mpr ⟨inferInstance, hey⟩
  have hxy : ⟨⟨x, p⟩ₖ, y⟩ₖ ∈ g := (hgmem _ _).mpr
    ⟨kpair_mem_iff.mpr ⟨hx, A.generic.1.1 p hp⟩, hy, by simpa using hpxy⟩
  have hyβ : y ∈ β := by
    simpa only [value_eq_of_kpair_mem hxy] using hb _ (mem_domain_of_kpair_mem hxy)
  exact hey ▸ (A.check_mem_iff y β).mpr hyβ

end ForcingContext
end ZFVP
