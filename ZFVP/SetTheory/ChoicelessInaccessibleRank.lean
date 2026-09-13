import ZFVP.SetTheory.ChoicelessInaccessible
import ZFVP.SetTheory.PiOneRankCriterion
import ZFVP.SetTheory.FiniteCofinality

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCofinalMap.extend_domain {κ X Y g i : V} (hg : IsCofinalMap κ X g)
    (hXY : X ⊆ Y) (hi : i ∈ X) : ∃ f, IsCofinalMap κ Y f := by
  classical
  let F := fun x ↦ if x ∈ X then g ‘ x else g ‘ i
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation (fun y x : V ↦ (x ∈ X ∧ y = g ‘ x) ∨ (x ∉ X ∧ y = g ‘ i)) := by
      definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = F (v 1) ↔ _
    by_cases hv : v 1 ∈ X <;> simp [F, hv]
  let f := definableGraph Y F hF
  refine ⟨f, definableGraph_mem_function_of_mapsTo _ _ _ _ ?_, ?_⟩
  · intro x hx
    dsimp [F]
    split_ifs with h
    · exact function_value_mem hg.1 h
    · exact function_value_mem hg.1 hi
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := hg.2 z hz
    refine ⟨x, hXY x hx, ?_⟩
    rw [show f ‘ x = F x from value_definableGraph _ _ _ (hXY x hx)]
    simpa [F, hx] using hzx

theorem IsChoicelessInaccessible.no_rank_cofinalMap {κ X g : V}
    (hκ : IsChoicelessInaccessible κ) (hX : X ∈ hierarchy κ) : ¬IsCofinalMap κ X g := by
  let := hκ.1
  intro hg
  have hz : (∅ : V) ∈ κ := IsOrdinal.toIsTransitive.mem_trans (by simp) hκ.2.1
  obtain ⟨i, hi, _⟩ := hg.2 ∅ hz
  obtain ⟨f, hf⟩ := hg.extend_domain (subset_hierarchy_rank X) hi
  exact hκ.2.2 (rank X) ((mem_hierarchy_iff_rank_mem X κ).mp hX) f hf

theorem IsChoicelessInaccessible.cofinality {κ : V} (hκ : IsChoicelessInaccessible κ) :
    internalCofinality κ = κ := by
  let := hκ.1
  rcases IsOrdinal.subset_iff.mp (internalCofinality_subset κ) with he | hlt
  · exact he
  · obtain ⟨g, hg⟩ := cofinalMap_exists κ
    exact False.elim (hκ.no_rank_cofinalMap (ordinal_mem_hierarchy_iff.mpr hlt) hg)

theorem IsChoicelessInaccessible.regular {κ : V} (hκ : IsChoicelessInaccessible κ) :
    IsRegularCardinal κ := by
  let := hκ.1
  exact ⟨hκ.cofinality ▸ internalCofinality_initial κ,
    IsOrdinal.toIsTransitive.transitive _ hκ.2.1, hκ.cofinality⟩

theorem IsChoicelessInaccessible.rankCriterion {κ : V} (hκ : IsChoicelessInaccessible κ) :
    IsRankCriterionHeight κ :=
  ⟨hκ.1, hκ.2.1, fun _ ha ↦ regularCardinal_succ_closed hκ.regular ha,
    fun _ hX _ ↦ hκ.no_rank_cofinalMap hX⟩

theorem IsChoicelessInaccessible.internalZFModel {κ : V} (hκ : IsChoicelessInaccessible κ) :
    IsInternalZFModel (hierarchy κ) := hκ.rankCriterion.internalZFModel

end ZFVP
