import ZFVP.SetTheory.BoundedCodingSupport
import ZFVP.SetTheory.FunctionValue

/-! Rank is characterized by bounded equations on a transitive set of arguments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_cofinal {x β : V} (hβ : β ∈ rank x) : ∃ y ∈ x, β ⊆ rank y := by
  let := IsOrdinal.of_mem hβ
  by_contra! h
  have hsub : rank x ⊆ β := rank_minimal x β inferInstance (by
    intro y hy
    apply (mem_hierarchy_iff_rank_mem y β).mpr
    rcases IsOrdinal.mem_trichotomy (rank y) β with hl | he | hg
    · exact hl
    · exact False.elim (h y hy (he ▸ subset_refl (rank y)))
    · exact False.elim (h y hy (IsOrdinal.toIsTransitive.transitive _ hg)))
  exact mem_irrefl β (hsub β hβ)

theorem rank_characterization (x α : V) : α = rank x ↔
    IsOrdinal α ∧ (∀ y ∈ x, rank y ∈ α) ∧ ∀ β ∈ α, ∃ y ∈ x, β ⊆ rank y := by
  constructor
  · rintro rfl
    exact ⟨inferInstance, fun _ hy ↦ rank_mem hy, fun _ hβ ↦ rank_cofinal hβ⟩
  · rintro ⟨hα, hupper, hcof⟩
    let := hα
    apply SetTheory.subset_antisymm
    · intro β hβ
      let := IsOrdinal.of_mem hβ
      obtain ⟨y, hy, hby⟩ := hcof β hβ
      rcases IsOrdinal.subset_iff.mp hby with he | hl
      · exact he ▸ rank_mem hy
      · exact IsOrdinal.toIsTransitive.mem_trans hl (rank_mem hy)
    · exact rank_minimal x α hα (fun y hy ↦ (mem_hierarchy_iff_rank_mem y α).mpr (hupper y hy))

def IsRankTable (T R f : V) : Prop := f ∈ R ^ T ∧ ∀ x ∈ T,
  IsOrdinal (f ‘ x) ∧ (∀ y ∈ x, f ‘ y ∈ f ‘ x) ∧ ∀ β ∈ f ‘ x, ∃ y ∈ x, β ⊆ f ‘ y

instance isRankTable_definable : ℒₛₑₜ-relation₃[V] IsRankTable := by
  unfold IsRankTable
  definability

theorem rankTable_correct {T R f : V} [hT : IsTransitive T] (hf : IsRankTable T R f) :
    ∀ x ∈ T, f ‘ x = rank x := by
  intro x
  apply set_induction (fun x : V ↦ x ∈ T → f ‘ x = rank x) (by definability) ?_ x
  intro x ih hx
  apply (rank_characterization x (f ‘ x)).mpr
  obtain ⟨ho, hupper, hcof⟩ := hf.2 x hx
  refine ⟨ho, ?_, ?_⟩
  · intro y hy
    rw [← ih y hy (hT.mem_trans hy hx)]
    exact hupper y hy
  · intro β hβ
    obtain ⟨y, hy, hby⟩ := hcof β hβ
    exact ⟨y, hy, (ih y hy (hT.mem_trans hy hx)) ▸ hby⟩

theorem rankTable_exists (T : V) [hT : IsTransitive T] : ∃ R f : V, IsRankTable T R f := by
  let f := definableGraph T rank (rank_definable (V := V))
  refine ⟨repl rank rank_definable T, f, definableGraph_mem_function _ _ _, ?_⟩
  intro x hx
  have hxval : f ‘ x = rank x := value_definableGraph _ _ _ hx
  have hyval (y : V) (hy : y ∈ x) : f ‘ y = rank y := value_definableGraph _ _ _ (hT.mem_trans hy hx)
  rw [hxval]
  refine ⟨inferInstance, ?_, ?_⟩
  · intro y hy
    rw [hyval y hy]
    exact rank_mem hy
  · intro β hβ
    obtain ⟨y, hy, hby⟩ := rank_cofinal hβ
    exact ⟨y, hy, (hyval y hy).symm ▸ hby⟩

end ZFVP
