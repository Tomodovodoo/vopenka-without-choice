import ZFVP.SetTheory.SubnameRecursion

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameClosure_equation (τ : V) :
    nameClosure τ = insert τ (⋃ˢ repl nameClosure (by definability) (domain τ)) := by
  let X := insert τ (⋃ˢ repl nameClosure (by definability) (domain τ))
  have hX : IsSubnameClosed X := by
    intro σ hσ υ hυ
    rcases mem_insert.mp hσ with heq | hσ
    · subst σ
      apply mem_insert.mpr
      apply Or.inr
      exact mem_sUnion_iff.mpr ⟨nameClosure υ, (repl_spec (by definability)).mpr ⟨υ, hυ, rfl⟩,
        mem_nameClosure_self υ⟩
    · obtain ⟨C, hC, hσC⟩ := mem_sUnion_iff.mp hσ
      obtain ⟨ξ, hξ, rfl⟩ := (repl_spec (by definability)).mp hC
      exact mem_insert.mpr (Or.inr (mem_sUnion_iff.mpr
        ⟨nameClosure ξ, (repl_spec (by definability)).mpr ⟨ξ, hξ, rfl⟩, nameClosure_closed ξ σ hσC υ hυ⟩))
  apply SetTheory.subset_antisymm (nameClosure_minimal hX (by simp [X]))
  intro σ hσ
  rcases mem_insert.mp hσ with heq | hσ
  · subst σ
    exact mem_nameClosure_self τ
  · obtain ⟨C, hC, hσC⟩ := mem_sUnion_iff.mp hσ
    obtain ⟨ξ, hξ, rfl⟩ := (repl_spec (by definability)).mp hC
    exact nameClosure_mem_mono (nameClosure_closed τ τ (mem_nameClosure_self τ) ξ hξ) σ hσC

theorem restrict_definableGraph_of_subset {C D : V} (hDC : D ⊆ C)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    (definableGraph C F hF) ↾ D = definableGraph D F hF := by
  apply functions_eq_of_domain_values
  · rw [domain_restrict_eq, domain_definableGraph, domain_definableGraph]
    apply SetTheory.mem_ext_iff.mpr
    intro x
    simp only [mem_inter_iff]
    exact ⟨And.right, fun h ↦ ⟨hDC x h, h⟩⟩
  · intro x hx
    rw [domain_restrict_eq, domain_definableGraph] at hx
    have hd := (mem_inter_iff.mp hx).2
    rw [value_restrict (by simpa only [domain_definableGraph] using hDC x hd) hd,
      value_definableGraph _ _ _ (hDC x hd), value_definableGraph _ _ _ hd]

noncomputable def nameClosureStep (τ f : V) : V := insert τ (⋃ˢ range f)

instance nameClosureStep_definable : ℒₛₑₜ-function₂[V] nameClosureStep := by
  unfold nameClosureStep
  definability

theorem nameClosure_graph_recursion {C : V} (hC : IsSubnameClosed C) :
    IsSubnameRecursion C nameClosureStep (definableGraph C nameClosure (by definability)) := by
  refine ⟨inferInstance, domain_definableGraph _ _ _, ?_⟩
  intro τ hτ
  rw [value_definableGraph _ _ _ hτ, nameClosureStep,
    restrict_definableGraph_of_subset (hC τ hτ), range_definableGraph]
  exact nameClosure_equation τ

theorem nameClosure_eq_subnameRecursion (τ : V) :
    nameClosure τ = subnameRecursion nameClosureStep (by definability) τ := by
  have he := subnameRecursion_coherent (nameClosure_closed τ) (nameClosure_closed τ)
    (nameClosure_graph_recursion (nameClosure_closed τ))
    (subnameRecursionTable_spec nameClosureStep (by definability) τ)
    τ (mem_nameClosure_self τ) (mem_nameClosure_self τ)
  change nameClosure τ = ((subnameRecursionTable nameClosureStep (by definability) τ) ‘ τ)
  simpa only [value_definableGraph _ _ _ (mem_nameClosure_self τ)] using he

end ZFVP
