import ZFVP.SetTheory.NameValue

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_nameValue_subset (G τ : V) : rank (nameValue G τ) ⊆ rank τ := by
  have h := projectedRank_induction (nameClosure τ) (fun x : V ↦ x) (by definability)
    (fun σ ↦ rank (nameValue G σ) ⊆ rank σ) (by definability) ?_
  · exact h τ (mem_nameClosure_self τ)
  intro σ hσ ih
  apply rank_minimal _ _ inferInstance
  intro x hx
  obtain ⟨υ, p, _, hυp, rfl⟩ := (mem_nameValue_iff _ _ _).mp hx
  apply (mem_hierarchy_iff_rank_mem _ _).mpr
  have hlt := rank_subname_lt hυp
  have hle := ih υ (nameClosure_closed τ σ hσ υ (mem_domain_of_kpair_mem hυp)) hlt
  rcases IsOrdinal.subset_iff.mp hle with he | hm
  · exact he.symm ▸ hlt
  · exact IsOrdinal.toIsTransitive.mem_trans hm hlt

theorem nameValue_mem_hierarchy {G τ α : V} [IsOrdinal α] (hτ : τ ∈ hierarchy α) :
    nameValue G τ ∈ hierarchy α := by
  apply (mem_hierarchy_iff_rank_mem _ _).mpr
  have hlt := (mem_hierarchy_iff_rank_mem _ _).mp hτ
  rcases IsOrdinal.subset_iff.mp (rank_nameValue_subset G τ) with he | hm
  · exact he.symm ▸ hlt
  · exact IsOrdinal.toIsTransitive.mem_trans hm hlt

noncomputable def namesBelow (P α : V) : V := {τ ∈ hierarchy α ; IsForcingName P τ}

theorem mem_namesBelow_iff (P α τ : V) :
    τ ∈ namesBelow P α ↔ τ ∈ hierarchy α ∧ IsForcingName P τ := mem_sep_iff

theorem namesBelow_closed (P α : V) [IsOrdinal α] : IsSubnameClosed (namesBelow P α) := by
  intro τ hτ σ hσ
  obtain ⟨hτV, hτN⟩ := (mem_namesBelow_iff _ _ _).mp hτ
  obtain ⟨p, hσp⟩ := mem_domain_iff.mp hσ
  apply (mem_namesBelow_iff _ _ _).mpr
  refine ⟨?_, forcingName_subname hτN hσp⟩
  apply (mem_hierarchy_iff_rank_mem _ _).mpr
  exact IsOrdinal.toIsTransitive.mem_trans (rank_subname_lt hσp)
    ((mem_hierarchy_iff_rank_mem _ _).mp hτV)

end ZFVP
