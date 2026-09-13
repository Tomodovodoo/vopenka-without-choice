import ZFVP.ModelTheory.NormalizedIsomorphismNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem normalizedIsomorphismName_mem_pool {P R A B one top δ U f τ : V}
    (hf : IsForcingIsomorphism P R A B f) (hB : IsForcingPreorder A B)
    (ht : top ∈ A) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ)
    (hU : IsForcingName P U) (hτ : τ ∈ normalizedNamePool P R one δ U) :
    normalizedIsomorphismName A B top f τ ∈ normalizedNamePool A B top δ (nameAction f U) := by
  obtain ⟨hτδ, hτN, _, hτU⟩ := mem_sep_iff.mp hτ
  apply mem_sep_iff.mpr
  refine ⟨normalizedIsomorphismName_mem_hierarchy hf hB ht hδ hP hA hτN hτδ,
    normalizedIsomorphismName_isName hf hB ht hτN,
    normalizedIsomorphismName_fixed hf hB ht hτN, ?_⟩
  apply atomicMembership_subst_left hB (normalizedIsomorphismName_equal hf hB ht hτN)
  simpa only [hft] using atomicMembership_isomorphism_forward hf hτN hU hτU

noncomputable def normalizedIsomorphismPoolMap (P R one δ U A B top f : V) : V :=
  definableGraph (normalizedNamePool P R one δ U) (normalizedIsomorphismName A B top f) (by
    apply Language.DefinableFunction₅.comp <;> definability)

theorem normalizedIsomorphismPoolMap_value {P R one δ U A B top f τ : V}
    (hτ : τ ∈ normalizedNamePool P R one δ U) :
    (normalizedIsomorphismPoolMap P R one δ U A B top f) ‘ τ = normalizedIsomorphismName A B top f τ :=
  value_definableGraph _ _ _ hτ

theorem normalizedIsomorphismPoolMap_bijection {P R A B one top δ U f : V}
    (hf : IsForcingIsomorphism P R A B f) (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : one ∈ P) (ht : top ∈ A) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ)
    (hU : IsForcingName P U) :
    let F := normalizedIsomorphismPoolMap P R one δ U A B top f
    F ∈ (normalizedNamePool A B top δ (nameAction f U)) ^ (normalizedNamePool P R one δ U) ∧
      Injective F ∧ range F = normalizedNamePool A B top δ (nameAction f U) := by
  dsimp only
  have hm : normalizedIsomorphismPoolMap P R one δ U A B top f ∈
      (normalizedNamePool A B top δ (nameAction f U)) ^ (normalizedNamePool P R one δ U) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _
      (fun _ hτ ↦ normalizedIsomorphismName_mem_pool hf hB ht hft hδ hP hA hU hτ)
  have hback : (converseGraph f) ‘ top = one := by rw [← hft, hf.inverse_value ho]
  refine ⟨hm, ?_, ?_⟩
  · intro σ τ z hσ hτ
    obtain ⟨hσP, hzσ⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hσ
    obtain ⟨hτP, hzτ⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hτ
    have he := congrArg (normalizedIsomorphismName P R one (converseGraph f)) (hzσ.symm.trans hzτ)
    have hσ' := mem_sep_iff.mp hσP
    have hτ' := mem_sep_iff.mp hτP
    simpa only [normalizedIsomorphismName_inverse hf hR hB ho ht hft hσ'.2.1 hσ'.2.2.1,
      normalizedIsomorphismName_inverse hf hR hB ho ht hft hτ'.2.1 hτ'.2.2.1] using he
  · apply subset_antisymm (range_subset_of_mem_function hm)
    intro σ hσ
    let τ := normalizedIsomorphismName P R one (converseGraph f) σ
    have hτ : τ ∈ normalizedNamePool P R one δ U := by
      simpa only [hf.name_inverse_cancel hU] using normalizedIsomorphismName_mem_pool hf.inverse hR
        ho hback hδ hA hP (nameAction_isName hf.1 hU) hσ
    have hσ' := mem_sep_iff.mp hσ
    have he : normalizedIsomorphismName A B top f τ = σ := by
      dsimp only [τ]
      rw [normalizedIsomorphismName_comp hf.inverse hf hR hB ho ht hft hσ'.2.1, hf.inverse_compose]
      unfold normalizedIsomorphismName
      rw [nameAction_identity hσ'.2.1, hσ'.2.2.1]
    have hv := value_mem_range hm hτ
    rwa [normalizedIsomorphismPoolMap_value hτ, he] at hv

end ZFVP
