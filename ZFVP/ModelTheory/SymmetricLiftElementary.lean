import ZFVP.ModelTheory.SymmetricLiftTruth
import ZFVP.ModelTheory.CodedElementaryEmbedding

/-! Restrict the internal symmetric graph to an arbitrary-language structure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (L : SymmetricLiftData S U W f)

theorem structure_restriction_function {language M : S.Model} (hM : IsStructureCode language M)
    (hm : M ∈ domain L.graph) :
    (L.graph ↾ (structureDomain M)) ∈ structureDomain (L.graph ‘ M) ^ structureDomain M := by
  have hsub := L.structureDomain_subset_graph_domain hM hm
  have hD : structureDomain M ∈ domain L.graph := (kpair_components_mem_transitive (hM.2.1 ▸ hm)).1
  apply mem_function.intro
  · intro p hp
    obtain ⟨hpf, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
    apply kpair_mem_iff.mpr
    refine ⟨hx, ?_⟩
    have hy := value_eq_of_kpair_mem hpf
    have hmem := (L.graph_value_mem_iff (hsub x hx) hD).mpr hx
    rwa [hy, L.graph_value_structureDomain hM hm] at hmem
  · intro x hx
    refine ⟨L.graph ‘ x, kpair_mem_restrict_iff.mpr ⟨kpair_value_mem (hsub x hx), hx⟩, ?_⟩
    intro y hy
    exact (value_eq_of_kpair_mem (kpair_mem_restrict_iff.mp hy).1).symm

theorem structure_restriction_elementary {language M : S.Model} (hM : IsStructureCode language M)
    (hm : M ∈ domain L.graph) (hl : language ∈ domain L.graph)
    (hfix : L.graph ‘ language = language)
    (hF : functionSymbols language ⊆ domain L.graph) (hR : relationSymbols language ⊆ domain L.graph)
    (hfixF : ∀ g ∈ functionSymbols language, L.graph ‘ g = g)
    (hfixR : ∀ g ∈ relationSymbols language, L.graph ‘ g = g) :
    IsCodedElementaryEmbedding language M (L.graph ‘ M) ((L.graph ↾ (structureDomain M))) := by
  have hN := (L.graph_structureCode_iff hl hm).mpr hM
  rw [hfix] at hN
  refine ⟨hM, hN, L.structure_restriction_function hM hm, ?_⟩
  intro n hn φ hφ b hb
  have hΓ : (∅ : S.Model) ⊆ domain L.graph := empty_subset _
  have hfixΓ : ∀ x ∈ (∅ : S.Model), L.graph ‘ x = x := fun _ hx ↦ (not_mem_empty hx).elim
  have hbD := mem_function_of_mem_function_of_subset hb (L.structureDomain_subset_graph_domain hM hm)
  have hbm := function_mem_sequenceSupport (subset_refl (domain L.graph)) hn hbD
  have hφm := formula_mem_sequenceSupport hM.language hF hR hΓ hφ
  have hφfix := L.graph_value_formula hM.language hF hR hΓ hfixF hfixR hfixΓ hφ
  have ht := L.graph_satisfies_iff hM.language hl IsCodingSupport.empty_mem hm IsCodingSupport.empty_mem
    (IsCodingSupport.natural_mem hn) hφm hbm
  rw [hfix, L.graph_value_empty, L.graph_value_natural hn, hφfix, L.graph_value_assignment hn hbD] at ht
  rw [graph_compose_restrict hb]
  exact ht.symm

end SymmetricLiftData
end ZFVP
