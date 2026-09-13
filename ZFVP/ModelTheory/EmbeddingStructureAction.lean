import ZFVP.ModelTheory.RankEmbeddingDictionary

/-! Structure domains and validity under sufficiently correct rank embeddings. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsStructureCode.domain_mem_transitive {A L M : V} [IsTransitive A]
    (hM : IsStructureCode L M) (hMA : M ∈ A) : structureDomain M ∈ A := by
  have hp : ⟨structureDomain M, ⟨structureFunctions M, structureRelations M⟩ₖ⟩ₖ ∈ A := (congrArg (fun z : V ↦ z ∈ A) hM.2.1).mp hMA
  exact (kpair_components_mem_transitive hp).1

theorem IsCodedMembershipEmbedding.value_structureDomain {A B f L M : V}
    [IsTransitive A] [IsTransitive B] (h : IsCodedMembershipEmbedding A B f)
    (hM : IsStructureCode L M) (hMA : M ∈ A) : f ‘ (structureDomain M) = structureDomain (f ‘ M) := by
  have hp : ⟨structureDomain M, ⟨structureFunctions M, structureRelations M⟩ₖ⟩ₖ ∈ A := (congrArg (fun z : V ↦ z ∈ A) hM.2.1).mp hMA
  obtain ⟨hD, hR⟩ := kpair_components_mem_transitive hp
  have he := h.value_pair hD hR hp
  change f ‘ (structureCode (structureDomain M) (structureFunctions M) (structureRelations M)) = _ at he
  rw [← hM.2.1] at he
  simp only [structureDomain, he, kpair.π₁_kpair]

theorem rankEmbedding_structureCode_iff {k : ℕ} {δ ε f L M : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (k + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hk : coreSyntaxDictionaryBound ≤ k + 1) (hL : L ∈ hierarchy δ) (hM : M ∈ hierarchy δ) :
    IsStructureCode L M ↔ IsStructureCode (f ‘ L) (f ‘ M) :=
  rankEmbedding_coreDictionary_iff hδ hε h hk
    (show ⟨2, isStructureCodeFormula⟩ ∈ coreSyntaxDictionary by simp [coreSyntaxDictionary])
    (fun v ↦ IsStructureCode (v 0) (v 1)) ![L, M] (by simp [hL, hM])

end ZFVP
