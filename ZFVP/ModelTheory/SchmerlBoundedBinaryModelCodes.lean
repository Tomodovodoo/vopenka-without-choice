import ZFVP.ModelTheory.InternalBinaryGraphRelabeling

/-! A fixed actual set of bounded binary model codes, and normalization of
an internally countable initial model into the first uncountable ordinal. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def boundedBinaryModelPairs (κ : V) : V :=
  {p ∈ power κ ×ˢ power (κ ×ˢ κ) ; kpair.π₂ p ⊆ kpair.π₁ p ×ˢ kpair.π₁ p}

instance boundedBinaryModelPairs_definable : ℒₛₑₜ-function₁[V] boundedBinaryModelPairs := by
  have hh : ℒₛₑₜ-relation[V] (fun P κ ↦ ∀ p, p ∈ P ↔
      p ∈ power κ ×ˢ power (κ ×ˢ κ) ∧ kpair.π₂ p ⊆ kpair.π₁ p ×ˢ kpair.π₁ p) := by
    definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [boundedBinaryModelPairs, mem_sep_iff]
  rfl

theorem pair_mem_boundedBinaryModelPairs {κ D E : V} :
    ⟨D, E⟩ₖ ∈ boundedBinaryModelPairs κ ↔ D ⊆ κ ∧ E ⊆ D ×ˢ D := by
  simp only [boundedBinaryModelPairs, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair, mem_power_iff]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩,
    fun h ↦ ⟨⟨h.1, subset_trans h.2 (prod_subset_prod_of_subset h.1 h.1)⟩, h.2⟩⟩

noncomputable def boundedBinaryModelCodes (κ : V) : V :=
  repl (fun p ↦ binaryRelationStructureCode (kpair.π₁ p) (kpair.π₂ p))
    (by definability) (boundedBinaryModelPairs κ)

theorem mem_boundedBinaryModelCodes {κ M : V} :
    M ∈ boundedBinaryModelCodes κ ↔
      ∃ D E, D ⊆ κ ∧ E ⊆ D ×ˢ D ∧ M = binaryRelationStructureCode D E := by
  rw [boundedBinaryModelCodes, repl_spec]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨D, _, E, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hp).1
    obtain ⟨hD, hE⟩ := pair_mem_boundedBinaryModelPairs.mp hp
    exact ⟨D, E, hD, hE, by simp only [kpair.π₁_kpair, kpair.π₂_kpair]⟩
  · rintro ⟨D, E, hD, hE, rfl⟩
    exact ⟨⟨D, E⟩ₖ, pair_mem_boundedBinaryModelPairs.mpr ⟨hD, hE⟩,
      by simp only [kpair.π₁_kpair, kpair.π₂_kpair]⟩

instance boundedBinaryModelCodes_definable : ℒₛₑₜ-function₁[V] boundedBinaryModelCodes := by
  have hh : ℒₛₑₜ-relation[V] (fun C κ ↦ ∀ M, M ∈ C ↔
      ∃ D E, D ⊆ κ ∧ E ⊆ D ×ˢ D ∧ M = binaryRelationStructureCode D E) := by
    definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [mem_boundedBinaryModelCodes]
  rfl

theorem binaryRelationStructureCode_mem_boundedBinaryModelCodes {κ D E : V}
    (hD : D ⊆ κ) (hE : E ⊆ D ×ˢ D) :
    binaryRelationStructureCode D E ∈ boundedBinaryModelCodes κ :=
  mem_boundedBinaryModelCodes.mpr ⟨D, E, hD, hE, rfl⟩

theorem boundedBinaryModelCodes_domain_subset {κ M : V} (hM : M ∈ boundedBinaryModelCodes κ) :
    structureDomain M ⊆ κ := by
  obtain ⟨D, E, hD, _, rfl⟩ := mem_boundedBinaryModelCodes.mp hM
  simpa only [binaryRelationStructureCode_domain] using hD

theorem binaryRelabelStructure_mem_boundedBinaryModelCodes {κ D E h : V}
    (hh : h ∈ κ ^ D) : binaryRelabelStructure E h ∈ boundedBinaryModelCodes κ :=
  binaryRelationStructureCode_mem_boundedBinaryModelCodes
    (range_subset_of_mem_function hh) (binaryRelabelEdges_subset E h)

theorem exists_hartogsOmega_normalized_codedZF {D E : V}
    (hM : IsCodedZFModel (binaryRelationStructureCode D E))
    (hcount : IsInternallyCountable D) :
    ∃ N ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)),
      ∃ h ∈ hartogsNumber (ω : V) ^ D, Injective h ∧
        N = binaryRelabelStructure E h ∧ IsCodedZFModel N ∧
        IsInternallyCountable (structureDomain N) ∧
        IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D E) N h := by
  obtain ⟨h, hh, hhi⟩ := hcount
  have hωκ : (ω : V) ⊆ hartogsNumber (ω : V) :=
    IsTransitive.transitive _ omega_mem_hartogs_omega
  have hhκ : h ∈ hartogsNumber (ω : V) ^ D := mem_function_of_mem_function_of_subset hh hωκ
  have hD : IsNonempty D := by
    simpa only [binaryRelationStructureCode_domain] using hM.valid.domain_nonempty
  refine ⟨binaryRelabelStructure E h, binaryRelabelStructure_mem_boundedBinaryModelCodes hhκ,
    h, hhκ, hhi, rfl, binaryRelabel_codedZF hM hhκ hhi, ?_, binaryRelabel_elementary hD hhκ hhi⟩
  exact binaryRelabel_countable ⟨h, hh, hhi⟩ hhκ

end ZFVP.Schmerl
