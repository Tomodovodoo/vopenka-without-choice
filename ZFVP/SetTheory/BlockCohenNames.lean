import ZFVP.SetTheory.BlockCohenSystem
import ZFVP.SetTheory.CohenSetName

/-!
Names for the block Cohen system of Jech's first embedding theorem: the Cohen real of an index
in `ω ×ˢ ω`, the block of `ω` reals sharing a first coordinate, and the set of all blocks.

These are the same names as in the basic Cohen model, but the group is the smaller
`blockCohenGroup` and the filter is `blockCohenFilter`, whose supports are finite sets of
conditions. The row marker conditions of `CohenSymmetricSystem` supply those supports.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Block permutations hit every index of the image block -/

/-- A block permutation maps the block `a` onto the whole block `ρ ‘ a`. -/
theorem blockPermutation_block_surjective {π ρ a : V} (h : IsBlockPermutation π ρ)
    (ha : a ∈ (ω : V)) : ∀ η ∈ (ω : V), ∃ ξ ∈ (ω : V), π ‘ ⟨a, ξ⟩ₖ = ⟨ρ ‘ a, η⟩ₖ := by
  intro η hη
  have hρa : ρ ‘ a ∈ (ω : V) := function_value_mem h.2.1.1 ha
  obtain ⟨z, hz, hzv⟩ := h.1.surjective (kpair_mem_iff.mpr ⟨hρa, hη⟩)
  obtain ⟨b, hb, ξ, hξ, rfl⟩ := mem_prod_iff.mp hz
  obtain ⟨θ, _, hθ⟩ := h.2.2 b hb ξ hξ
  have hρ : ρ ‘ b = ρ ‘ a := (kpair_iff.mp (hθ.symm.trans hzv)).1
  have hba : b = a := injective_value_eq h.2.1.1 h.2.1.2.1 hb ha hρ
  exact ⟨ξ, hξ, hba ▸ hzv⟩

/-! ### The Cohen real of an index -/

/-- The name of the Cohen real at index `i` is hereditarily symmetric for the block system. -/
theorem cohenRealName_blockHereditarilySymmetric {i : V} (hi : i ∈ (ω : V) ×ˢ (ω : V)) :
    IsHereditarilySymmetricName (cohenConditions ((ω : V) ×ˢ (ω : V))) blockCohenGroup
      blockCohenFilter (cohenRealName ((ω : V) ×ˢ (ω : V)) i) := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨cohenRealName_isName _ i, ?_⟩, ?_⟩
  · refine (mem_finiteStabilizerFilter _ _ _).mpr
      ⟨nameStabilizer_subgroup blockCohenGroup_group (cohenRealName_isName _ i),
        ({cohenRowMarker i} : V), ?_, ?_, ?_⟩
    · intro p hp
      exact (mem_singleton_iff.mp hp) ▸ cohenRowMarker_condition hi
    · simpa using internallyFinite_insert (internallyFinite_empty (V := V)) (cohenRowMarker i)
    · intro σ hσ
      obtain ⟨hσG, hσfix⟩ := (mem_pointwiseStabilizer _ _ _).mp hσ
      obtain ⟨π, ρ, hπρ, rfl⟩ := (mem_blockCohenGroup σ).mp hσG
      have hπi : π ‘ i = i :=
        (cohenRowMarker_fix_iff hi).mp (hσfix _ (mem_singleton_iff.mpr rfl))
      refine mem_sep_iff.mpr ⟨hσG, ?_⟩
      rw [nameAction_cohenRealName hπρ.1 hi, hπi]
  · intro σ p hσp
    obtain ⟨_, n, _, rfl, _⟩ := (pair_mem_cohenRealName _ i σ p).mp hσp
    exact hereditarilySymmetric_checkName (cohen_poset _) blockCohenGroup_group
      blockCohenFilter_normal (cohen_top _) n

/-! ### The block of an index -/

/-- The name of the set of the `ω` Cohen reals of block `a`. -/
noncomputable def blockName (a : V) : V :=
  repl (fun ξ ↦ ⟨cohenRealName ((ω : V) ×ˢ (ω : V)) ⟨a, ξ⟩ₖ, (∅ : V)⟩ₖ) (by definability) (ω : V)

theorem mem_blockName (a z : V) : z ∈ blockName a ↔
    ∃ ξ ∈ (ω : V), z = ⟨cohenRealName ((ω : V) ×ˢ (ω : V)) ⟨a, ξ⟩ₖ, (∅ : V)⟩ₖ := repl_spec _

instance blockName_definable : ℒₛₑₜ-function₁[V] blockName := by
  have h : ℒₛₑₜ-relation[V] (fun A a ↦ ∀ z, z ∈ A ↔
      ∃ ξ ∈ (ω : V), z = ⟨cohenRealName ((ω : V) ×ˢ (ω : V)) ⟨a, ξ⟩ₖ, (∅ : V)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = blockName (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_blockName]

theorem blockName_isName (a : V) :
    IsForcingName (cohenConditions ((ω : V) ×ˢ (ω : V))) (blockName a) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨ξ, _, rfl⟩ := (mem_blockName a z).mp hz
  exact ⟨_, ∅, (cohen_top _).1, rfl, cohenRealName_isName _ _⟩

theorem nameAction_blockName {π ρ a : V} (h : IsBlockPermutation π ρ) (ha : a ∈ (ω : V)) :
    nameAction (cohenPermutation ((ω : V) ×ˢ (ω : V)) π) (blockName a) = blockName (ρ ‘ a) := by
  have hauto := cohenPermutation_automorphism h.1
  have htop := forcingAutomorphism_top (cohen_poset ((ω : V) ×ˢ (ω : V))) (cohen_top _) hauto
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨σ, p, hσp, rfl⟩ := (mem_nameAction_iff (blockName_isName a) _ z).mp hz
    obtain ⟨ξ, hξ, he⟩ := (mem_blockName a _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    obtain ⟨η, hη, hπη⟩ := h.2.2 a ha ξ hξ
    rw [nameAction_cohenRealName h.1 (kpair_mem_iff.mpr ⟨ha, hξ⟩), hπη, htop]
    exact (mem_blockName _ _).mpr ⟨η, hη, rfl⟩
  · intro hz
    obtain ⟨η, hη, rfl⟩ := (mem_blockName (ρ ‘ a) z).mp hz
    obtain ⟨ξ, hξ, hπη⟩ := blockPermutation_block_surjective h ha η hη
    refine (mem_nameAction_iff (blockName_isName a) _ _).mpr
      ⟨cohenRealName ((ω : V) ×ˢ (ω : V)) ⟨a, ξ⟩ₖ, ∅,
        (mem_blockName a _).mpr ⟨ξ, hξ, rfl⟩, ?_⟩
    rw [nameAction_cohenRealName h.1 (kpair_mem_iff.mpr ⟨ha, hξ⟩), hπη, htop]

theorem blockName_hereditarilySymmetric {a : V} (ha : a ∈ (ω : V)) :
    IsHereditarilySymmetricName (cohenConditions ((ω : V) ×ˢ (ω : V))) blockCohenGroup
      blockCohenFilter (blockName a) := by
  have ha0 : ⟨a, (0 : V)⟩ₖ ∈ (ω : V) ×ˢ (ω : V) :=
    kpair_mem_iff.mpr ⟨ha, by simp⟩
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨blockName_isName a, ?_⟩, ?_⟩
  · refine (mem_finiteStabilizerFilter _ _ _).mpr
      ⟨nameStabilizer_subgroup blockCohenGroup_group (blockName_isName a),
        ({cohenRowMarker ⟨a, (0 : V)⟩ₖ} : V), ?_, ?_, ?_⟩
    · intro p hp
      exact (mem_singleton_iff.mp hp) ▸ cohenRowMarker_condition ha0
    · simpa using
        internallyFinite_insert (internallyFinite_empty (V := V)) (cohenRowMarker ⟨a, (0 : V)⟩ₖ)
    · intro σ hσ
      obtain ⟨hσG, hσfix⟩ := (mem_pointwiseStabilizer _ _ _).mp hσ
      obtain ⟨π, ρ, hπρ, rfl⟩ := (mem_blockCohenGroup σ).mp hσG
      have hπ0 : π ‘ ⟨a, (0 : V)⟩ₖ = ⟨a, (0 : V)⟩ₖ :=
        (cohenRowMarker_fix_iff ha0).mp (hσfix _ (mem_singleton_iff.mpr rfl))
      obtain ⟨η, _, hη⟩ := hπρ.2.2 a ha (0 : V) (by simp)
      have hρa : ρ ‘ a = a := (kpair_iff.mp (hη.symm.trans hπ0)).1
      refine mem_sep_iff.mpr ⟨hσG, ?_⟩
      rw [nameAction_blockName hπρ ha, hρa]
  · intro σ p hσp
    obtain ⟨ξ, hξ, he⟩ := (mem_blockName a _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact cohenRealName_blockHereditarilySymmetric (kpair_mem_iff.mpr ⟨ha, hξ⟩)

/-! ### The set of all blocks -/

/-- The name of the set whose elements are the `ω` blocks. -/
noncomputable def blockSetName : V :=
  repl (fun a ↦ ⟨blockName a, (∅ : V)⟩ₖ) (by definability) (ω : V)

theorem mem_blockSetName (z : V) : z ∈ (blockSetName : V) ↔
    ∃ a ∈ (ω : V), z = ⟨blockName a, (∅ : V)⟩ₖ := repl_spec _

theorem blockSetName_isName :
    IsForcingName (cohenConditions ((ω : V) ×ˢ (ω : V))) (blockSetName : V) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨a, _, rfl⟩ := (mem_blockSetName z).mp hz
  exact ⟨blockName a, ∅, (cohen_top _).1, rfl, blockName_isName a⟩

theorem nameAction_blockSetName {π ρ : V} (h : IsBlockPermutation π ρ) :
    nameAction (cohenPermutation ((ω : V) ×ˢ (ω : V)) π) (blockSetName : V) = blockSetName := by
  have hauto := cohenPermutation_automorphism h.1
  have htop := forcingAutomorphism_top (cohen_poset ((ω : V) ×ˢ (ω : V))) (cohen_top _) hauto
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨σ, p, hσp, rfl⟩ := (mem_nameAction_iff blockSetName_isName _ z).mp hz
    obtain ⟨a, ha, he⟩ := (mem_blockSetName _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    rw [nameAction_blockName h ha, htop]
    exact (mem_blockSetName _).mpr ⟨ρ ‘ a, function_value_mem h.2.1.1 ha, rfl⟩
  · intro hz
    obtain ⟨b, hb, rfl⟩ := (mem_blockSetName z).mp hz
    obtain ⟨a, ha, hab⟩ := h.2.1.surjective hb
    refine (mem_nameAction_iff blockSetName_isName _ _).mpr
      ⟨blockName a, ∅, (mem_blockSetName _).mpr ⟨a, ha, rfl⟩, ?_⟩
    rw [nameAction_blockName h ha, hab, htop]

theorem nameStabilizer_blockSetName :
    nameStabilizer (blockCohenGroup : V) blockSetName = blockCohenGroup := by
  ext σ
  simp only [nameStabilizer, mem_sep_iff]
  refine ⟨And.left, fun hσ ↦ ?_⟩
  obtain ⟨π, ρ, hπρ, rfl⟩ := (mem_blockCohenGroup σ).mp hσ
  exact ⟨hσ, nameAction_blockSetName hπρ⟩

theorem blockSetName_hereditarilySymmetric :
    IsHereditarilySymmetricName (cohenConditions ((ω : V) ×ˢ (ω : V))) blockCohenGroup
      blockCohenFilter (blockSetName : V) := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨blockSetName_isName, ?_⟩, ?_⟩
  · rw [nameStabilizer_blockSetName]
    exact blockCohenFilter_normal.2.1
  · intro σ p hσp
    obtain ⟨a, ha, he⟩ := (mem_blockSetName _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact blockName_hereditarilySymmetric ha

end ZFVP
