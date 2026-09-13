import ZFVP.ModelTheory.TwoMarkerMembership
import ZFVP.SetTheory.VopenkaZFRanks
import ZFVP.SetTheory.LeastRankWitnesses
import ZFVP.SetTheory.NaturalAddition

/-! Canonical expanded ZF rank structures for an unbounded ordinal witness relation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def witnessRankBound (ρ α X : V) : V :=
  ordinalAdd ((ρ ∪ α) ∪ rank X) (ω : V)

instance witnessRankBound_definable : ℒₛₑₜ-function₃[V] witnessRankBound := by
  unfold witnessRankBound
  definability

instance witnessRankBound_ordinal (ρ α X : V) [IsOrdinal ρ] [IsOrdinal α] :
    IsOrdinal (witnessRankBound ρ α X) := by
  let := ordinal_union_ordinal ρ α
  let := ordinal_union_ordinal (ρ ∪ α) (rank X)
  unfold witnessRankBound
  infer_instance

theorem witnessRankBound_above (ρ α X : V) [IsOrdinal ρ] [IsOrdinal α] :
    ρ ∈ witnessRankBound ρ α X ∧ α ∈ witnessRankBound ρ α X ∧ rank X ∈ witnessRankBound ρ α X := by
  let := ordinal_union_ordinal ρ α
  let := ordinal_union_ordinal (ρ ∪ α) (rank X)
  have hb := ordinalAdd_omega_gt ((ρ ∪ α) ∪ rank X)
  have hm {δ : V} [IsOrdinal δ] (hd : δ ⊆ (ρ ∪ α) ∪ rank X) :
      δ ∈ witnessRankBound ρ α X := by
    rcases IsOrdinal.subset_iff.mp hd with he | he
    · simpa only [he, witnessRankBound] using hb
    · exact IsOrdinal.toIsTransitive.mem_trans he hb
  refine ⟨hm ?_, hm ?_, hm ?_⟩ <;> intro z hz
  · simp only [mem_union_iff]; exact Or.inl (Or.inl hz)
  · simp only [mem_union_iff]; exact Or.inl (Or.inr hz)
  · simp only [mem_union_iff]; exact Or.inr hz

def IsWitnessRankStage (R : V → V → Prop) (ρ α X θ : V) : Prop :=
  IsOrdinal α ∧ IsLeastRankWitnessSet R α X ∧ IsLeastZFRankAbove (witnessRankBound ρ α X) θ

theorem isWitnessRankStage_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (ρ : V) :
    ℒₛₑₜ-relation₃[V] (IsWitnessRankStage R ρ) := by
  have := isLeastRankWitnessSet_definable R hR
  unfold IsWitnessRankStage
  definability

theorem witnessRankStage_exists
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (ρ α : V) [IsOrdinal ρ] [IsOrdinal α]
    (hex : ∃ τ, R α τ) : ∃ X θ, IsWitnessRankStage R ρ α X θ := by
  obtain ⟨X, hX, _⟩ := leastRankWitnessSet_existsUnique R hR α hex
  obtain ⟨θ, hθ, _⟩ := leastZFRankAbove_existsUnique hVP (witnessRankBound ρ α X)
  exact ⟨X, θ, inferInstance, hX, hθ⟩

theorem IsWitnessRankStage.bounds {R : V → V → Prop} {ρ α X θ : V} [IsOrdinal ρ]
    (h : IsWitnessRankStage R ρ α X θ) : ρ ∈ θ ∧ α ∈ θ ∧ rank X ∈ θ := by
  let := h.1
  let := h.2.2.1
  obtain ⟨hρ, hα, hX⟩ := witnessRankBound_above ρ α X
  exact ⟨IsOrdinal.toIsTransitive.mem_trans hρ h.2.2.2.1.1,
    IsOrdinal.toIsTransitive.mem_trans hα h.2.2.2.1.1,
    IsOrdinal.toIsTransitive.mem_trans hX h.2.2.2.1.1⟩

theorem IsWitnessRankStage.structure_expansion {R : V → V → Prop} {ρ α X θ : V} [IsOrdinal ρ]
    (h : IsWitnessRankStage R ρ α X θ) :
    IsMembershipExpansion (namedMembershipLanguageCode (succ (succ (hierarchy ρ))))
      (twoMarkerStructure (hierarchy ρ) (hierarchy θ) α X) := by
  let := h.2.2.1
  obtain ⟨hρ, hα, hX⟩ := h.bounds
  exact twoMarkerStructure_expansion h.2.2.2.1.2.1.1
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive ρ hρ))
    (ordinal_subset_hierarchy θ α hα) ((mem_hierarchy_iff_rank_mem X θ).mpr hX)

def IsWitnessRankStructure (R : V → V → Prop) (ρ M : V) : Prop :=
  ∃ α X θ, IsWitnessRankStage R ρ α X θ ∧ M = twoMarkerStructure (hierarchy ρ) (hierarchy θ) α X

theorem isWitnessRankStructure_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (ρ : V) :
    ℒₛₑₜ-predicate (IsWitnessRankStructure R ρ) := by
  have := isWitnessRankStage_definable R hR ρ
  unfold IsWitnessRankStructure
  definability

theorem IsWitnessRankStructure.valid {R : V → V → Prop} {ρ M : V} [IsOrdinal ρ]
    (h : IsWitnessRankStructure R ρ M) :
    IsStructureCode (namedMembershipLanguageCode (succ (succ (hierarchy ρ)))) M := by
  obtain ⟨α, X, θ, h, rfl⟩ := h
  exact h.structure_expansion.2.1

theorem witnessRankStructure_proper
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (ρ : V) [IsOrdinal ρ]
    (hu : ∀ δ : V, IsOrdinal δ → ∃ α τ, IsOrdinal α ∧ δ ∈ α ∧ R α τ) :
    IsProperClass (IsWitnessRankStructure R ρ) := by
  intro C
  obtain ⟨α, τ, hα, hCα, hτ⟩ := hu (rank C) inferInstance
  let := hα
  obtain ⟨X, θ, h⟩ := witnessRankStage_exists hVP R hR ρ α ⟨τ, hτ⟩
  let := h.2.2.1
  refine ⟨twoMarkerStructure (hierarchy ρ) (hierarchy θ) α X, ⟨α, X, θ, h, rfl⟩, ?_⟩
  intro hm
  have hM := subset_hierarchy_rank C _ hm
  let := hierarchy_transitive (rank C)
  have hA : hierarchy θ ∈ hierarchy (rank C) := (kpair_components_mem_transitive hM).1
  have hθC : θ ∈ rank C := by
    simpa only [rank_hierarchy] using (mem_hierarchy_iff_rank_mem (hierarchy θ) (rank C)).mp hA
  have hCθ := IsOrdinal.toIsTransitive.mem_trans hCα h.bounds.2.1
  exact mem_irrefl θ (IsOrdinal.toIsTransitive.mem_trans hθC hCθ)

theorem IsWitnessRankStage.unique {R : V → V → Prop} (hR : ℒₛₑₜ-relation R)
    {ρ α X Y θ η : V} (h : IsWitnessRankStage R ρ α X θ) (k : IsWitnessRankStage R ρ α Y η) :
    X = Y ∧ θ = η := by
  obtain ⟨τ, hτ⟩ := h.2.1.nonempty
  obtain ⟨Z, _, hu⟩ := leastRankWitnessSet_existsUnique R hR α ⟨τ, h.2.1.witness hτ⟩
  have he : X = Y := (hu X h.2.1).trans (hu Y k.2.1).symm
  subst Y
  exact ⟨rfl, subset_antisymm (h.2.2.2.2 η k.2.2.1 k.2.2.2.1)
    (k.2.2.2.2 θ h.2.2.1 h.2.2.2.1)⟩

theorem vopenka_witnessRank_embedding
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (ρ : V) [IsOrdinal ρ]
    (hu : ∀ δ : V, IsOrdinal δ → ∃ α τ, IsOrdinal α ∧ δ ∈ α ∧ R α τ) :
    ∃ α β X Y θ η f : V,
      α ≠ β ∧ IsWitnessRankStage R ρ α X θ ∧ IsWitnessRankStage R ρ β Y η ∧
      IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f ∧
      f ‘ α = β ∧ f ‘ X = Y ∧ ∀ i ∈ hierarchy ρ, f ‘ i = i := by
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ := vopenka_definable_class hVP
    (namedMembershipLanguageCode (succ (succ (hierarchy ρ)))) (IsWitnessRankStructure R ρ)
    (isWitnessRankStructure_definable R hR ρ) (witnessRankStructure_proper hVP R hR ρ hu)
    (fun _ h ↦ h.valid)
  obtain ⟨α, X, θ, h, rfl⟩ := hM
  obtain ⟨β, Y, η, k, rfl⟩ := hN
  let := h.2.2.1
  have hv := hf.twoMarker_values
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive ρ h.bounds.1))
    (ordinal_subset_hierarchy θ α h.bounds.2.1)
    ((mem_hierarchy_iff_rank_mem X θ).mpr h.bounds.2.2)
  refine ⟨α, β, X, Y, θ, η, f, ?_, h, k, ?_, hv⟩
  · intro he
    subst β
    obtain ⟨rfl, rfl⟩ := h.unique hR k
    exact hne rfl
  · simpa only [twoMarkerStructure_domain] using
      hf.membership_reduct h.structure_expansion k.structure_expansion

end ZFVP
