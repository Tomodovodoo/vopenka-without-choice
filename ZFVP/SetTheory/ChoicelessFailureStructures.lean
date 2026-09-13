import ZFVP.SetTheory.ChoicelessFailureStages
import ZFVP.ModelTheory.NamedMembershipEmbedding
import ZFVP.SetTheory.ProperClassRanks

/-! Expanded rank structures for the failure-class Vopenka argument.
The extra name is the predecessor marker; the other names fix all ordinals
through the prescribed bound. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def choicelessFailureName (α σ i : V) : V := by
  classical
  exact if i = succ α then σ else i

instance choicelessFailureName_definable : ℒₛₑₜ-function₃[V] choicelessFailureName := by
  have hd : ℒₛₑₜ-relation₄[V] (fun x α σ i ↦
      (i = succ α ∧ x = σ) ∨ (i ≠ succ α ∧ x = i)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = choicelessFailureName (v 1) (v 2) (v 3) ↔ _
  unfold choicelessFailureName
  split <;> simp_all

noncomputable def choicelessFailureNames (α σ : V) : V :=
  definableGraph (succ (succ α)) (choicelessFailureName α σ) (by definability)

instance choicelessFailureNames_definable : ℒₛₑₜ-function₂[V] choicelessFailureNames := by
  have hd : ℒₛₑₜ-relation₃[V] (fun g α σ ↦ ∀ p,
      p ∈ g ↔ ∃ i ∈ succ (succ α), p = ⟨i, choicelessFailureName α σ i⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = choicelessFailureNames (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [choicelessFailureNames, mem_definableGraph_iff]

theorem choicelessFailureNames_marker (α σ : V) :
    (choicelessFailureNames α σ) ‘ (succ α) = σ := by
  rw [choicelessFailureNames, value_definableGraph _ _ _ (mem_succ_self _)]
  simp [choicelessFailureName]

theorem choicelessFailureNames_fixed (α σ : V) {i : V} (hi : i ∈ succ α) :
    (choicelessFailureNames α σ) ‘ i = i := by
  have hne : i ≠ succ α := by rintro rfl; exact mem_irrefl _ hi
  rw [choicelessFailureNames, value_definableGraph _ _ _ (mem_succ_iff.mpr (Or.inr hi))]
  simp [choicelessFailureName, hne]

theorem choicelessFailureNames_mem {α σ β : V} [IsOrdinal β]
    (hαβ : α ∈ β) (hσβ : σ ∈ β) :
    choicelessFailureNames α σ ∈ hierarchy β ^ (succ (succ α)) := by
  let : IsOrdinal α := IsOrdinal.of_mem hαβ
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  classical
  by_cases he : i = succ α
  · simp only [choicelessFailureName, he, ite_true]
    exact ordinal_subset_hierarchy β σ hσβ
  · have hi' : i ∈ succ α := (mem_succ_iff.mp hi).resolve_left he
    have hiβ : i ∈ β := by
      rcases mem_succ_iff.mp hi' with rfl | hiα
      · exact hαβ
      · exact IsOrdinal.toIsTransitive.mem_trans hiα hαβ
    simp only [choicelessFailureName, he, ite_false]
    exact ordinal_subset_hierarchy β i hiβ

noncomputable def choicelessFailureStructure (α σ β : V) : V :=
  namedMembershipStructureCode (succ (succ α)) (hierarchy β) (choicelessFailureNames α σ)

instance choicelessFailureStructure_definable : ℒₛₑₜ-function₃[V] choicelessFailureStructure := by
  unfold choicelessFailureStructure
  definability

@[simp] theorem choicelessFailureStructure_domain (α σ β : V) :
    structureDomain (choicelessFailureStructure α σ β) = hierarchy β :=
  namedMembershipStructureCode_domain _ _ _

def IsChoicelessFailureStructure (n k : ℕ) (α M : V) : Prop :=
  ∃ σ β, IsChoicelessFailureStage n k α σ ∧ IsNextChoicelessFailureStage n k α σ β ∧
    M = choicelessFailureStructure α σ β

instance isChoicelessFailureStructure_definable (n k : ℕ) :
    ℒₛₑₜ-relation[V] (IsChoicelessFailureStructure n k) := by
  unfold IsChoicelessFailureStructure
  definability

theorem choicelessFailureStructure_expansion {α σ β : V} [IsOrdinal β]
    (hαβ : α ∈ β) (hσβ : σ ∈ β) :
    IsMembershipExpansion (namedMembershipLanguageCode (succ (succ α)))
      (choicelessFailureStructure α σ β) :=
  namedMembershipStructureCode_expansion ⟨σ, ordinal_subset_hierarchy β σ hσβ⟩
    (choicelessFailureNames_mem hαβ hσβ)

theorem IsChoicelessFailureStructure.valid {n k : ℕ} {α M : V}
    (h : IsChoicelessFailureStructure n k α M) :
    IsStructureCode (namedMembershipLanguageCode (succ (succ α))) M := by
  obtain ⟨σ, β, _, hβ, rfl⟩ := h
  let := hβ.1
  exact (choicelessFailureStructure_expansion hβ.2.1.2.1.2.1 hβ.2.1.1).2.1

theorem choicelessFailureStructure_proper (n k : ℕ) (α : V) [IsOrdinal α]
    (h : ∀ γ, ¬IsAlphaChoicelessExtendible n α γ) :
    IsProperClass (IsChoicelessFailureStructure n k α) := by
  intro X
  obtain ⟨σ, hXσ, hσ⟩ := choicelessFailureStage_unbounded n k α (rank X) h
  let := hσ.1.1
  obtain ⟨β, hβ, _⟩ := nextChoicelessFailureStage_existsUnique n k α σ h
  let := hβ.1
  refine ⟨choicelessFailureStructure α σ β, ⟨σ, β, hσ, hβ, rfl⟩, ?_⟩
  intro hMX
  have hM := subset_hierarchy_rank X _ hMX
  let := hierarchy_transitive (rank X)
  have hA : hierarchy β ∈ hierarchy (rank X) :=
    (kpair_components_mem_transitive hM).1
  have hβX : β ∈ rank X := by
    simpa only [rank_hierarchy] using (mem_hierarchy_iff_rank_mem (hierarchy β) (rank X)).mp hA
  have hXβ := IsOrdinal.toIsTransitive.mem_trans hXσ hβ.2.1.1
  exact mem_irrefl β (IsOrdinal.toIsTransitive.mem_trans hβX hXβ)

end ZFVP
