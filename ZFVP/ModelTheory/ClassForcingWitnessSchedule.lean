import ZFVP.ModelTheory.ClassForcingDenseWitnessBounds
import ZFVP.SetTheory.LeastOrdinalChoice
import ZFVP.SetTheory.TransfiniteIteration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

def ProjectedWitnessStage (D : V → V → Prop) (I i j k : V) : Prop :=
  IsOrdinal k ∧ j ∈ k ∧ ∀ a ∈ I, ∀ c ∈ T.boundedConditions j,
    ∀ r ∈ T.P i, ⟨r, T.projectCondition i c⟩ₖ ∈ T.R i →
      ∃ q ∈ T.boundedConditions k, D a q ∧ T.LE q c ∧ T.LE q ⟨i, r⟩ₖ

theorem projectedWitnessStage_definable (D : V → V → Prop)
    (hDdef : ℒₛₑₜ-relation D) (I i : V) :
    ℒₛₑₜ-relation (T.ProjectedWitnessStage D I i) := by
  have := T.P_definable
  have := T.R_definable
  unfold ProjectedWitnessStage
  definability

theorem projectedWitnessStage_exists (D : V → V → Prop)
    (hDdef : ℒₛₑₜ-relation D) (I i j : V) [IsOrdinal i] [IsOrdinal j]
    (hD : ∀ a ∈ I, ClassForcingDense T.Condition T.LE (D a)) :
    ∃ k, IsOrdinal k ∧ T.ProjectedWitnessStage D I i j k := by
  obtain ⟨k, hk, hb⟩ := T.denseClasses_projectedWitnessBound D hDdef I (T.boundedConditions j) i hD
  let := hk
  have : IsOrdinal (succ j ∪ k) := ordinal_union_ordinal _ _
  refine ⟨succ j ∪ k, inferInstance, inferInstance,
    mem_union_iff.mpr (Or.inl (mem_succ_self j)), ?_⟩
  intro a ha c hc r hr hrc
  obtain ⟨q, hq, hqa, hqc, hqr⟩ := hb a ha c hc (T.boundedConditions_condition hc) r hr hrc
  exact ⟨q, T.boundedConditions_mono (subset_union_right _ _) q hq, hqa, hqc, hqr⟩

/-- Least ordinal witness bounds give a definable operation. The union makes
it inflationary even on nonordinals, where its default value may be zero. -/
noncomputable def witnessStageStep (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j : V) : V :=
  j ∪ leastOrdinalOrZero (T.ProjectedWitnessStage D I i)
    (T.projectedWitnessStage_definable D hDdef I i) j

theorem witnessStageStep_definable (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i : V) : ℒₛₑₜ-function₁ (T.witnessStageStep D hDdef I i) := by
  unfold witnessStageStep
  definability

theorem witnessStageStep_inflationary (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j : V) : j ⊆ T.witnessStageStep D hDdef I i j := subset_union_left _ _

theorem witnessStageStep_ordinal (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j : V) [IsOrdinal j] : IsOrdinal (T.witnessStageStep D hDdef I i j) :=
  ordinal_union_ordinal _ _

theorem witnessStageStep_spec (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j : V) [IsOrdinal i] [IsOrdinal j]
    (hD : ∀ a ∈ I, ClassForcingDense T.Condition T.LE (D a)) :
    T.ProjectedWitnessStage D I i j (T.witnessStageStep D hDdef I i j) := by
  have h := (leastOrdinalOrZero_spec (T.ProjectedWitnessStage D I i)
    (T.projectedWitnessStage_definable D hDdef I i) j
    (T.projectedWitnessStage_exists D hDdef I i j hD)).2.1
  let k := leastOrdinalOrZero (T.ProjectedWitnessStage D I i)
    (T.projectedWitnessStage_definable D hDdef I i) j
  change T.ProjectedWitnessStage D I i j k at h
  have hjk : j ⊆ k := IsOrdinal.toIsTransitive.transitive _ h.2.1
  have he : j ∪ k = k := by ext x; simp only [mem_union_iff]; exact ⟨fun hx ↦ hx.elim (hjk x) id, Or.inr⟩
  change T.ProjectedWitnessStage D I i j (j ∪ k)
  rwa [he]

noncomputable def witnessStageSchedule (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j : V) : V → V :=
  iterate (T.witnessStageStep D hDdef I i) (T.witnessStageStep_definable D hDdef I i) j

theorem witnessStageSchedule_definable (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j : V) : ℒₛₑₜ-function₁ (T.witnessStageSchedule D hDdef I i j) :=
  iterate_definable (T.witnessStageStep_definable D hDdef I i) j

theorem witnessStageSchedule_ordinal (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j : V) [IsOrdinal j] (α : V) [IsOrdinal α] :
    IsOrdinal (T.witnessStageSchedule D hDdef I i j α) := by
  have hdef := T.witnessStageSchedule_definable D hDdef I i j
  suffices h : ∀ β : Ordinal V, IsOrdinal (T.witnessStageSchedule D hDdef I i j β) from
    h (IsOrdinal.toOrdinal α)
  apply transfinite_induction (fun β ↦ IsOrdinal (T.witnessStageSchedule D hDdef I i j β)) (by definability)
  intro β ih
  have : IsOrdinal (β : V) := β.ordinal
  rcases ordinal_cases (β : V) with h0 | ⟨γ, hγ, he⟩ | hlim
  · simp only [witnessStageSchedule, h0, iterate_zero]
    infer_instance
  · let := hγ
    have hγβ : γ ∈ (β : V) := he ▸ mem_succ_self γ
    have : IsOrdinal (iterate (T.witnessStageStep D hDdef I i)
        (T.witnessStageStep_definable D hDdef I i) j γ) := ih (IsOrdinal.toOrdinal γ) hγβ
    simp only [witnessStageSchedule, he, iterate_succ]
    exact T.witnessStageStep_ordinal D hDdef I i _
  · rw [witnessStageSchedule, iterate_limit _ _ _ hlim]
    apply IsOrdinal.sUnion
    intro z hz
    obtain ⟨γ, hγ, rfl⟩ := (repl_spec _).mp hz
    have : IsOrdinal γ := IsOrdinal.of_mem hγ
    exact ih (IsOrdinal.toOrdinal γ) hγ

theorem witnessStageSchedule_mono (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j : V) {α β : V} [IsOrdinal β] (hαβ : α ∈ β) :
    T.witnessStageSchedule D hDdef I i j α ⊆ T.witnessStageSchedule D hDdef I i j β :=
  iterate_mono (T.witnessStageStep_definable D hDdef I i)
    (T.witnessStageStep_inflationary D hDdef I i) j (IsOrdinal.toOrdinal β) α hαβ

theorem witnessStageSchedule_zero (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j : V) : T.witnessStageSchedule D hDdef I i j ∅ = j :=
  iterate_zero (T.witnessStageStep_definable D hDdef I i) j

theorem witnessStageSchedule_mono_le (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j : V) {α β : V} [IsOrdinal α] [IsOrdinal β] (hαβ : α ⊆ β) :
    T.witnessStageSchedule D hDdef I i j α ⊆ T.witnessStageSchedule D hDdef I i j β := by
  rcases IsOrdinal.subset_iff.mp hαβ with he | hlt
  · rw [he]
  · exact T.witnessStageSchedule_mono D hDdef I i j hlt

theorem witnessStageSchedule_base_subset (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j β : V) [IsOrdinal β] : j ⊆ T.witnessStageSchedule D hDdef I i j β := by
  have h := T.witnessStageSchedule_mono_le D hDdef I i j (empty_subset β)
  rwa [T.witnessStageSchedule_zero] at h

theorem witnessStageSchedule_successor (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (I i j α : V) [IsOrdinal i] [IsOrdinal j] [IsOrdinal α]
    (hD : ∀ a ∈ I, ClassForcingDense T.Condition T.LE (D a)) :
    T.ProjectedWitnessStage D I i (T.witnessStageSchedule D hDdef I i j α)
      (T.witnessStageSchedule D hDdef I i j (succ α)) := by
  have : IsOrdinal (iterate (T.witnessStageStep D hDdef I i)
      (T.witnessStageStep_definable D hDdef I i) j α) := T.witnessStageSchedule_ordinal D hDdef I i j α
  rw [witnessStageSchedule, iterate_succ]
  exact T.witnessStageStep_spec D hDdef I i _ hD

end DefinableForcingTower
end ZFVP
