import ZFVP.SetTheory.ClassForcingTowerOrder
import ZFVP.SetTheory.DenseEmbedding

/-! Each bounded part of the proper-class direct limit is a set forcing.
Its last stage is densely embedded, so a name with bounded stage support
reduces to a genuine set stage. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower

variable (T : DefinableForcingTower V)

noncomputable def boundedConditions (θ : V) : V :=
  ⋃ˢ repl (fun i ↦ ({i} : V) ×ˢ T.P i) (by
    have := T.P_definable
    definability) (succ θ)

instance boundedConditions_definable : ℒₛₑₜ-function₁ T.boundedConditions := by
  have := T.P_definable
  unfold boundedConditions
  definability

theorem mem_boundedConditions (θ c : V) : c ∈ T.boundedConditions θ ↔
    ∃ i ∈ succ θ, ∃ p ∈ T.P i, c = ⟨i, p⟩ₖ := by
  simp only [boundedConditions, mem_sUnion_iff]
  constructor
  · rintro ⟨B, hB, hc⟩
    obtain ⟨i, hi, rfl⟩ := (repl_spec _).mp hB
    obtain ⟨j, hj, p, hp, rfl⟩ := mem_prod_iff.mp hc
    have he : j = i := by simpa using hj
    subst j
    exact ⟨i, hi, p, hp, rfl⟩
  · rintro ⟨i, hi, p, hp, rfl⟩
    exact ⟨_, (repl_spec _).mpr ⟨i, hi, rfl⟩, kpair_mem_iff.mpr ⟨by simp, hp⟩⟩

theorem boundedConditions_condition {θ c : V} [IsOrdinal θ]
    (hc : c ∈ T.boundedConditions θ) : T.Condition c := by
  obtain ⟨i, hi, p, hp, rfl⟩ := (T.mem_boundedConditions _ _).mp hc
  exact (T.condition_pair _ _).mpr ⟨IsOrdinal.of_mem hi, hp⟩

theorem boundedConditions_stage {θ c : V} [IsOrdinal θ]
    (hc : c ∈ T.boundedConditions θ) : kpair.π₁ c ⊆ θ := by
  obtain ⟨i, hi, p, _, rfl⟩ := (T.mem_boundedConditions _ _).mp hc
  simp only [kpair.π₁_kpair]
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact subset_refl _
  · exact IsOrdinal.toIsTransitive.transitive _ hi

theorem tagged_mem_boundedConditions {i θ p : V} [IsOrdinal i] [IsOrdinal θ]
    (hiθ : i ⊆ θ) (hp : p ∈ T.P i) : ⟨i, p⟩ₖ ∈ T.boundedConditions θ := by
  have hi : i ∈ succ θ := by
    rcases IsOrdinal.subset_iff.mp hiθ with rfl | hi
    · exact mem_succ_self _
    · exact mem_succ_iff.mpr (Or.inr hi)
  exact (T.mem_boundedConditions _ _).mpr ⟨i, hi, p, hp, rfl⟩

noncomputable def boundedOrder (θ : V) : V :=
  {z ∈ T.boundedConditions θ ×ˢ T.boundedConditions θ ; T.LE (kpair.π₁ z) (kpair.π₂ z)}

instance boundedOrder_definable : ℒₛₑₜ-function₁ T.boundedOrder := by
  have h : ℒₛₑₜ-relation (fun R θ : V ↦ ∀ z, z ∈ R ↔
      z ∈ T.boundedConditions θ ×ˢ T.boundedConditions θ ∧
        T.LE (kpair.π₁ z) (kpair.π₂ z)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = T.boundedOrder (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [boundedOrder, mem_sep_iff]

theorem pair_mem_boundedOrder (θ c d : V) : ⟨c, d⟩ₖ ∈ T.boundedOrder θ ↔
    c ∈ T.boundedConditions θ ∧ d ∈ T.boundedConditions θ ∧ T.LE c d := by
  simp only [boundedOrder, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem bounded_preorder (θ : V) [IsOrdinal θ] :
    IsForcingPreorder (T.boundedConditions θ) (T.boundedOrder θ) := by
  refine ⟨fun z hz ↦ (mem_sep_iff.mp hz).1, ?_, ?_⟩
  · intro c hc
    exact (T.pair_mem_boundedOrder _ _ _).mpr
      ⟨hc, hc, T.le_refl (T.boundedConditions_condition hc)⟩
  · intro c hc d hd e he hcd hde
    exact (T.pair_mem_boundedOrder _ _ _).mpr
      ⟨hc, he, T.le_trans ((T.pair_mem_boundedOrder _ _ _).mp hcd).2.2
        ((T.pair_mem_boundedOrder _ _ _).mp hde).2.2⟩

theorem one_mem_boundedConditions (θ : V) [IsOrdinal θ] :
    T.one ∈ T.boundedConditions θ :=
  T.tagged_mem_boundedConditions (empty_subset θ) (T.top_spec ∅ inferInstance).1

theorem bounded_top (θ : V) [IsOrdinal θ] :
    IsForcingTop (T.boundedConditions θ) (T.boundedOrder θ) T.one := by
  refine ⟨T.one_mem_boundedConditions θ, fun c hc ↦ ?_⟩
  exact (T.pair_mem_boundedOrder _ _ _).mpr
    ⟨hc, T.one_mem_boundedConditions θ, T.le_one (T.boundedConditions_condition hc)⟩

noncomputable def stageEmbedding (θ : V) : V :=
  definableGraph (T.P θ) (fun p ↦ ⟨θ, p⟩ₖ) (by definability)

theorem stageEmbedding_value {θ p : V} (hp : p ∈ T.P θ) :
    (T.stageEmbedding θ) ‘ p = ⟨θ, p⟩ₖ := value_definableGraph _ _ _ hp

noncomputable def reduceCondition (θ c : V) : V :=
  (T.sectionMap (kpair.π₁ c) θ) ‘ (kpair.π₂ c)

instance reduceCondition_definable : ℒₛₑₜ-function₂ T.reduceCondition := by
  have := T.section_definable
  unfold reduceCondition
  definability

theorem reduceCondition_mem {θ c : V} [IsOrdinal θ]
    (hc : c ∈ T.boundedConditions θ) : T.reduceCondition θ c ∈ T.P θ := by
  have hs := T.condition_spec (T.boundedConditions_condition hc)
  let := hs.1
  exact T.section_mem (T.boundedConditions_stage hc) hs.2.1

theorem reduceCondition_equivalent {θ c : V} [IsOrdinal θ]
    (hc : c ∈ T.boundedConditions θ) :
    T.LE ⟨θ, T.reduceCondition θ c⟩ₖ c ∧ T.LE c ⟨θ, T.reduceCondition θ c⟩ₖ := by
  obtain ⟨i, hi, p, hp, rfl⟩ := (T.mem_boundedConditions _ _).mp hc
  let := IsOrdinal.of_mem hi
  have hiθ : i ⊆ θ := by
    simpa only [kpair.π₁_kpair] using T.boundedConditions_stage hc
  simpa only [reduceCondition, kpair.π₁_kpair, kpair.π₂_kpair, and_comm] using
    T.section_equivalent hiθ hp

theorem stageEmbedding_dense (θ : V) [IsOrdinal θ] :
    IsDenseEmbedding (T.P θ) (T.R θ) (T.boundedConditions θ)
      (T.boundedOrder θ) (T.stageEmbedding θ) := by
  have hmem (p : V) (hp : p ∈ T.P θ) :=
    T.tagged_mem_boundedConditions (subset_refl θ) hp
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ hmem, ?_, ?_, ?_⟩
  · intro p hp q hq hqp
    rw [T.stageEmbedding_value hp, T.stageEmbedding_value hq]
    exact (T.pair_mem_boundedOrder _ _ _).mpr
      ⟨hmem q hq, hmem p hp, (T.le_sameStage_iff hq hp).mpr hqp⟩
  · intro p hp q hq hinc hc
    rw [T.stageEmbedding_value hp, T.stageEmbedding_value hq] at hc
    obtain ⟨c, hc, hcp, hcq⟩ := hc
    have hr := T.reduceCondition_mem hc
    have he := (T.reduceCondition_equivalent hc).1
    apply hinc
    refine ⟨T.reduceCondition θ c, hr, ?_, ?_⟩
    · exact (T.le_sameStage_iff hr hp).mp
        (T.le_trans he ((T.pair_mem_boundedOrder _ _ _).mp hcp).2.2)
    · exact (T.le_sameStage_iff hr hq).mp
        (T.le_trans he ((T.pair_mem_boundedOrder _ _ _).mp hcq).2.2)
  · intro c hc
    have hr := T.reduceCondition_mem hc
    refine ⟨T.reduceCondition θ c, hr, ?_⟩
    rw [T.stageEmbedding_value hr]
    exact (T.pair_mem_boundedOrder _ _ _).mpr
      ⟨hmem _ hr, hc, (T.reduceCondition_equivalent hc).1⟩

end DefinableForcingTower
end ZFVP
