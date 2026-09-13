import ZFVP.SetTheory.ClassForcingTowerOrder

/-! Complete projections of the proper-class direct limit onto each set
stage. The lifting property is proved from the set-stage lifts and the
common-stage order, rather than postulated for the class forcing. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower

variable (T : DefinableForcingTower V)

noncomputable def projectCondition (i c : V) : V :=
  (T.projection i (i ∪ kpair.π₁ c)) ‘
    ((T.sectionMap (kpair.π₁ c) (i ∪ kpair.π₁ c)) ‘ (kpair.π₂ c))

instance projectCondition_definable : ℒₛₑₜ-function₂ T.projectCondition := by
  have := T.projection_definable
  have := T.section_definable
  unfold projectCondition
  definability

theorem projectCondition_mem {i c : V} [IsOrdinal i] (hc : T.Condition c) :
    T.projectCondition i c ∈ T.P i := by
  obtain ⟨j, q, hj, hq, rfl⟩ := hc
  let := hj
  have : IsOrdinal (i ∪ j) := ordinal_union_ordinal _ _
  simp only [projectCondition, kpair.π₁_kpair, kpair.π₂_kpair]
  exact T.projection_mem (subset_union_left _ _)
    (T.section_mem (subset_union_right _ _) hq)

theorem below_stage_iff {i c p : V} [IsOrdinal i]
    (hc : T.Condition c) (hp : p ∈ T.P i) :
    T.LE c ⟨i, p⟩ₖ ↔ ⟨T.projectCondition i c, p⟩ₖ ∈ T.R i := by
  obtain ⟨j, q, hj, hq, rfl⟩ := hc
  let := hj
  have : IsOrdinal (i ∪ j) := ordinal_union_ordinal _ _
  rw [T.le_pair_at_iff (subset_union_right i j) (subset_union_left i j) hq hp,
    T.below_section i (i ∪ j) inferInstance inferInstance (subset_union_left _ _)
      _ (T.section_mem (subset_union_right _ _) hq) p hp]
  simp only [projectCondition, kpair.π₁_kpair, kpair.π₂_kpair]

theorem below_projectCondition {i c : V} [IsOrdinal i] (hc : T.Condition c) :
    T.LE c ⟨i, T.projectCondition i c⟩ₖ :=
  (T.below_stage_iff hc (T.projectCondition_mem hc)).mpr
    ((T.order i inferInstance).2.1 _ (T.projectCondition_mem hc))

theorem projectCondition_order {i c d : V} [IsOrdinal i]
    (hcd : T.LE c d) :
    ⟨T.projectCondition i c, T.projectCondition i d⟩ₖ ∈ T.R i :=
  (T.below_stage_iff hcd.1 (T.projectCondition_mem hcd.2.1)).mp
    (T.le_trans hcd (T.below_projectCondition hcd.2.1))

theorem projectCondition_self {i p : V} [IsOrdinal i] (hp : p ∈ T.P i) :
    T.projectCondition i ⟨i, p⟩ₖ = p := by
  have hu : i ∪ i = i := by ext x; simp
  simp only [projectCondition, kpair.π₁_kpair, kpair.π₂_kpair, hu,
    T.section_self i inferInstance p hp, T.projection_self i inferInstance p hp]

theorem lift_stage_condition {i c q : V} [IsOrdinal i]
    (hc : T.Condition c) (hq : q ∈ T.P i)
    (hqc : ⟨q, T.projectCondition i c⟩ₖ ∈ T.R i) :
    ∃ d : V, T.Condition d ∧ T.LE d c ∧ T.LE d ⟨i, q⟩ₖ := by
  obtain ⟨j, p, hj, hp, rfl⟩ := hc
  let := hj
  have : IsOrdinal (i ∪ j) := ordinal_union_ordinal _ _
  have hpθ := T.section_mem (subset_union_right i j) hp
  simp only [projectCondition, kpair.π₁_kpair, kpair.π₂_kpair] at hqc
  obtain ⟨r, hr, hrp, hrq⟩ := T.lift i (i ∪ j) inferInstance inferInstance
    (subset_union_left _ _) _ hpθ q hq hqc
  have hd : T.Condition ⟨i ∪ j, r⟩ₖ := (T.condition_pair _ _).mpr ⟨inferInstance, hr⟩
  refine ⟨⟨i ∪ j, r⟩ₖ, hd, ?_, ?_⟩
  · apply (T.le_pair_at_iff (subset_refl (i ∪ j)) (subset_union_right _ _) hr hp).mpr
    rwa [T.section_self _ inferInstance r hr]
  · apply (T.le_pair_at_iff (subset_refl (i ∪ j)) (subset_union_left _ _) hr hq).mpr
    rw [T.section_self _ inferInstance r hr,
      T.below_section i (i ∪ j) inferInstance inferInstance (subset_union_left _ _) r hr q hq,
      hrq]
    exact (T.order i inferInstance).2.1 q hq

def DenseClass (D : V → Prop) : Prop :=
  (∀ c, D c → T.Condition c) ∧
    ∀ c, T.Condition c → ∃ d, D d ∧ T.LE d c

def stageDenseClass (i D c : V) : Prop :=
  T.Condition c ∧ ∃ p ∈ D, T.LE c ⟨i, p⟩ₖ

instance stageDenseClass_definable (i D : V) :
    ℒₛₑₜ-predicate (T.stageDenseClass i D) := by
  unfold stageDenseClass
  definability

theorem stageDenseClass_dense {i D : V} [IsOrdinal i]
    (hD : ForcingDense (T.P i) (T.R i) D) : T.DenseClass (T.stageDenseClass i D) := by
  refine ⟨fun c hc ↦ hc.1, fun c hc ↦ ?_⟩
  obtain ⟨p, hp, hpq⟩ := hD.2 _ (T.projectCondition_mem hc)
  obtain ⟨d, hd, hdc, hdp⟩ := T.lift_stage_condition hc (hD.1 p hp) hpq
  exact ⟨d, ⟨hd, p, hp, hdp⟩, hdc⟩

end DefinableForcingTower
end ZFVP
