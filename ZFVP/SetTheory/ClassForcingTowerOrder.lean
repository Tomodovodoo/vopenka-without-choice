import ZFVP.SetTheory.ClassForcingTower

/-! The direct limit of a definable forcing tower. Conditions are tagged
by their set stage. Compare two conditions by moving them to a common
later stage. The comparison is independent of the chosen common stage. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower

variable (T : DefinableForcingTower V)

def Condition (c : V) : Prop :=
  ∃ i p : V, IsOrdinal i ∧ p ∈ T.P i ∧ c = ⟨i, p⟩ₖ

instance condition_definable : ℒₛₑₜ-predicate T.Condition := by
  have := T.P_definable
  unfold Condition
  definability

theorem condition_pair (i p : V) :
    T.Condition ⟨i, p⟩ₖ ↔ IsOrdinal i ∧ p ∈ T.P i := by
  constructor
  · rintro ⟨j, q, hj, hq, he⟩
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨hj, hq⟩
  · rintro ⟨hi, hp⟩
    exact ⟨i, p, hi, hp, rfl⟩

theorem condition_spec {c : V} (hc : T.Condition c) :
    IsOrdinal (kpair.π₁ c) ∧ kpair.π₂ c ∈ T.P (kpair.π₁ c) ∧
      c = ⟨kpair.π₁ c, kpair.π₂ c⟩ₖ := by
  obtain ⟨i, p, hi, hp, rfl⟩ := hc
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  exact ⟨hi, hp, True.intro⟩

def LE (c d : V) : Prop :=
  T.Condition c ∧ T.Condition d ∧ ∃ θ : V, IsOrdinal θ ∧
    kpair.π₁ c ⊆ θ ∧ kpair.π₁ d ⊆ θ ∧
    ⟨(T.sectionMap (kpair.π₁ c) θ) ‘ (kpair.π₂ c),
      (T.sectionMap (kpair.π₁ d) θ) ‘ (kpair.π₂ d)⟩ₖ ∈ T.R θ

instance le_definable : ℒₛₑₜ-relation T.LE := by
  have := T.section_definable
  have := T.R_definable
  unfold LE
  definability

theorem le_pair_iff {i j p q : V} [IsOrdinal i] [IsOrdinal j]
    (hp : p ∈ T.P i) (hq : q ∈ T.P j) :
    T.LE ⟨i, p⟩ₖ ⟨j, q⟩ₖ ↔ ∃ θ : V, IsOrdinal θ ∧ i ⊆ θ ∧ j ⊆ θ ∧
      ⟨(T.sectionMap i θ) ‘ p, (T.sectionMap j θ) ‘ q⟩ₖ ∈ T.R θ := by
  simp only [LE, condition_pair, kpair.π₁_kpair, kpair.π₂_kpair,
    show IsOrdinal i from inferInstance, show IsOrdinal j from inferInstance, hp, hq, true_and]

theorem comparison_raise {i j θ η p q : V}
    [IsOrdinal i] [IsOrdinal j] [IsOrdinal θ] [IsOrdinal η]
    (hiθ : i ⊆ θ) (hjθ : j ⊆ θ) (hθη : θ ⊆ η)
    (hp : p ∈ T.P i) (hq : q ∈ T.P j)
    (h : ⟨(T.sectionMap i θ) ‘ p, (T.sectionMap j θ) ‘ q⟩ₖ ∈ T.R θ) :
    ⟨(T.sectionMap i η) ‘ p, (T.sectionMap j η) ‘ q⟩ₖ ∈ T.R η := by
  have hh := (T.section_order_iff hθη (T.section_mem hiθ hp) (T.section_mem hjθ hq)).mpr h
  simpa only [T.section_comp i θ η inferInstance inferInstance inferInstance hiθ hθη p hp,
    T.section_comp j θ η inferInstance inferInstance inferInstance hjθ hθη q hq] using hh

theorem comparison_lower {i j θ η p q : V}
    [IsOrdinal i] [IsOrdinal j] [IsOrdinal θ] [IsOrdinal η]
    (hiθ : i ⊆ θ) (hjθ : j ⊆ θ) (hθη : θ ⊆ η)
    (hp : p ∈ T.P i) (hq : q ∈ T.P j)
    (h : ⟨(T.sectionMap i η) ‘ p, (T.sectionMap j η) ‘ q⟩ₖ ∈ T.R η) :
    ⟨(T.sectionMap i θ) ‘ p, (T.sectionMap j θ) ‘ q⟩ₖ ∈ T.R θ := by
  apply (T.section_order_iff hθη (T.section_mem hiθ hp) (T.section_mem hjθ hq)).mp
  simpa only [T.section_comp i θ η inferInstance inferInstance inferInstance hiθ hθη p hp,
    T.section_comp j θ η inferInstance inferInstance inferInstance hjθ hθη q hq] using h

theorem le_pair_at_iff {i j θ p q : V} [IsOrdinal i] [IsOrdinal j] [IsOrdinal θ]
    (hiθ : i ⊆ θ) (hjθ : j ⊆ θ) (hp : p ∈ T.P i) (hq : q ∈ T.P j) :
    T.LE ⟨i, p⟩ₖ ⟨j, q⟩ₖ ↔
      ⟨(T.sectionMap i θ) ‘ p, (T.sectionMap j θ) ‘ q⟩ₖ ∈ T.R θ := by
  rw [T.le_pair_iff hp hq]
  constructor
  · rintro ⟨η, hη, hiη, hjη, h⟩
    let := hη
    have : IsOrdinal (θ ∪ η) := ordinal_union_ordinal _ _
    exact T.comparison_lower hiθ hjθ (subset_union_left _ _) hp hq
      (T.comparison_raise hiη hjη (subset_union_right _ _) hp hq h)
  · intro h
    exact ⟨θ, inferInstance, hiθ, hjθ, h⟩

theorem le_sameStage_iff {i p q : V} [IsOrdinal i]
    (hp : p ∈ T.P i) (hq : q ∈ T.P i) :
    T.LE ⟨i, p⟩ₖ ⟨i, q⟩ₖ ↔ ⟨p, q⟩ₖ ∈ T.R i := by
  rw [T.le_pair_at_iff (subset_refl i) (subset_refl i) hp hq,
    T.section_self i inferInstance p hp, T.section_self i inferInstance q hq]

theorem le_refl {c : V} (hc : T.Condition c) : T.LE c c := by
  obtain ⟨i, p, hi, hp, rfl⟩ := hc
  let := hi
  exact (T.le_sameStage_iff hp hp).mpr ((T.order i hi).2.1 p hp)

theorem le_trans {c d e : V} (hcd : T.LE c d) (hde : T.LE d e) : T.LE c e := by
  obtain ⟨i, p, hi, hp, rfl⟩ := hcd.1
  obtain ⟨j, q, hj, hq, rfl⟩ := hcd.2.1
  obtain ⟨k, r, hk, hr, rfl⟩ := hde.2.1
  let := hi
  let := hj
  let := hk
  obtain ⟨θ, hθ, hiθ, hjθ, hpq⟩ := (T.le_pair_iff hp hq).mp hcd
  obtain ⟨η, hη, hjη, hkη, hqr⟩ := (T.le_pair_iff hq hr).mp hde
  let := hθ
  let := hη
  have : IsOrdinal (θ ∪ η) := ordinal_union_ordinal _ _
  have hiu : i ⊆ θ ∪ η := subset_trans hiθ (subset_union_left _ _)
  have hju : j ⊆ θ ∪ η := subset_trans hjθ (subset_union_left _ _)
  have hku : k ⊆ θ ∪ η := subset_trans hkη (subset_union_right _ _)
  apply (T.le_pair_at_iff hiu hku hp hr).mpr
  exact (T.order (θ ∪ η) inferInstance).2.2 _ (T.section_mem hiu hp)
    _ (T.section_mem hju hq) _ (T.section_mem hku hr)
    (T.comparison_raise hiθ hjθ (subset_union_left _ _) hp hq hpq)
    (T.comparison_raise hjη hkη (subset_union_right _ _) hq hr hqr)

noncomputable def one : V := ⟨(∅ : V), T.top ∅⟩ₖ

theorem one_condition : T.Condition T.one :=
  (T.condition_pair _ _).mpr ⟨inferInstance, (T.top_spec ∅ inferInstance).1⟩

theorem le_one {c : V} (hc : T.Condition c) : T.LE c T.one := by
  obtain ⟨i, p, hi, hp, rfl⟩ := hc
  let := hi
  have ht := T.top_spec ∅ inferInstance
  apply (T.le_pair_at_iff (subset_refl i) (empty_subset i) hp ht.1).mpr
  rw [T.section_self i hi p hp, T.section_top ∅ i inferInstance hi (empty_subset i)]
  exact (T.top_spec i hi).2 p hp

theorem section_equivalent {i j p : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) (hp : p ∈ T.P i) :
    T.LE ⟨i, p⟩ₖ ⟨j, (T.sectionMap i j) ‘ p⟩ₖ ∧
      T.LE ⟨j, (T.sectionMap i j) ‘ p⟩ₖ ⟨i, p⟩ₖ := by
  have he := T.section_mem hij hp
  have hr := (T.order j inferInstance).2.1 _ he
  constructor
  · apply (T.le_pair_at_iff hij (subset_refl j) hp he).mpr
    rwa [T.section_self j inferInstance _ he]
  · apply (T.le_pair_at_iff (subset_refl j) hij he hp).mpr
    rwa [T.section_self j inferInstance _ he]

end DefinableForcingTower
end ZFVP
