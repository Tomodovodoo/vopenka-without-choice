import ZFVP.SetTheory.RealMeasurableAlgebra

/-! Splitting genuine intervals at a rational point, with one positive padding cost. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Classical

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realSplitLeft (p q e : V) : V :=
  if ¬ InternalRationalLT q (kpair.π₂ p) then p else
  if ¬ InternalRationalLT (kpair.π₁ p) q then ⟨rationalZero V, e⟩ₖ else
    ⟨kpair.π₁ p, rationalAdd q e⟩ₖ

noncomputable def realSplitRight (p q e : V) : V :=
  if ¬ InternalRationalLT q (kpair.π₂ p) then ⟨rationalZero V, e⟩ₖ else
  if ¬ InternalRationalLT (kpair.π₁ p) q then p else ⟨q, kpair.π₂ p⟩ₖ

instance realSplitLeft_definable : ℒₛₑₜ-function₃[V] realSplitLeft := by
  have h : ℒₛₑₜ-relation₄ (fun w p q e : V ↦
    (¬ InternalRationalLT q (kpair.π₂ p) ∧ w = p) ∨
    (InternalRationalLT q (kpair.π₂ p) ∧ ¬ InternalRationalLT (kpair.π₁ p) q ∧ w = ⟨rationalZero V, e⟩ₖ) ∨
    (InternalRationalLT q (kpair.π₂ p) ∧ InternalRationalLT (kpair.π₁ p) q ∧ w = ⟨kpair.π₁ p, rationalAdd q e⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  simp only [realSplitLeft]
  split_ifs <;> simp_all

instance realSplitRight_definable : ℒₛₑₜ-function₃[V] realSplitRight := by
  have h : ℒₛₑₜ-relation₄ (fun w p q e : V ↦
    (¬ InternalRationalLT q (kpair.π₂ p) ∧ w = ⟨rationalZero V, e⟩ₖ) ∨
    (InternalRationalLT q (kpair.π₂ p) ∧ ¬ InternalRationalLT (kpair.π₁ p) q ∧ w = p) ∨
    (InternalRationalLT q (kpair.π₂ p) ∧ InternalRationalLT (kpair.π₁ p) q ∧ w = ⟨q, kpair.π₂ p⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  simp only [realSplitRight]
  split_ifs <;> simp_all

theorem realSplit_codes {p : V} (hp : p ∈ realBasicCodes V)
    (q e : InternalRational V) (he : 0 < e) :
    realSplitLeft p q.val e.val ∈ realBasicCodes V ∧
    realSplitRight p q.val e.val ∈ realBasicCodes V := by
  have hfill : (⟨rationalZero V, e.val⟩ₖ : V) ∈ realBasicCodes V :=
    (pair_mem_realBasicCodes_iff _ _).mpr ⟨rationalZero_mem, e.property, he⟩
  obtain ⟨hpp, _⟩ := (mem_realBasicCodes_iff _).mp hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hpp
  simp only [realSplitLeft, realSplitRight, kpair.π₁_kpair, kpair.π₂_kpair]
  by_cases hqb : InternalRationalLT q.val b
  · by_cases haq : InternalRationalLT a q.val
    · simp only [hqb, haq, not_true_eq_false, ite_false]
      have haq' : (⟨a, ha⟩ : InternalRational V) < q := haq
      have hqb' : q < (⟨b, hb⟩ : InternalRational V) := hqb
      exact ⟨(pair_mem_realBasicCodes_iff _ _).mpr ⟨ha, (q + e).property,
        lt_trans haq' (lt_add_of_pos_right q he)⟩,
        (pair_mem_realBasicCodes_iff _ _).mpr ⟨q.property, hb, hqb'⟩⟩
    · simpa only [hqb, haq, not_true_eq_false, not_false_eq_true, ite_false, ite_true] using And.intro hfill hp
  · simpa only [hqb, not_false_eq_true, ite_true] using And.intro hp hfill

theorem realSplit_length_sum {p : V} (hp : p ∈ realBasicCodes V)
    (q e : InternalRational V) :
    rationalAdd (realIntervalLength (realSplitLeft p q.val e.val))
      (realIntervalLength (realSplitRight p q.val e.val)) = rationalAdd (realIntervalLength p) e.val := by
  obtain ⟨hpp, _⟩ := (mem_realBasicCodes_iff _).mp hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hpp
  let s : InternalRational V := ⟨a, ha⟩
  let t : InternalRational V := ⟨b, hb⟩
  simp only [realSplitLeft, realSplitRight, kpair.π₁_kpair, kpair.π₂_kpair]
  by_cases hqb : InternalRationalLT q.val b
  · by_cases haq : InternalRationalLT a q.val
    · simp only [hqb, haq, not_true_eq_false, ite_false, realIntervalLength, kpair.π₁_kpair, kpair.π₂_kpair]
      exact congrArg Subtype.val (show (q + e - s) + (t - q) = (t - s) + e from by ring)
    · simp only [hqb, haq, not_true_eq_false, not_false_eq_true, ite_false, ite_true, realIntervalLength, kpair.π₁_kpair, kpair.π₂_kpair]
      exact congrArg Subtype.val (show (e - 0) + (t - s) = (t - s) + e from by ring)
  · simp only [hqb, not_false_eq_true, ite_true, realIntervalLength, kpair.π₁_kpair, kpair.π₂_kpair]
    exact congrArg Subtype.val (show (t - s) + (e - 0) = (t - s) + e from by ring)

theorem realSplitLeft_covers {p x : V} (hp : p ∈ realBasicCodes V)
    (q e : InternalRational V) (he : 0 < e)
    (hx : x ∈ realInterval (kpair.π₁ p) (kpair.π₂ p)) (hxq : x ⊆ rationalCut q.val) :
    x ∈ realInterval (kpair.π₁ (realSplitLeft p q.val e.val))
      (kpair.π₂ (realSplitLeft p q.val e.val)) := by
  obtain ⟨hpp, _⟩ := (mem_realBasicCodes_iff _).mp hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hpp
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hx
  obtain ⟨hxCut, hax, hxb⟩ := (mem_realInterval_iff _ _ _).mp hx
  by_cases hqb : InternalRationalLT q.val b
  · by_cases haq : InternalRationalLT a q.val
    · simp only [realSplitLeft, kpair.π₁_kpair, kpair.π₂_kpair, hqb, haq, not_true_eq_false, ite_false]
      exact (mem_realInterval_iff _ _ _).mpr ⟨hxCut, hax,
        dedekindLT_of_subset_of_lt hxq ((rationalCut_lt_iff q.property (q + e).property).mpr
          (lt_add_of_pos_right q he))⟩
    · have hqa : rationalCut q.val ⊆ rationalCut a :=
        InternalRational.rationalCut_mono (show q ≤ (⟨a, ha⟩ : InternalRational V) from haq)
      exact (hax.2 (subset_antisymm hax.1 (subset_trans hxq hqa))).elim
  · simpa only [realSplitLeft, kpair.π₁_kpair, kpair.π₂_kpair, hqb, not_false_eq_true, ite_true]
      using (mem_realInterval_iff a b x).mpr ⟨hxCut, hax, hxb⟩

theorem realSplitRight_covers {p x : V} (hp : p ∈ realBasicCodes V)
    (q e : InternalRational V)
    (hx : x ∈ realInterval (kpair.π₁ p) (kpair.π₂ p)) (hqx : DedekindLT (rationalCut q.val) x) :
    x ∈ realInterval (kpair.π₁ (realSplitRight p q.val e.val))
      (kpair.π₂ (realSplitRight p q.val e.val)) := by
  obtain ⟨hpp, _⟩ := (mem_realBasicCodes_iff _).mp hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hpp
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hx
  obtain ⟨hxCut, hax, hxb⟩ := (mem_realInterval_iff _ _ _).mp hx
  by_cases hqb : InternalRationalLT q.val b
  · by_cases haq : InternalRationalLT a q.val
    · simp only [realSplitRight, kpair.π₁_kpair, kpair.π₂_kpair, hqb, haq, not_true_eq_false, ite_false]
      exact (mem_realInterval_iff _ _ _).mpr ⟨hxCut, hqx, hxb⟩
    · simpa only [realSplitRight, kpair.π₁_kpair, kpair.π₂_kpair, hqb, haq,
        not_true_eq_false, not_false_eq_true, ite_false, ite_true]
        using (mem_realInterval_iff a b x).mpr ⟨hxCut, hax, hxb⟩
  · have hbq : rationalCut b ⊆ rationalCut q.val :=
      InternalRational.rationalCut_mono (show (⟨b, hb⟩ : InternalRational V) ≤ q from hqb)
    exact (hqx.2 (subset_antisymm hqx.1 (subset_trans hxb.1 hbq))).elim

end ZFVP
