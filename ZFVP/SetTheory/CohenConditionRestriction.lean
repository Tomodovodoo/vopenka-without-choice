import ZFVP.SetTheory.CohenAutomorphisms

/-! Restricting a Cohen condition to a set of row indices, and gluing two conditions
that agree on those rows. This is the condition-level toolkit behind Jech's Lemma 5.24
for the basic Cohen model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The part of a Cohen condition living on the rows indexed by `e`. -/
noncomputable def cohenRestrict (p e : V) : V := {z ∈ p ; kpair.π₁ (kpair.π₁ z) ∈ e}

instance cohenRestrict_definable : ℒₛₑₜ-function₂[V] cohenRestrict := by
  have h : ℒₛₑₜ-relation₃[V] (fun r p e ↦ ∀ z, z ∈ r ↔ z ∈ p ∧ kpair.π₁ (kpair.π₁ z) ∈ e) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cohenRestrict (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [cohenRestrict, mem_sep_iff]

theorem pair_mem_cohenRestrict (p e i n b : V) :
    ⟨⟨i, n⟩ₖ, b⟩ₖ ∈ cohenRestrict p e ↔ ⟨⟨i, n⟩ₖ, b⟩ₖ ∈ p ∧ i ∈ e := by
  simp only [cohenRestrict, mem_sep_iff, kpair.π₁_kpair]

theorem cohenRestrict_subset (p e : V) : cohenRestrict p e ⊆ p := by
  intro z hz
  exact (mem_sep_iff.mp hz).1

/-- Every element of a Cohen condition is a pair of a row-column pair with a bit. -/
theorem cohenCondition_mem_eq {I p z : V} (hp : p ∈ cohenConditions I) (hz : z ∈ p) :
    ∃ i ∈ I, ∃ n ∈ (ω : V), ∃ b ∈ (2 : V), z = ⟨⟨i, n⟩ₖ, b⟩ₖ := by
  have hsub := ((mem_finitePartialFunctions _ _ _).mp hp).1
  obtain ⟨u, hu, b, hb, rfl⟩ := mem_prod_iff.mp (hsub _ hz)
  obtain ⟨i, hi, n, hn, rfl⟩ := mem_prod_iff.mp hu
  exact ⟨i, hi, n, hn, b, hb, rfl⟩

theorem cohenRestrict_condition {I p e : V} (hp : p ∈ cohenConditions I) :
    cohenRestrict p e ∈ cohenConditions I :=
  finitePartialFunction_subset hp (cohenRestrict_subset p e)

theorem cohenRestrict_order {I p e : V} (hp : p ∈ cohenConditions I) :
    ⟨p, cohenRestrict p e⟩ₖ ∈ cohenOrder I :=
  (pair_mem_cohenOrder I p _).mpr ⟨hp, cohenRestrict_condition hp, cohenRestrict_subset p e⟩

theorem cohenSupport_cohenRestrict {I p e : V} (hp : p ∈ cohenConditions I) :
    cohenSupport (cohenRestrict p e) = cohenSupport p ∩ e := by
  have _ : p ∈ cohenConditions I := hp
  apply mem_ext
  intro i
  rw [mem_inter_iff, mem_cohenSupport, mem_cohenSupport]
  constructor
  · rintro ⟨n, b, hb⟩
    obtain ⟨hb, hie⟩ := (pair_mem_cohenRestrict p e i n b).mp hb
    exact ⟨⟨n, b, hb⟩, hie⟩
  · rintro ⟨⟨n, b, hb⟩, hie⟩
    exact ⟨n, b, (pair_mem_cohenRestrict p e i n b).mpr ⟨hb, hie⟩⟩

theorem cohenRestrict_of_support_subset {I p e : V} (hp : p ∈ cohenConditions I)
    (h : cohenSupport p ⊆ e) : cohenRestrict p e = p := by
  apply mem_ext
  intro z
  refine ⟨fun hz ↦ cohenRestrict_subset p e _ hz, fun hz ↦ ?_⟩
  obtain ⟨i, _, n, _, b, _, rfl⟩ := cohenCondition_mem_eq hp hz
  exact (pair_mem_cohenRestrict p e i n b).mpr ⟨hz, h _ ((mem_cohenSupport p i).mpr ⟨n, b, hz⟩)⟩

/-- Two conditions glue when the part of `p` on the rows of `e` sits inside `q` and the
rows of `q` outside `e` miss the rows of `p`. -/
theorem cohen_union_condition {I p q e : V} (hp : p ∈ cohenConditions I)
    (hq : q ∈ cohenConditions I) (hsub : cohenRestrict p e ⊆ q)
    (hdisj : ∀ i ∈ cohenSupport q, i ∉ e → i ∉ cohenSupport p) :
    p ∪ q ∈ cohenConditions I ∧ ⟨p ∪ q, p⟩ₖ ∈ cohenOrder I ∧ ⟨p ∪ q, q⟩ₖ ∈ cohenOrder I := by
  classical
  have hqf : IsFunction q := ((mem_finitePartialFunctions _ _ _).mp hq).2.1
  have hcompat : ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z := by
    intro x y z hxy hxz
    obtain ⟨i, _, n, _, b, _, he⟩ := cohenCondition_mem_eq hp hxy
    obtain ⟨hx, rfl⟩ := kpair_iff.mp he
    subst hx
    by_cases hie : i ∈ e
    · have hpe : ⟨⟨i, n⟩ₖ, y⟩ₖ ∈ q := hsub _ ((pair_mem_cohenRestrict p e i n y).mpr ⟨hxy, hie⟩)
      exact IsFunction.unique hpe hxz
    · exact absurd ((mem_cohenSupport p i).mpr ⟨n, y, hxy⟩)
        (hdisj i ((mem_cohenSupport q i).mpr ⟨n, z, hxz⟩) hie)
  have hu := finitePartialFunction_union hp hq hcompat
  exact ⟨hu,
    (pair_mem_cohenOrder I _ p).mpr ⟨hu, hp, fun z hz ↦ mem_union_iff.mpr (Or.inl hz)⟩,
    (pair_mem_cohenOrder I _ q).mpr ⟨hu, hq, fun z hz ↦ mem_union_iff.mpr (Or.inr hz)⟩⟩

theorem cohenConditionAction_cohenRestrict {I π p e : V} (hπ : IsInternalPermutation I π)
    (hp : p ∈ cohenConditions I) (he : ∀ i ∈ e, π ‘ i = i) :
    cohenRestrict (cohenConditionAction I π p) e = cohenConditionAction I π (cohenRestrict p e) := by
  have hpa : cohenConditionAction I π p ∈ cohenConditions I := cohenConditionAction_condition hπ hp
  have hr : cohenRestrict p e ∈ cohenConditions I := cohenRestrict_condition hp
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨hz', hze⟩ := mem_sep_iff.mp hz
    obtain ⟨x, _, n, _, b, _, rfl⟩ := cohenCondition_mem_eq hpa hz'
    rw [kpair.π₁_kpair, kpair.π₁_kpair] at hze
    obtain ⟨i, hip, rfl⟩ := (cohenConditionAction_pair_iff hp).mp hz'
    have hiI : i ∈ I := cohenSupport_subset hp _ ((mem_cohenSupport p i).mpr ⟨n, b, hip⟩)
    have hxI : π ‘ i ∈ I := function_value_mem hπ.1 hiI
    have hfix : π ‘ (π ‘ i) = π ‘ i := he _ hze
    have : i = π ‘ i := by
      have h1 := hπ.inv_value hiI
      have h2 := hπ.inv_value hxI
      rw [hfix] at h2
      exact h1.symm.trans h2
    rw [← this] at hze
    exact (cohenConditionAction_pair_iff hr).mpr
      ⟨i, (pair_mem_cohenRestrict p e i n b).mpr ⟨hip, hze⟩, rfl⟩
  · intro hz
    obtain ⟨x, _, n, _, b, _, rfl⟩ :=
      cohenCondition_mem_eq (cohenConditionAction_condition hπ hr) hz
    obtain ⟨i, hi, rfl⟩ := (cohenConditionAction_pair_iff hr).mp hz
    obtain ⟨hip, hie⟩ := (pair_mem_cohenRestrict p e i n b).mp hi
    have hfix : π ‘ i = i := he _ hie
    refine mem_sep_iff.mpr ⟨cohenConditionAction_pair hp hip, ?_⟩
    rw [kpair.π₁_kpair, kpair.π₁_kpair, hfix]
    exact hie

end ZFVP
