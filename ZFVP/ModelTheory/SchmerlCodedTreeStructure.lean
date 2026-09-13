import ZFVP.ModelTheory.SchmerlCodedInterpretations

/-! Order and rank facts for the actual interpreted tree. The proofs use
standard ZF truth of the represented model, without well-foundedness. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)

theorem ordinalOrder_poset : IsForcingPoset (codedOrdinals R.code) (codedOrdinalOrder R.code) := by
  refine ⟨⟨codedBinaryOn_subset _ _ _ _, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨α, rfl⟩ := (R.mem_ordinals_iff p).mp hp
    exact (R.ordinalOrder_iff α α).mpr le_rfl
  · intro p hp q hq r hr hpq hqr
    obtain ⟨α, rfl⟩ := (R.mem_ordinals_iff p).mp hp
    obtain ⟨β, rfl⟩ := (R.mem_ordinals_iff q).mp hq
    obtain ⟨γ, rfl⟩ := (R.mem_ordinals_iff r).mp hr
    exact (R.ordinalOrder_iff α γ).mpr (((R.ordinalOrder_iff α β).mp hpq).trans ((R.ordinalOrder_iff β γ).mp hqr))
  · intro p hp q hq hpq hqp
    obtain ⟨α, rfl⟩ := (R.mem_ordinals_iff p).mp hp
    obtain ⟨β, rfl⟩ := (R.mem_ordinals_iff q).mp hq
    exact congrArg (fun a : SetTheory.Ordinal W ↦ (R.equiv a.val).val)
      (le_antisymm ((R.ordinalOrder_iff α β).mp hpq) ((R.ordinalOrder_iff β α).mp hqp))

theorem ordinalOrder_total {p q : V} (hp : p ∈ codedOrdinals R.code) (hq : q ∈ codedOrdinals R.code) :
    ⟨p, q⟩ₖ ∈ codedOrdinalOrder R.code ∨ ⟨q, p⟩ₖ ∈ codedOrdinalOrder R.code := by
  obtain ⟨α, rfl⟩ := (R.mem_ordinals_iff p).mp hp
  obtain ⟨β, rfl⟩ := (R.mem_ordinals_iff q).mp hq
  exact (le_total α β).imp (R.ordinalOrder_iff α β).mpr (R.ordinalOrder_iff β α).mpr

theorem ordinals_directedNoMax : IsInternalDirectedNoMax (codedOrdinals R.code) (codedOrdinalOrder R.code) := by
  refine ⟨⟨(R.equiv (∅ : W)).val, R.ordinal_mem ⟨∅, inferInstance⟩⟩, ?_, ?_⟩
  · intro p hp q hq
    rcases R.ordinalOrder_total hp hq with hpq | hqp
    · exact ⟨q, hq, hpq, R.ordinalOrder_poset.1.2.1 q hq⟩
    · exact ⟨p, hp, R.ordinalOrder_poset.1.2.1 p hp, hqp⟩
  · rintro ⟨p, hp, hmax⟩
    obtain ⟨α, rfl⟩ := (R.mem_ordinals_iff p).mp hp
    let : IsOrdinal α.val := α.ordinal
    let β : SetTheory.Ordinal W := ⟨succ α.val, inferInstance⟩
    have hle := (R.ordinalOrder_iff β α).mp (hmax _ (R.ordinal_mem β))
    exact mem_irrefl α.val (hle α.val (mem_succ_self α.val))

theorem classOrder_poset : IsForcingPoset (codedClassNodes R.code) (codedClassOrder R.code) := by
  refine ⟨⟨codedBinaryOn_subset _ _ _ _, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨t, rfl⟩ := (R.mem_classNodes_iff p).mp hp
    exact (R.classOrder_iff t t).mpr le_rfl
  · intro p hp q hq r hr hpq hqr
    obtain ⟨s, rfl⟩ := (R.mem_classNodes_iff p).mp hp
    obtain ⟨t, rfl⟩ := (R.mem_classNodes_iff q).mp hq
    obtain ⟨u, rfl⟩ := (R.mem_classNodes_iff r).mp hr
    exact (R.classOrder_iff s u).mpr (((R.classOrder_iff s t).mp hpq).trans ((R.classOrder_iff t u).mp hqr))
  · intro p hp q hq hpq hqp
    obtain ⟨s, rfl⟩ := (R.mem_classNodes_iff p).mp hp
    obtain ⟨t, rfl⟩ := (R.mem_classNodes_iff q).mp hq
    exact congrArg (fun u : ClassTreeNode W ↦ (R.equiv u.code).val)
      (le_antisymm ((R.classOrder_iff s t).mp hpq) ((R.classOrder_iff t s).mp hqp))

theorem classOrder_below_linear {p q r : V}
    (hp : p ∈ codedClassNodes R.code) (hq : q ∈ codedClassNodes R.code) (hr : r ∈ codedClassNodes R.code)
    (hpr : ⟨p, r⟩ₖ ∈ codedClassOrder R.code) (hqr : ⟨q, r⟩ₖ ∈ codedClassOrder R.code) :
    ⟨p, q⟩ₖ ∈ codedClassOrder R.code ∨ ⟨q, p⟩ₖ ∈ codedClassOrder R.code := by
  obtain ⟨s, rfl⟩ := (R.mem_classNodes_iff p).mp hp
  obtain ⟨t, rfl⟩ := (R.mem_classNodes_iff q).mp hq
  obtain ⟨u, rfl⟩ := (R.mem_classNodes_iff r).mp hr
  exact (ClassTreeNode.tree ((R.classOrder_iff s u).mp hpr) ((R.classOrder_iff t u).mp hqr)).imp
    (R.classOrder_iff s t).mpr (R.classOrder_iff t s).mpr

theorem classLevels_function : codedClassLevels R.code ∈ codedOrdinals R.code ^ codedClassNodes R.code := by
  apply mem_function_iff.mpr
  refine ⟨codedBinaryOn_subset _ _ _ _, ?_⟩
  intro p hp
  obtain ⟨t, rfl⟩ := (R.mem_classNodes_iff p).mp hp
  refine ⟨(R.equiv t.level.val).val, (R.classLevels_iff t t.level).mpr rfl, ?_⟩
  intro q hq
  have hqO := ((pair_mem_codedBinaryOn _ _ _ _ _ _).mp hq).2.1
  obtain ⟨α, rfl⟩ := (R.mem_ordinals_iff q).mp hqO
  exact congrArg (fun a : SetTheory.Ordinal W ↦ (R.equiv a.val).val) ((R.classLevels_iff t α).mp hq)

theorem classLevels_value (t : ClassTreeNode W) :
    (codedClassLevels R.code) ‘ (R.equiv t.code).val = (R.equiv t.level.val).val := by
  let : IsFunction (codedClassLevels R.code) := IsFunction.of_mem R.classLevels_function
  exact value_eq_of_kpair_mem ((R.classLevels_iff t t.level).mpr rfl)

theorem classLevels_onto {a : V} (ha : a ∈ codedOrdinals R.code) :
    ∃ p ∈ codedClassNodes R.code, (codedClassLevels R.code) ‘ p = a := by
  obtain ⟨α, rfl⟩ := (R.mem_ordinals_iff a).mp ha
  let t : ClassTreeNode W := ⟨α, ∅, empty_subset _⟩
  exact ⟨(R.equiv t.code).val, R.classNode_mem t, R.classLevels_value t⟩

theorem classLevels_monotone {p q : V} (hp : p ∈ codedClassNodes R.code) (hq : q ∈ codedClassNodes R.code)
    (hpq : ⟨p, q⟩ₖ ∈ codedClassOrder R.code) :
    ⟨(codedClassLevels R.code) ‘ p, (codedClassLevels R.code) ‘ q⟩ₖ ∈ codedOrdinalOrder R.code := by
  obtain ⟨s, rfl⟩ := (R.mem_classNodes_iff p).mp hp
  obtain ⟨t, rfl⟩ := (R.mem_classNodes_iff q).mp hq
  rw [R.classLevels_value, R.classLevels_value]
  exact (R.ordinalOrder_iff s.level t.level).mpr ((R.classOrder_iff s t).mp hpq).1

theorem classLevels_comparable_injective {p q : V}
    (hp : p ∈ codedClassNodes R.code) (hq : q ∈ codedClassNodes R.code)
    (hpq : ⟨p, q⟩ₖ ∈ codedClassOrder R.code)
    (he : (codedClassLevels R.code) ‘ p = (codedClassLevels R.code) ‘ q) : p = q := by
  obtain ⟨s, rfl⟩ := (R.mem_classNodes_iff p).mp hp
  obtain ⟨t, rfl⟩ := (R.mem_classNodes_iff q).mp hq
  rw [R.classLevels_value, R.classLevels_value] at he
  have hl : s.level = t.level := SetTheory.Ordinal.ext (R.equiv.injective (Subtype.ext he))
  have hst := (R.classOrder_iff s t).mp hpq
  have hts : t ≤ s := ClassTreeNode.le_of_common_above le_rfl hst hl.ge
  exact congrArg (fun u : ClassTreeNode W ↦ (R.equiv u.code).val) (le_antisymm hst hts)

theorem classLevels_predecessor {p a : V} (hp : p ∈ codedClassNodes R.code) (ha : a ∈ codedOrdinals R.code)
    (hap : ⟨a, (codedClassLevels R.code) ‘ p⟩ₖ ∈ codedOrdinalOrder R.code) :
    ∃ q ∈ codedClassNodes R.code, ⟨q, p⟩ₖ ∈ codedClassOrder R.code ∧ (codedClassLevels R.code) ‘ q = a := by
  obtain ⟨t, rfl⟩ := (R.mem_classNodes_iff p).mp hp
  obtain ⟨α, rfl⟩ := (R.mem_ordinals_iff a).mp ha
  rw [R.classLevels_value] at hap
  refine ⟨(R.equiv (t.atLevel α).code).val, R.classNode_mem _,
    (R.classOrder_iff _ _).mpr (t.atLevel_le ((R.ordinalOrder_iff α t.level).mp hap)), ?_⟩
  exact R.classLevels_value _

end ZFVP.BinaryRelationRepresentation
