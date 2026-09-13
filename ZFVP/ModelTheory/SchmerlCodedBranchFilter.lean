import ZFVP.ModelTheory.SchmerlCodedBranchSequence

/-! A full-tree maximally compatible filter reconstructed from a selected
cofinal branch. The Rubin clause applies to this full definable poset. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedBranchFilter (M B : V) : V :=
  {x ∈ codedClassNodes M ; ∃ y ∈ B, ⟨x, y⟩ₖ ∈ codedClassOrder M}

theorem mem_codedBranchFilter (M B x : V) :
    x ∈ codedBranchFilter M B ↔ x ∈ codedClassNodes M ∧ ∃ y ∈ B, ⟨x, y⟩ₖ ∈ codedClassOrder M := mem_sep_iff

instance codedBranchFilter_definable : ℒₛₑₜ-function₂[V] codedBranchFilter := by
  have h : ℒₛₑₜ-relation₃[V] (fun F M B ↦ ∀ x, x ∈ F ↔
      x ∈ codedClassNodes M ∧ ∃ y ∈ B, ⟨x, y⟩ₖ ∈ codedClassOrder M) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_codedBranchFilter]
  rfl

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)

theorem classOrder_of_common_above_of_levels {p q z : V}
    (hp : p ∈ codedClassNodes R.code) (hq : q ∈ codedClassNodes R.code) (hz : z ∈ codedClassNodes R.code)
    (hpz : ⟨p, z⟩ₖ ∈ codedClassOrder R.code) (hqz : ⟨q, z⟩ₖ ∈ codedClassOrder R.code)
    (hr : ⟨(codedClassLevels R.code) ‘ p, (codedClassLevels R.code) ‘ q⟩ₖ ∈ codedOrdinalOrder R.code) :
    ⟨p, q⟩ₖ ∈ codedClassOrder R.code := by
  obtain ⟨s, rfl⟩ := (R.mem_classNodes_iff p).mp hp
  obtain ⟨t, rfl⟩ := (R.mem_classNodes_iff q).mp hq
  obtain ⟨u, rfl⟩ := (R.mem_classNodes_iff z).mp hz
  rw [R.classLevels_value, R.classLevels_value, R.ordinalOrder_iff] at hr
  exact (R.classOrder_iff s t).mpr (ClassTreeNode.le_of_common_above
    ((R.classOrder_iff s u).mp hpz) ((R.classOrder_iff t u).mp hqz) hr)

variable {κ c B : V} [IsOrdinal κ]
variable (hc : IsInternalCofinalStrictChain κ (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
variable (hB : IsInternalCofinalBranch (codedSelectedClassNodes R.code κ c)
  (codedSelectedClassOrder R.code κ c) κ (codedSelectedClassRank R.code κ c) B)

include hB

omit [IsOrdinal κ] in
theorem selectedBranch_subset_filter : B ⊆ codedBranchFilter R.code B := by
  intro x hx
  have hxT := ((mem_codedSelectedClassNodes _ _ _ _).mp (hB.1 x hx)).1
  exact (mem_codedBranchFilter _ _ _).mpr ⟨hxT, x, hx, R.classOrder_poset.1.2.1 x hxT⟩

omit [IsOrdinal κ] in
theorem codedBranchFilter_recovers :
    codedBranchFilter R.code B ∩ codedSelectedClassNodes R.code κ c = B := by
  apply mem_ext
  intro x
  rw [mem_inter_iff]
  constructor
  · rintro ⟨hF, hx⟩
    obtain ⟨_, y, hy, hxy⟩ := (mem_codedBranchFilter _ _ _).mp hF
    exact hB.2.2.2 x hx y hy ((pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr ⟨hxy, hx, hB.1 y hy⟩)
  · intro hx
    exact ⟨R.selectedBranch_subset_filter hB x hx, hB.1 x hx⟩

omit [IsOrdinal κ] in
theorem codedBranchFilter_directed {x y : V} (hx : x ∈ codedBranchFilter R.code B)
    (hy : y ∈ codedBranchFilter R.code B) :
    ∃ z ∈ codedBranchFilter R.code B, ⟨x, z⟩ₖ ∈ codedClassOrder R.code ∧ ⟨y, z⟩ₖ ∈ codedClassOrder R.code := by
  obtain ⟨hxT, b, hb, hxb⟩ := (mem_codedBranchFilter _ _ _).mp hx
  obtain ⟨hyT, d, hd, hyd⟩ := (mem_codedBranchFilter _ _ _).mp hy
  have hbT := ((mem_codedSelectedClassNodes _ _ _ _).mp (hB.1 b hb)).1
  have hdT := ((mem_codedSelectedClassNodes _ _ _ _).mp (hB.1 d hd)).1
  rcases hB.2.1 b hb d hd with hbd | hdb
  · exact ⟨d, R.selectedBranch_subset_filter hB d hd,
      R.classOrder_poset.1.2.2 x hxT b hbT d hdT hxb (mem_inter_iff.mp hbd).1, hyd⟩
  · exact ⟨b, R.selectedBranch_subset_filter hB b hb, hxb,
      R.classOrder_poset.1.2.2 y hyT d hdT b hbT hyd (mem_inter_iff.mp hdb).1⟩

include hc

theorem codedBranchFilter_maximallyCompatible :
    IsInternalMaximallyCompatible (codedClassNodes R.code) (codedClassOrder R.code) (codedBranchFilter R.code B) := by
  refine ⟨fun x hx ↦ ((mem_codedBranchFilter _ _ _).mp hx).1,
    fun _ hx _ hy ↦ R.codedBranchFilter_directed hB hx hy, ?_⟩
  intro q hq hcompatible
  have hqO := function_value_mem R.classLevels_function hq
  obtain ⟨i, hi, hqi⟩ := hc.2.2 _ hqO
  obtain ⟨b, hb, hbrank⟩ := R.selectedBranch_node_at_rank hc hB hi
  obtain ⟨z, hz, hbz, hqz⟩ := hcompatible b (R.selectedBranch_subset_filter hB b hb)
  have hbT := ((mem_codedSelectedClassNodes _ _ _ _).mp (hB.1 b hb)).1
  have hblevel := (codedSelectedClassRank_spec hc (hB.1 b hb)).2
  rw [hbrank] at hblevel
  have hqb := R.classOrder_of_common_above_of_levels hq hbT hz hqz hbz (hblevel.symm ▸ hqi)
  exact (mem_codedBranchFilter _ _ _).mpr ⟨hq, b, hb, hqb⟩

theorem codedBranchFilter_cofinalChain :
    IsInternalCofinalStrictChain κ (codedBranchFilter R.code B) (codedClassOrder R.code)
      (codedBranchSequence R.code κ c B) := by
  refine ⟨mem_function_of_mem_function_of_subset (R.codedBranchSequence_function hc hB)
    (R.selectedBranch_subset_filter hB), ?_, ?_⟩
  · exact fun _ hi _ hj hij ↦ R.codedBranchSequence_strict hc hB hi hj hij
  · intro x hx
    obtain ⟨_, b, hb, hxb⟩ := (mem_codedBranchFilter _ _ _).mp hx
    refine ⟨(codedSelectedClassRank R.code κ c) ‘ b, (codedSelectedClassRank_spec hc (hB.1 b hb)).1, ?_⟩
    rw [R.codedBranchSequence_recovers hc hB hb]
    exact hxb

theorem codedBranchFilter_isCodedDefinable (hRubin : IsCodedRubin R.code κ) :
    IsCodedDefinableSet R.code (codedBranchFilter R.code B) :=
  hRubin.2 _ _ (codedUnarySet_isCodedDefinable R.code classNodeFormula)
    R.classOrder_isCodedDefinable R.classOrder_poset _ (R.codedBranchFilter_maximallyCompatible hc hB)
    ⟨codedBranchSequence R.code κ c B, R.codedBranchFilter_cofinalChain hc hB⟩

end ZFVP.BinaryRelationRepresentation
