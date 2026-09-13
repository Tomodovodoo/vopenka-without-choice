import ZFVP.ModelTheory.SchmerlCodedFunctionBranchSequence

/-! A full-tree maximally compatible filter reconstructed from a selected
cofinal branch. The Rubin clause applies to this full definable poset. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedFunctionBranchFilter (M s B : V) : V :=
  {x ∈ codedFunctionNodes M s ; ∃ y ∈ B, ⟨x, y⟩ₖ ∈ codedFunctionOrder M s}

theorem mem_codedFunctionBranchFilter (M s B x : V) :
    x ∈ codedFunctionBranchFilter M s B ↔ x ∈ codedFunctionNodes M s ∧ ∃ y ∈ B, ⟨x, y⟩ₖ ∈ codedFunctionOrder M s := mem_sep_iff

instance codedFunctionBranchFilter_definable : ℒₛₑₜ-function₃[V] codedFunctionBranchFilter := by
  have h : ℒₛₑₜ-relation₄[V] (fun F M s B ↦ ∀ x, x ∈ F ↔
      x ∈ codedFunctionNodes M s ∧ ∃ y ∈ B, ⟨x, y⟩ₖ ∈ codedFunctionOrder M s) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_codedFunctionBranchFilter]
  rfl

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W) (s : W)

variable {κ c B : V} [IsOrdinal κ]
variable (hc : IsInternalCofinalStrictChain κ (codedFiniteDomains R.code (R.equiv s).val) (codedFiniteDomainOrder R.code (R.equiv s).val) c)
variable (hB : IsInternalCofinalBranch (codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
  (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) κ (codedSelectedFunctionRank R.code (R.equiv s).val κ c) B)

include hB

omit [IsOrdinal κ] in
theorem selectedFunctionBranch_subset_filter : B ⊆ codedFunctionBranchFilter R.code (R.equiv s).val B := by
  intro x hx
  have hxT := ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp (hB.1 x hx)).1
  exact (mem_codedFunctionBranchFilter _ _ _ _).mpr ⟨hxT, x, hx, (R.functionOrder_poset s).1.2.1 x hxT⟩

omit [IsOrdinal κ] in
theorem codedFunctionBranchFilter_recovers :
    codedFunctionBranchFilter R.code (R.equiv s).val B ∩ codedSelectedFunctionNodes R.code (R.equiv s).val κ c = B := by
  apply mem_ext
  intro x
  rw [mem_inter_iff]
  constructor
  · rintro ⟨hF, hx⟩
    obtain ⟨_, y, hy, hxy⟩ := (mem_codedFunctionBranchFilter _ _ _ _).mp hF
    exact hB.2.2.2 x hx y hy ((pair_mem_codedSelectedFunctionOrder _ _ _ _ _ _).mpr ⟨hxy, hx, hB.1 y hy⟩)
  · intro hx
    exact ⟨R.selectedFunctionBranch_subset_filter s hB x hx, hB.1 x hx⟩

omit [IsOrdinal κ] in
theorem codedFunctionBranchFilter_directed {x y : V} (hx : x ∈ codedFunctionBranchFilter R.code (R.equiv s).val B)
    (hy : y ∈ codedFunctionBranchFilter R.code (R.equiv s).val B) :
    ∃ z ∈ codedFunctionBranchFilter R.code (R.equiv s).val B, ⟨x, z⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val ∧ ⟨y, z⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val := by
  obtain ⟨hxT, b, hb, hxb⟩ := (mem_codedFunctionBranchFilter _ _ _ _).mp hx
  obtain ⟨hyT, d, hd, hyd⟩ := (mem_codedFunctionBranchFilter _ _ _ _).mp hy
  have hbT := ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp (hB.1 b hb)).1
  have hdT := ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp (hB.1 d hd)).1
  rcases hB.2.1 b hb d hd with hbd | hdb
  · exact ⟨d, R.selectedFunctionBranch_subset_filter s hB d hd,
      (R.functionOrder_poset s).1.2.2 x hxT b hbT d hdT hxb (mem_inter_iff.mp hbd).1, hyd⟩
  · exact ⟨b, R.selectedFunctionBranch_subset_filter s hB b hb, hxb,
      (R.functionOrder_poset s).1.2.2 y hyT d hdT b hbT hyd (mem_inter_iff.mp hdb).1⟩

include hc

theorem codedFunctionBranchFilter_maximallyCompatible :
    IsInternalMaximallyCompatible (codedFunctionNodes R.code (R.equiv s).val) (codedFunctionOrder R.code (R.equiv s).val) (codedFunctionBranchFilter R.code (R.equiv s).val B) := by
  refine ⟨fun x hx ↦ ((mem_codedFunctionBranchFilter _ _ _ _).mp hx).1,
    fun _ hx _ hy ↦ R.codedFunctionBranchFilter_directed s hB hx hy, ?_⟩
  intro q hq hcompatible
  have hqO := function_value_mem (R.functionDomains_function s) hq
  obtain ⟨i, hi, hqi⟩ := hc.2.2 _ hqO
  obtain ⟨b, hb, hbrank⟩ := R.selectedFunctionBranch_node_at_rank s hc hB hi
  obtain ⟨z, hz, hbz, hqz⟩ := hcompatible b (R.selectedFunctionBranch_subset_filter s hB b hb)
  have hbT := ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp (hB.1 b hb)).1
  have hblevel := (codedSelectedFunctionRank_spec hc (hB.1 b hb)).2
  rw [hbrank] at hblevel
  have hqb := R.functionOrder_of_common_above_of_domains s hq hbT hz hqz hbz (hblevel.symm ▸ hqi)
  exact (mem_codedFunctionBranchFilter _ _ _ _).mpr ⟨hq, b, hb, hqb⟩

theorem codedFunctionBranchFilter_cofinalChain :
    IsInternalCofinalStrictChain κ (codedFunctionBranchFilter R.code (R.equiv s).val B) (codedFunctionOrder R.code (R.equiv s).val)
      (codedFunctionBranchSequence R.code (R.equiv s).val κ c B) := by
  refine ⟨mem_function_of_mem_function_of_subset (R.codedFunctionBranchSequence_function s hc hB)
    (R.selectedFunctionBranch_subset_filter s hB), ?_, ?_⟩
  · exact fun _ hi _ hj hij ↦ R.codedFunctionBranchSequence_strict s hc hB hi hj hij
  · intro x hx
    obtain ⟨_, b, hb, hxb⟩ := (mem_codedFunctionBranchFilter _ _ _ _).mp hx
    refine ⟨(codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ b, (codedSelectedFunctionRank_spec hc (hB.1 b hb)).1, ?_⟩
    rw [R.codedFunctionBranchSequence_recovers s hc hB hb]
    exact hxb

theorem codedFunctionBranchFilter_isCodedDefinable (hRubin : IsCodedRubin R.code κ) :
    IsCodedDefinableSet R.code (codedFunctionBranchFilter R.code (R.equiv s).val B) :=
  hRubin.2 _ _ (codedFunctionNodes_isCodedDefinable (by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using (R.equiv s).property))
    (R.functionOrder_isCodedDefinable s) (R.functionOrder_poset s) _ (R.codedFunctionBranchFilter_maximallyCompatible s hc hB)
    ⟨codedFunctionBranchSequence R.code (R.equiv s).val κ c B, R.codedFunctionBranchFilter_cofinalChain s hc hB⟩

end ZFVP.BinaryRelationRepresentation

