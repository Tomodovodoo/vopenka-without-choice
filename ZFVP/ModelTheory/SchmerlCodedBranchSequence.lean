import ZFVP.ModelTheory.SchmerlCodedSelectedTree

/-! Every internal selected-tree cofinal branch has a unique node at each
selected rank. Those nodes form an actual internal κ-sequence. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsInternalCofinalStrictChain.mono {κ P S c i j : V} [IsOrdinal κ]
    (h : IsInternalCofinalStrictChain κ P S c) (hP : IsForcingPoset P S)
    (hi : i ∈ κ) (hj : j ∈ κ) (hij : i ⊆ j) : ⟨c ‘ i, c ‘ j⟩ₖ ∈ S := by
  let : IsOrdinal i := IsOrdinal.of_mem hi
  let : IsOrdinal j := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy (α := i) (β := j) with hij' | rfl | hji
  · exact (h.2.1 i hi j hj hij').1
  · exact hP.1.2.1 _ (function_value_mem h.1 hi)
  · exact False.elim (mem_irrefl j (hij j hji))

noncomputable def codedBranchSequence (M κ c B : V) : V :=
  {p ∈ κ ×ˢ B ; (codedSelectedClassRank M κ c) ‘ (kpair.π₂ p) = kpair.π₁ p}

theorem pair_mem_codedBranchSequence (M κ c B i x : V) :
    ⟨i, x⟩ₖ ∈ codedBranchSequence M κ c B ↔ i ∈ κ ∧ x ∈ B ∧ (codedSelectedClassRank M κ c) ‘ x = i := by
  simp only [codedBranchSequence, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)
variable {κ c B : V} [IsOrdinal κ]
variable (hc : IsInternalCofinalStrictChain κ (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
variable (hB : IsInternalCofinalBranch (codedSelectedClassNodes R.code κ c)
  (codedSelectedClassOrder R.code κ c) κ (codedSelectedClassRank R.code κ c) B)

include hc hB

theorem selectedBranch_node_at_rank {i : V} (hi : i ∈ κ) :
    ∃ x ∈ B, (codedSelectedClassRank R.code κ c) ‘ x = i := by
  obtain ⟨y, hy, hiy⟩ := hB.2.2.1 i hi
  have hyT := hB.1 y hy
  have hyr := codedSelectedClassRank_spec hc hyT
  have hlevel : ⟨c ‘ i, (codedClassLevels R.code) ‘ y⟩ₖ ∈ codedOrdinalOrder R.code := by
    rw [hyr.2]
    exact hc.mono R.ordinalOrder_poset hi hyr.1 hiy
  obtain ⟨x, hx, hxy, hxr⟩ := R.classLevels_predecessor
    ((mem_codedSelectedClassNodes _ _ _ _).mp hyT).1 (function_value_mem hc.1 hi) hlevel
  have hxT := (mem_codedSelectedClassNodes _ _ _ _).mpr ⟨hx, i, hi, hxr⟩
  have hxB := hB.2.2.2 x hxT y hy ((pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr ⟨hxy, hxT, hyT⟩)
  let : IsFunction (codedSelectedClassRank R.code κ c) := IsFunction.of_mem (codedSelectedClassRank_function hc)
  exact ⟨x, hxB, value_eq_of_kpair_mem ((pair_mem_codedSelectedClassRank _ _ _ _ _).mpr ⟨hxT, hi, hxr⟩)⟩

theorem selectedBranch_rank_injective {x y : V} (hx : x ∈ B) (hy : y ∈ B)
    (he : (codedSelectedClassRank R.code κ c) ‘ x = (codedSelectedClassRank R.code κ c) ‘ y) : x = y := by
  rcases hB.2.1 x hx y hy with hxy | hyx
  · exact R.selectedClassRank_comparable_injective hc (hB.1 x hx) (hB.1 y hy) hxy he
  · exact (R.selectedClassRank_comparable_injective hc (hB.1 y hy) (hB.1 x hx) hyx he.symm).symm

theorem codedBranchSequence_function : codedBranchSequence R.code κ c B ∈ B ^ κ := by
  apply mem_function_iff.mpr
  refine ⟨fun _ hp ↦ (mem_sep_iff.mp hp).1, ?_⟩
  intro i hi
  obtain ⟨x, hx, hr⟩ := R.selectedBranch_node_at_rank hc hB hi
  refine ⟨x, (pair_mem_codedBranchSequence _ _ _ _ _ _).mpr ⟨hi, hx, hr⟩, ?_⟩
  intro y hy
  have hy' := (pair_mem_codedBranchSequence _ _ _ _ _ _).mp hy
  exact R.selectedBranch_rank_injective hc hB hy'.2.1 hx (hy'.2.2.trans hr.symm)

theorem codedBranchSequence_value {i : V} (hi : i ∈ κ) :
    (codedBranchSequence R.code κ c B) ‘ i ∈ B ∧
      (codedSelectedClassRank R.code κ c) ‘ ((codedBranchSequence R.code κ c B) ‘ i) = i := by
  have hf := R.codedBranchSequence_function hc hB
  let : IsFunction (codedBranchSequence R.code κ c B) := IsFunction.of_mem hf
  have hp := kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hi)
  exact ((pair_mem_codedBranchSequence _ _ _ _ _ _).mp hp).2

theorem codedBranchSequence_recovers {x : V} (hx : x ∈ B) :
    (codedBranchSequence R.code κ c B) ‘ ((codedSelectedClassRank R.code κ c) ‘ x) = x := by
  have hi := (codedSelectedClassRank_spec hc (hB.1 x hx)).1
  have hv := R.codedBranchSequence_value hc hB hi
  exact R.selectedBranch_rank_injective hc hB hv.1 hx hv.2

theorem codedBranchSequence_strict {i j : V} (hi : i ∈ κ) (hj : j ∈ κ) (hij : i ∈ j) :
    ⟨(codedBranchSequence R.code κ c B) ‘ i, (codedBranchSequence R.code κ c B) ‘ j⟩ₖ ∈ codedClassOrder R.code ∧
      (codedBranchSequence R.code κ c B) ‘ i ≠ (codedBranchSequence R.code κ c B) ‘ j := by
  have hvi := R.codedBranchSequence_value hc hB hi
  have hvj := R.codedBranchSequence_value hc hB hj
  constructor
  · rcases hB.2.1 _ hvi.1 _ hvj.1 with he | he
    · exact (mem_inter_iff.mp he).1
    · have hs := (R.selectedClassTree hc).rank_monotone _ (hB.1 _ hvj.1) _ (hB.1 _ hvi.1) he
      rw [hvi.2, hvj.2] at hs
      exact False.elim (mem_irrefl i (hs i hij))
  · intro he
    have he' := congrArg (fun x ↦ (codedSelectedClassRank R.code κ c) ‘ x) he
    rw [hvi.2, hvj.2] at he'
    exact mem_irrefl j (he' ▸ hij)

end ZFVP.BinaryRelationRepresentation
