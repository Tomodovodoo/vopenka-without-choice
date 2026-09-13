import ZFVP.ModelTheory.SchmerlCodedSelectedFunctionTree

/-! Every internal selected-tree cofinal branch has a unique node at each
selected rank. Those nodes form an actual internal κ-sequence. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedFunctionBranchSequence (M s κ c B : V) : V :=
  {p ∈ κ ×ˢ B ; (codedSelectedFunctionRank M s κ c) ‘ (kpair.π₂ p) = kpair.π₁ p}

theorem pair_mem_codedFunctionBranchSequence (M s κ c B i x : V) :
    ⟨i, x⟩ₖ ∈ codedFunctionBranchSequence M s κ c B ↔ i ∈ κ ∧ x ∈ B ∧ (codedSelectedFunctionRank M s κ c) ‘ x = i := by
  simp only [codedFunctionBranchSequence, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

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

include hc hB

theorem selectedFunctionBranch_node_at_rank {i : V} (hi : i ∈ κ) :
    ∃ x ∈ B, (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ x = i := by
  obtain ⟨y, hy, hiy⟩ := hB.2.2.1 i hi
  have hyT := hB.1 y hy
  have hyr := codedSelectedFunctionRank_spec hc hyT
  have hlevel : ⟨c ‘ i, (codedFunctionDomains R.code (R.equiv s).val) ‘ y⟩ₖ ∈ codedFiniteDomainOrder R.code (R.equiv s).val := by
    rw [hyr.2]
    exact hc.mono (R.finiteDomainOrder_poset s) hi hyr.1 hiy
  obtain ⟨x, hx, hxy, hxr⟩ := R.functionDomains_predecessor s
    ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hyT).1 (function_value_mem hc.1 hi) hlevel
  have hxT := (mem_codedSelectedFunctionNodes _ _ _ _ _).mpr ⟨hx, i, hi, hxr⟩
  have hxB := hB.2.2.2 x hxT y hy ((pair_mem_codedSelectedFunctionOrder _ _ _ _ _ _).mpr ⟨hxy, hxT, hyT⟩)
  let : IsFunction (codedSelectedFunctionRank R.code (R.equiv s).val κ c) := IsFunction.of_mem (codedSelectedFunctionRank_function hc)
  exact ⟨x, hxB, value_eq_of_kpair_mem ((pair_mem_codedSelectedFunctionRank _ _ _ _ _ _).mpr ⟨hxT, hi, hxr⟩)⟩

theorem selectedFunctionBranch_rank_injective {x y : V} (hx : x ∈ B) (hy : y ∈ B)
    (he : (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ x = (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ y) : x = y := by
  rcases hB.2.1 x hx y hy with hxy | hyx
  · exact R.selectedFunctionRank_comparable_injective s hc (hB.1 x hx) (hB.1 y hy) hxy he
  · exact (R.selectedFunctionRank_comparable_injective s hc (hB.1 y hy) (hB.1 x hx) hyx he.symm).symm

theorem codedFunctionBranchSequence_function : codedFunctionBranchSequence R.code (R.equiv s).val κ c B ∈ B ^ κ := by
  apply mem_function_iff.mpr
  refine ⟨fun _ hp ↦ (mem_sep_iff.mp hp).1, ?_⟩
  intro i hi
  obtain ⟨x, hx, hr⟩ := R.selectedFunctionBranch_node_at_rank s hc hB hi
  refine ⟨x, (pair_mem_codedFunctionBranchSequence _ _ _ _ _ _ _).mpr ⟨hi, hx, hr⟩, ?_⟩
  intro y hy
  have hy' := (pair_mem_codedFunctionBranchSequence _ _ _ _ _ _ _).mp hy
  exact R.selectedFunctionBranch_rank_injective s hc hB hy'.2.1 hx (hy'.2.2.trans hr.symm)

theorem codedFunctionBranchSequence_value {i : V} (hi : i ∈ κ) :
    (codedFunctionBranchSequence R.code (R.equiv s).val κ c B) ‘ i ∈ B ∧
      (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ ((codedFunctionBranchSequence R.code (R.equiv s).val κ c B) ‘ i) = i := by
  have hf := R.codedFunctionBranchSequence_function s hc hB
  let : IsFunction (codedFunctionBranchSequence R.code (R.equiv s).val κ c B) := IsFunction.of_mem hf
  have hp := kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hi)
  exact ((pair_mem_codedFunctionBranchSequence _ _ _ _ _ _ _).mp hp).2

theorem codedFunctionBranchSequence_recovers {x : V} (hx : x ∈ B) :
    (codedFunctionBranchSequence R.code (R.equiv s).val κ c B) ‘ ((codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ x) = x := by
  have hi := (codedSelectedFunctionRank_spec hc (hB.1 x hx)).1
  have hv := R.codedFunctionBranchSequence_value s hc hB hi
  exact R.selectedFunctionBranch_rank_injective s hc hB hv.1 hx hv.2

theorem codedFunctionBranchSequence_strict {i j : V} (hi : i ∈ κ) (hj : j ∈ κ) (hij : i ∈ j) :
    ⟨(codedFunctionBranchSequence R.code (R.equiv s).val κ c B) ‘ i, (codedFunctionBranchSequence R.code (R.equiv s).val κ c B) ‘ j⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val ∧
      (codedFunctionBranchSequence R.code (R.equiv s).val κ c B) ‘ i ≠ (codedFunctionBranchSequence R.code (R.equiv s).val κ c B) ‘ j := by
  have hvi := R.codedFunctionBranchSequence_value s hc hB hi
  have hvj := R.codedFunctionBranchSequence_value s hc hB hj
  constructor
  · rcases hB.2.1 _ hvi.1 _ hvj.1 with he | he
    · exact (mem_inter_iff.mp he).1
    · have hs := (R.selectedFunctionTree s hc).rank_monotone _ (hB.1 _ hvj.1) _ (hB.1 _ hvi.1) he
      rw [hvi.2, hvj.2] at hs
      exact False.elim (mem_irrefl i (hs i hij))
  · intro he
    have he' := congrArg (fun x ↦ (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ x) he
    rw [hvi.2, hvj.2] at he'
    exact mem_irrefl j (he' ▸ hij)

end ZFVP.BinaryRelationRepresentation

