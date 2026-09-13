import ZFVP.ModelTheory.SchmerlInternalBranchNames

/-! Internal square ccc prevents new full cofinal branches in the actual
forcing quotient. The ground branch is the internal set of all possible
nodes below a stabilizing condition in the generic filter. -/

namespace ZFVP.ForcingContext

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalCofinalBranch_of_check (F : ForcingContext V) {T S κ rank B : V}
    (hrank : rank ∈ κ ^ T)
    (hB : IsInternalCofinalBranch (F.check T) (F.check S) (F.check κ)
      (F.check rank) (F.check B)) : IsInternalCofinalBranch T S κ rank B := by
  let : IsFunction rank := IsFunction.of_mem hrank
  have hBT : B ⊆ T := (F.check_subset_iff B T).mp hB.1
  refine ⟨hBT, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact (hB.2.1 (F.check x) ((F.check_mem_iff x B).mpr hx)
      (F.check y) ((F.check_mem_iff y B).mpr hy)).imp
      (F.check_relation_iff S x y).mp (F.check_relation_iff S y x).mp
  · intro i hi
    obtain ⟨x, hx, hix⟩ := hB.2.2.1 (F.check i) ((F.check_mem_iff i κ).mpr hi)
    obtain ⟨y, hy, rfl⟩ := (F.mem_check_iff B x).mp hx
    refine ⟨y, hy, ?_⟩
    rw [F.check_value (domain_eq_of_mem_function hrank ▸ hBT y hy)] at hix
    exact (F.check_subset_iff i (rank ‘ y)).mp hix
  · intro x hx y hy hxy
    exact (F.check_mem_iff x B).mp (hB.2.2.2 (F.check x) ((F.check_mem_iff x T).mpr hx)
      (F.check y) ((F.check_mem_iff y B).mpr hy) ((F.check_relation_iff S x y).mpr hxy))

/-- Every actual branch node is possible below any condition in the filter. -/
theorem branch_node_mem_internalPossibleNodes (F : ForcingContext V)
    (τ : ForcingName F.P) {T base p x : V} (hbase : base ∈ F.G) (hp : p ∈ F.G)
    (hx : x ∈ T) (hxB : F.check x ∈ F.ofName τ) :
    x ∈ internalPossibleNodes F.P F.R T
      (checkedBranchRelation F.P F.R F.one T τ.val base) p := by
  obtain ⟨q, hqG, hqx⟩ := (F.checkedBranchMembership_truth τ x).mp hxB
  obtain ⟨r, hrG, hrq, hrp⟩ := F.generic.1.2.2.2 q hqG p hp
  obtain ⟨s, hsG, hsr, hsb⟩ := F.generic.1.2.2.2 r hrG base hbase
  have hs := F.generic.1.1 s hsG
  have hr := F.generic.1.1 r hrG
  have hsq := F.order.2.2 s hs r hr q (F.generic.1.1 q hqG) hsr hrq
  exact mem_sep_iff.mpr ⟨hx, s, hs,
    F.order.2.2 s hs r hr p (F.generic.1.1 p hp) hsr hrp,
    (pair_mem_checkedBranchRelation _ _ _ _ _ _ _ _).mpr
      ⟨hs, hx, hsb, atomicMembership_mono F.order hqx hs hsq⟩⟩

/-- Stabilization identifies the full quotient branch with one checked ground set. -/
theorem cofinalBranch_eq_checkedPossibleNodes (F : ForcingContext V)
    (τ : ForcingName F.P) {T S κ rank base p : V}
    (hTree : InternalRankedTree T S κ rank) (hreg : IsRegularCardinal κ)
    (hω : (ω : V) ∈ κ) (hbase : base ∈ F.G) (hp : p ∈ F.G)
    (hstab : InternalStabilizes F.P F.R T S
      (checkedBranchRelation F.P F.R F.one T τ.val base) p)
    (hB : IsInternalCofinalBranch (F.check T) (F.check S) (F.check κ)
      (F.check rank) (F.ofName τ)) :
    F.ofName τ = F.check (internalPossibleNodes F.P F.R T
      (checkedBranchRelation F.P F.R F.one T τ.val base) p) := by
  let : IsFunction rank := IsFunction.of_mem hTree.rank_function
  let C := internalPossibleNodes F.P F.R T
    (checkedBranchRelation F.P F.R F.one T τ.val base) p
  apply mem_ext_iff.mpr
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (F.mem_check_iff T z).mp (hB.1 z hz)
    exact (F.check_mem_iff x C).mpr (F.branch_node_mem_internalPossibleNodes τ hbase hp hx hz)
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (F.mem_check_iff C z).mp hz
    have hxT : x ∈ T := (mem_sep_iff.mp hx).1
    have hxκ := function_value_mem hTree.rank_function hxT
    obtain ⟨i, hi, hbound⟩ := regular_small_subset_bounded hreg
      (show ({rank ‘ x} : V) ⊆ κ from fun j hj ↦ (mem_singleton_iff.mp hj) ▸ hxκ)
      hω (internallyCountable_singleton (rank ‘ x))
    have hxi : (rank ‘ x) ∈ i := hbound _ (mem_singleton_iff.mpr rfl)
    obtain ⟨z, hzB, hiz⟩ := hB.2.2.1 (F.check i) ((F.check_mem_iff i κ).mpr hi)
    obtain ⟨y, hy, rfl⟩ := (F.mem_check_iff T z).mp (hB.1 z hzB)
    have hyC := F.branch_node_mem_internalPossibleNodes τ hbase hp hy hzB
    have hxy := hstab x hx y hyC
    rw [F.check_value (domain_eq_of_mem_function hTree.rank_function ▸ hy)] at hiz
    have hxyRank : (rank ‘ x) ∈ (rank ‘ y) := (F.check_subset_iff i (rank ‘ y)).mp hiz _ hxi
    have hxyS : ⟨x, y⟩ₖ ∈ S := hxy.resolve_right (fun hyx ↦
      mem_irrefl (rank ‘ x) (hTree.rank_monotone y hy x hxT hyx _ hxyRank))
    exact hB.2.2.2 (F.check x) ((F.check_mem_iff x T).mpr hxT) (F.check y) hzB
      ((F.check_relation_iff S x y).mpr hxyS)

/-- No new internal cofinal branch is added by a forcing with internally ccc
square. All tree and cardinal assumptions refer to the ground model. -/
theorem exists_ground_cofinalBranch_of_internalSquareCCC [Countable V]
    (F : ForcingContext V) (hAC : InternalChoice V) {T S κ rank : V}
    (hTree : InternalRankedTree T S κ rank) (hreg : IsRegularCardinal κ)
    (hω : (ω : V) ∈ κ)
    (hccc : ∀ A : V,
      IsForcingAntichain (F.P ×ˢ F.P) (productOrder F.P F.R F.P F.R) A → IsInternallyCountable A)
    {B : F.Model}
    (hB : IsInternalCofinalBranch (F.check T) (F.check S) (F.check κ) (F.check rank) B) :
    ∃ C : V, IsInternalCofinalBranch T S κ rank C ∧ F.check C = B := by
  obtain ⟨τ, rfl⟩ := F.ofName_surjective B
  obtain ⟨base, hbG, hbase⟩ := (F.internalCofinalBranch_truth τ T S κ rank).mp hB
  have hdata := checkedBranchRelation_internalBranchRelation F.order F.top τ.property hTree hbase
  obtain ⟨p, hpG, hpD⟩ := externalForcingGeneric_meets_denseBelow F.order F.generic hbG
    (internal_stabilizes_dense_below hAC F.order hdata hreg hω hccc)
  have he := F.cofinalBranch_eq_checkedPossibleNodes τ hTree hreg hω hbG hpG
    (mem_sep_iff.mp hpD).2 hB
  refine ⟨_, F.internalCofinalBranch_of_check hTree.rank_function ?_, he.symm⟩
  exact he ▸ hB

end ZFVP.ForcingContext
