import ZFVP.ModelTheory.SchmerlInternalBranchPreservation
import ZFVP.ModelTheory.ForcingSemanticConsequence
import ZFVP.ModelTheory.ForcingModelChecks

/-! An actual cofinal-branch formula and its checked-name forcing relation.
The condition/node relation is an internal separation set. Its local clauses
follow from quotient truth, including for ill-founded countable ground models. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace Schmerl

def internalCofinalBranchFormula : SetTheorySemisentence 5 :=
  f“B T S k r. (∀ x ∈ B, x ∈ T) ∧
    (∀ x ∈ B, ∀ y ∈ B, !kpair.dfn x y ∈ S ∨ !kpair.dfn y x ∈ S) ∧
    (∀ i ∈ k, ∃ x ∈ B, ∀ j ∈ i, j ∈ !value.dfn r x) ∧
    (∀ x ∈ T, ∀ y ∈ B, !kpair.dfn x y ∈ S → x ∈ B)”

/-- A full downward-closed branch with cofinal ranks. -/
def IsInternalCofinalBranch (T S κ rank B : V) : Prop :=
  B ⊆ T ∧
    (∀ x ∈ B, ∀ y ∈ B, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) ∧
    (∀ i ∈ κ, ∃ x ∈ B, i ⊆ (rank ‘ x)) ∧
    (∀ x ∈ T, ∀ y ∈ B, ⟨x, y⟩ₖ ∈ S → x ∈ B)

theorem eval_internalCofinalBranchFormula (v : Fin 5 → V) :
    internalCofinalBranchFormula.Evalb v ↔
      IsInternalCofinalBranch (v 1) (v 2) (v 3) (v 4) (v 0) := by
  simp [internalCofinalBranchFormula, IsInternalCofinalBranch, SetTheory.subset_def]

instance isInternalCofinalBranch_definable (T S κ rank : V) :
    ℒₛₑₜ-predicate[V] (IsInternalCofinalBranch T S κ rank) := by
  unfold IsInternalCofinalBranch
  definability

/-- The ground ranked-tree assumptions used by the splitting argument. -/
structure InternalRankedTree (T S κ rank : V) : Prop where
  rank_function : rank ∈ κ ^ T
  rank_monotone : ∀ x ∈ T, ∀ y ∈ T, ⟨x, y⟩ₖ ∈ S → (rank ‘ x) ⊆ (rank ‘ y)
  below_linear : ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T,
    ⟨x, z⟩ₖ ∈ S → ⟨y, z⟩ₖ ∈ S → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S

def ForcesInternalCofinalBranch (P R one T S κ rank τ base : V) : Prop :=
  base ∈ forcingFormula P R internalCofinalBranchFormula
    (standardTuple ![τ, checkName one T, checkName one S, checkName one κ, checkName one rank])

noncomputable def checkedBranchRelation (P R one T τ base : V) : V :=
  {a ∈ P ×ˢ T ; ⟨kpair.π₁ a, base⟩ₖ ∈ R ∧
    kpair.π₁ a ∈ atomicMembership P R (checkName one (kpair.π₂ a)) τ}

theorem pair_mem_checkedBranchRelation (P R one T τ base p x : V) :
    ⟨p, x⟩ₖ ∈ checkedBranchRelation P R one T τ base ↔
      p ∈ P ∧ x ∈ T ∧ ⟨p, base⟩ₖ ∈ R ∧
        p ∈ atomicMembership P R (checkName one x) τ := by
  simp only [checkedBranchRelation, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

end Schmerl

namespace ForcingContext

open Schmerl

theorem checkedBranchMembership_truth (F : ForcingContext V) (τ : ForcingName F.P) (x : V) :
    F.check x ∈ F.ofName τ ↔
      ∃ p ∈ F.G, p ∈ atomicMembership F.P F.R (checkName F.one x) τ.val := Iff.rfl

theorem internalCofinalBranch_truth (F : ForcingContext V) (τ : ForcingName F.P)
    (T S κ rank : V) :
    IsInternalCofinalBranch (F.check T) (F.check S) (F.check κ) (F.check rank) (F.ofName τ) ↔
      ∃ p ∈ F.G, ForcesInternalCofinalBranch F.P F.R F.one T S κ rank τ.val p := by
  let ν (x : V) : ForcingName F.P := ⟨checkName F.one x, checkName_isName F.top.1 x⟩
  exact (eval_internalCofinalBranchFormula _).symm.trans
    (F.formula_truth internalCofinalBranchFormula ![τ, ν T, ν S, ν κ, ν rank])

theorem check_subset_iff (F : ForcingContext V) (a b : V) :
    F.check a ⊆ F.check b ↔ a ⊆ b := by
  constructor
  · intro h x hx
    exact (F.check_mem_iff x b).mp (h _ ((F.check_mem_iff x a).mpr hx))
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := (F.mem_check_iff a x).mp hx
    exact (F.check_mem_iff y b).mpr (h y hy)

theorem check_relation_iff (F : ForcingContext V) (S x y : V) :
    ⟨F.check x, F.check y⟩ₖ ∈ F.check S ↔ ⟨x, y⟩ₖ ∈ S := by
  rw [← F.check_kpair, F.check_mem_iff]

end ForcingContext

namespace Schmerl

variable [Countable V]

theorem checkedBranchRelation_internalBranchRelation
    {P R one T S κ rank τ base : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hτ : IsForcingName P τ)
    (hTree : InternalRankedTree T S κ rank)
    (hbase : ForcesInternalCofinalBranch P R one T S κ rank τ base) :
    InternalBranchRelation P R T S κ rank (checkedBranchRelation P R one T τ base) base := by
  refine ⟨hTree.rank_function, hTree.rank_monotone, hTree.below_linear, ?_, ?_, ?_⟩
  · intro p hp q hq x hx hpq hqx
    obtain ⟨_, _, hqb, hqx⟩ := (pair_mem_checkedBranchRelation _ _ _ _ _ _ _ _).mp hqx
    exact (pair_mem_checkedBranchRelation _ _ _ _ _ _ _ _).mpr
      ⟨hp, hx, hR.2.2 p hp q hq base
        ((forcingFormula_regular hR internalCofinalBranchFormula _).1 base hbase) hpq hqb,
        atomicMembership_mono hR hqx hp hpq⟩
  · intro p hp x hx y hy hpx hpy
    obtain ⟨_, _, hpb, hpx⟩ := (pair_mem_checkedBranchRelation _ _ _ _ _ _ _ _).mp hpx
    obtain ⟨_, _, _, hpy⟩ := (pair_mem_checkedBranchRelation _ _ _ _ _ _ _ _).mp hpy
    obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
    let F : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    have hbP := (forcingFormula_regular hR internalCofinalBranchFormula _).1 base hbase
    have hbG := hG.1.2.2.1 p hpG base hbP hpb
    have hB := (F.internalCofinalBranch_truth ⟨τ, hτ⟩ T S κ rank).mpr ⟨base, hbG, hbase⟩
    have hxy := hB.2.1 (F.check x) ((F.checkedBranchMembership_truth ⟨τ, hτ⟩ x).mpr ⟨p, hpG, hpx⟩)
      (F.check y) ((F.checkedBranchMembership_truth ⟨τ, hτ⟩ y).mpr ⟨p, hpG, hpy⟩)
    exact hxy.imp (F.check_relation_iff S x y).mp (F.check_relation_iff S y x).mp
  · intro p hp hpb i hi
    obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
    let F : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    have hbP := (forcingFormula_regular hR internalCofinalBranchFormula _).1 base hbase
    have hbG := hG.1.2.2.1 p hpG base hbP hpb
    have hB := (F.internalCofinalBranch_truth ⟨τ, hτ⟩ T S κ rank).mpr ⟨base, hbG, hbase⟩
    obtain ⟨z, hzB, hiz⟩ := hB.2.2.1 (F.check i) ((F.check_mem_iff i κ).mpr hi)
    obtain ⟨x, hx, rfl⟩ := (F.mem_check_iff T z).mp (hB.1 z hzB)
    obtain ⟨q, hqG, hqx⟩ := (F.checkedBranchMembership_truth ⟨τ, hτ⟩ x).mp hzB
    obtain ⟨r, hrG, hrq, hrp⟩ := hG.1.2.2.2 q hqG p hpG
    have hr := hG.1.1 r hrG
    refine ⟨r, hr, hrp, x, hx,
      (pair_mem_checkedBranchRelation _ _ _ _ _ _ _ _).mpr
        ⟨hr, hx, hR.2.2 r hr p hp base hbP hrp hpb, atomicMembership_mono hR hqx hr hrq⟩, ?_⟩
    let : IsFunction rank := IsFunction.of_mem hTree.rank_function
    rw [F.check_value (domain_eq_of_mem_function hTree.rank_function ▸ hx)] at hiz
    exact (F.check_subset_iff i (rank ‘ x)).mp hiz

end Schmerl
end ZFVP
