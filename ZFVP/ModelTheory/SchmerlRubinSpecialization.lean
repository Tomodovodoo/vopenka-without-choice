import ZFVP.ModelTheory.SchmerlRubinTrees
import ZFVP.ModelTheory.SchmerlSimultaneousSpecialization

/-! A single corrected specializing poset for the class tree and every
finite-function tree of an aleph-one-sized Rubin model. All tree, cofinality,
and branch-bound premises are derived from that model. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory Set Order

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rubinDomainChain (h : IsRubinDefinable V)
    (s : {s : V // IsInternallyInfinite s}) :
    FiniteDomainChain s.val (Ordinal.ToType (Ordinal.omega.{0} 1)) :=
  Classical.choice (exists_finiteDomainChain_of_rubin h s.property)

/-- `none` names the class tree; `some s` names the binary tree over `s`. -/
abbrev RubinTreeIndex (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :=
  Option {s : V // IsInternallyInfinite s}

noncomputable def RubinTree (h : IsRubinDefinable V) : RubinTreeIndex V → Type
  | none => ClassTreeNode V
  | some s => FunctionTreeNode (rubinDomainChain h s)

def RubinRank : RubinTreeIndex V → Type
  | none => SetTheory.Ordinal V
  | some _ => Ordinal.ToType (Ordinal.omega.{0} 1)

noncomputable instance (h : IsRubinDefinable V) (j : RubinTreeIndex V) :
    PartialOrder (RubinTree h j) := by
  cases j <;> dsimp [RubinTree] <;> infer_instance

noncomputable instance (j : RubinTreeIndex V) : LinearOrder (RubinRank j) := by
  cases j <;> dsimp [RubinRank] <;> infer_instance

noncomputable def rubinRankedTree (h : IsRubinDefinable V) (j : RubinTreeIndex V) :
    RankedTree (RubinTree h j) (RubinRank j) := by
  cases j with
  | none => exact ClassTreeNode.rankedTree
  | some s => exact FunctionTreeNode.rankedTree (C := rubinDomainChain h s)

theorem rubinRank_cofinality (h : IsRubinDefinable V) (j : RubinTreeIndex V) :
    Order.cof (RubinRank j) = Cardinal.aleph 1 := by
  cases j with
  | none => exact ordinal_cofinality_of_rubin h
  | some s => exact (Ordinal.cof_toType _).trans Cardinal.cof_omega_one

theorem rubinTree_branch_bound (h : IsRubinDefinable V)
    (hcard : Cardinal.mk V ≤ Cardinal.aleph 1) (j : RubinTreeIndex V) :
    Cardinal.mk {B : Set (RubinTree h j) // (rubinRankedTree h j).IsBranch B} ≤ Cardinal.aleph 1 := by
  cases j with
  | none => exact classTree_branch_bound_of_rubin h hcard
  | some s => exact functionTree_branch_bound_of_rubin h hcard (rubinDomainChain h s)

/-- This is the actual external specializing forcing required in Stage 2. Its
square is ccc, all node-deciding sets are dense, and any directed family meeting
them supplies weak colors on every selected tree. No ccc, branch-count, marker,
or generic-coloring conclusion is assumed. -/
theorem exists_ccc_specialization_of_rubin (h : IsRubinDefinable V)
    (hcard : Cardinal.mk V ≤ Cardinal.aleph 1) :
    ∃ c : ∀ j : RubinTreeIndex V, Ordinal.ToType (Ordinal.omega.{0} 1) ↪o RubinRank j,
      (∀ j, IsCofinal (Set.range (c j))) ∧
      ∃ D : ∀ j, BranchMarkers ((rubinRankedTree h j).restrictRanks (c j))
        {B : Set ((rubinRankedTree h j).RankRestriction (c j)) //
          ((rubinRankedTree h j).restrictRanks (c j)).IsBranch B},
        (∀ A : Set (StrictCondition (Σ j, (D j).core) × StrictCondition (Σ j, (D j).core)),
          A.Pairwise (fun p q ↦ ¬ Poset.Compatible p q) → A.Countable) ∧
        (∀ x, ∀ p : StrictCondition (Σ j, (D j).core),
          ∃ q ≤ p, q ∈ StrictCondition.decides x) ∧
        (∀ G : Set (StrictCondition (Σ j, (D j).core)), DirectedOn (· ≥ ·) G →
          (∀ x, ∃ p ∈ G, p ∈ StrictCondition.decides x) →
          ∃ f : ∀ j, (rubinRankedTree h j).RankRestriction (c j) → ℕ,
            ∀ j, WeaklySpecializes (· ≤ ·) (f j)) :=
  exists_simultaneous_ccc_weak_specialization (rubinRankedTree h)
    (rubinRank_cofinality h) (rubinTree_branch_bound h hcard)

end ZFVP.Schmerl
