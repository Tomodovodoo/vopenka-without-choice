import ZFVP.ModelTheory.SchmerlAronszajnCore
import ZFVP.ModelTheory.SchmerlSpecializationCCC

/-! The corrected ccc weak-specialization forcing: construct the branch markers,
strictly specialize the Aronszajn core, and extend its coloring along the tails.
This states the forcing-poset result through its dense sets and directed union;
it does not assume or assert an ambient generic-extension existence theorem.
-/

namespace ZFVP.Schmerl

open Set

universe u v w

variable {T : Type u} {I : Type v} [PartialOrder T] [LinearOrder I]

namespace BranchMarkers

variable {R : RankedTree T I} {J : Type w} (D : BranchMarkers R J)

/-- The core inherits the tree order. -/
theorem core_tree : IsTreeOrder D.core := by
  intro x y z hx hy
  exact R.tree hx hy

/-- A directed family meeting the strict deciding dense sets provides a weak
specialization of the original tree. -/
theorem exists_weak_coloring_of_directed
    {G : Set (StrictCondition D.core)} (hG : DirectedOn (· ≥ ·) G)
    (hmeets : ∀ x, ∃ p ∈ G, p ∈ StrictCondition.decides x) :
    ∃ f : T → ℕ, WeaklySpecializes (· ≤ ·) f := by
  obtain ⟨f, hf, _⟩ := StrictCondition.exists_coloring hG hmeets
  exact ⟨D.extendColor f, D.extendColor_weaklySpecializes hf⟩

end BranchMarkers

/-- Every omega-one ranked tree with at most aleph-one branches has a ccc
finite-condition weak-specialization forcing, via the constructed core.
No marker system, chain condition, or core-specialization premise is assumed. -/
theorem exists_ccc_weak_specialization_forcing
    (R : RankedTree T (Ordinal.ToType (Ordinal.omega.{v} 1)))
    (hcard : Cardinal.mk {B : Set T // R.IsBranch B} ≤ Cardinal.aleph 1) :
    ∃ D : BranchMarkers R {B : Set T // R.IsBranch B},
      (∀ j, D.branch j = j.val) ∧
      (∀ A : Set (StrictCondition D.core),
        A.Pairwise (fun p q ↦ ¬ StrictCondition.Compatible p q) → A.Countable) ∧
      (∀ x : D.core, ∀ p : StrictCondition D.core,
        ∃ q ≤ p, q ∈ StrictCondition.decides x) ∧
      (∀ G : Set (StrictCondition D.core), DirectedOn (· ≥ ·) G →
        (∀ x, ∃ p ∈ G, p ∈ StrictCondition.decides x) →
        ∃ f : T → ℕ, WeaklySpecializes (· ≤ ·) f) := by
  obtain ⟨D, hD, hchains⟩ := exists_aronszajn_core R hcard
  exact ⟨D, hD, StrictCondition.countable_antichains D.core_tree hchains,
    StrictCondition.decides_dense, fun _ hG hmeet ↦ D.exists_weak_coloring_of_directed hG hmeet⟩

end ZFVP.Schmerl
