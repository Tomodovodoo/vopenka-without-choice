import ZFVP.ModelTheory.SchmerlRankedTree

/-! The branch-tail reduction in Baumgartner's weak specialization argument,
as proved for ranked trees in Switzer, *Destructibility and axiomatizability of
Kaufmann models*, Lemma 3.5 and Claim 3.6.

Separated branch markers determine a subtree and a monotone retraction onto it.
Its fibers are chains. Every strict specialization of that subtree therefore
extends to a weak specialization of the original tree. If the markers enumerate
all branches, the subtree has no cofinal branch.
-/

namespace ZFVP.Schmerl

open Set

universe u v w

variable {T : Type u} {I : Type v} [PartialOrder T] [LinearOrder I]

/-- A family of branches with distinct markers satisfying Baumgartner's
separation condition. This is intermediate construction data, not an assumed
model-existence assertion. -/
structure BranchMarkers (R : RankedTree T I) (J : Type w) where
  branch : J → Set T
  isBranch : ∀ j, R.IsBranch (branch j)
  marker : J → T
  marker_mem : ∀ j, marker j ∈ branch j
  injective : Function.Injective marker
  separates : ∀ i j, marker i < marker j → marker j ∉ branch i

namespace BranchMarkers

variable {R : RankedTree T I} {J : Type w} (D : BranchMarkers R J)

/-- Keep a node precisely when it is not above a marker on any branch containing it. -/
def core : Set T := {x | ∀ j, x ∈ D.branch j → x ≤ D.marker j}

/-- A node belongs to a removed tail if it lies strictly above that branch's marker. -/
def OnTail (x : T) (j : J) : Prop := x ∈ D.branch j ∧ D.marker j < x

theorem marker_mem_core (j : J) : D.marker j ∈ D.core := by
  intro i hi
  by_contra hle
  have hlt := (D.isBranch i).1.lt_of_not_ge hi (D.marker_mem i) hle
  exact D.separates i j hlt hi

theorem onTail_not_core {x : T} {j : J} (hx : D.OnTail x j) : x ∉ D.core :=
  fun h ↦ hx.2.not_ge (h j hx.1)

theorem exists_tail_of_not_core {x : T} (hx : x ∉ D.core) : ∃ j, D.OnTail x j := by
  classical
  have hx' : ∃ j, x ∈ D.branch j ∧ ¬ x ≤ D.marker j := by
    simpa only [core, Set.mem_ofPred_eq, not_forall, not_imp, exists_prop] using hx
  obtain ⟨j, hj, hle⟩ := hx'
  refine ⟨j, hj, ?_⟩
  exact (D.isBranch j).1.lt_of_not_ge hj (D.marker_mem j) hle

/-- Different marked tails are disjoint. -/
theorem tail_unique {x : T} {i j : J} (hi : D.OnTail x i) (hj : D.OnTail x j) : i = j := by
  apply D.injective
  apply le_antisymm
  · by_contra hle
    have hji := (R.tree hi.2.le hj.2.le).resolve_left hle
    have hlt : D.marker j < D.marker i := lt_of_le_not_ge hji hle
    have hmem : D.marker i ∈ D.branch j :=
      branch_downward_closed R.tree (D.isBranch j).isMaxChain hj.1 hi.2.le
    exact D.separates j i hlt hmem
  · by_contra hle
    have hij := (R.tree hi.2.le hj.2.le).resolve_right hle
    have hlt : D.marker i < D.marker j := lt_of_le_not_ge hij hle
    have hmem : D.marker j ∈ D.branch i :=
      branch_downward_closed R.tree (D.isBranch i).isMaxChain hi.1 hj.2.le
    exact D.separates i j hlt hmem

/-- The selected branch whose tail contains a node outside the core. -/
noncomputable def tailIndex (x : T) (hx : x ∉ D.core) : J :=
  Classical.choose (D.exists_tail_of_not_core hx)

theorem tailIndex_spec (x : T) (hx : x ∉ D.core) : D.OnTail x (D.tailIndex x hx) :=
  Classical.choose_spec (D.exists_tail_of_not_core hx)

/-- Retract every removed tail to its marker and fix the core. -/
noncomputable def anchor (x : T) : D.core := by
  classical
  exact if hx : x ∈ D.core then ⟨x, hx⟩
    else ⟨D.marker (D.tailIndex x hx), D.marker_mem_core _⟩

theorem anchor_eq_self {x : T} (hx : x ∈ D.core) : (D.anchor x : T) = x := by
  simp [anchor, hx]

theorem anchor_eq_marker {x : T} {j : J} (hx : D.OnTail x j) :
    (D.anchor x : T) = D.marker j := by
  have hn := D.onTail_not_core hx
  have heq := D.tail_unique (D.tailIndex_spec x hn) hx
  simp [anchor, hn, heq]

theorem anchor_le (x : T) : (D.anchor x : T) ≤ x := by
  by_cases hx : x ∈ D.core
  · exact (D.anchor_eq_self hx).le
  · have ht := D.tailIndex_spec x hx
    rw [D.anchor_eq_marker ht]
    exact ht.2.le

theorem anchor_le_marker_of_mem {x : T} {j : J} (hx : x ∈ D.branch j) :
    (D.anchor x : T) ≤ D.marker j := by
  by_cases hcore : x ∈ D.core
  · rw [D.anchor_eq_self hcore]
    exact hcore j hx
  · have ht := D.tailIndex_spec x hcore
    rw [D.anchor_eq_marker ht]
    have hm : D.marker (D.tailIndex x hcore) ∈ D.branch j :=
      branch_downward_closed R.tree (D.isBranch j).isMaxChain hx ht.2.le
    by_contra hle
    have hlt := (D.isBranch j).1.lt_of_not_ge hm (D.marker_mem j) hle
    exact D.separates j (D.tailIndex x hcore) hlt hm

/-- The retraction is monotone. -/
theorem anchor_monotone : Monotone D.anchor := by
  intro x y hxy
  change (D.anchor x : T) ≤ (D.anchor y : T)
  by_cases hy : y ∈ D.core
  · rw [D.anchor_eq_self hy]
    exact (D.anchor_le x).trans hxy
  · have ht := D.tailIndex_spec y hy
    rw [D.anchor_eq_marker ht]
    have hx := branch_downward_closed R.tree (D.isBranch _).isMaxChain ht.1 hxy
    exact D.anchor_le_marker_of_mem hx

/-- Each fiber of the retraction is a chain. -/
theorem anchor_fiber_chain {x y : T} (heq : D.anchor x = D.anchor y) : x ≤ y ∨ y ≤ x := by
  have hval := congrArg Subtype.val heq
  by_cases hx : x ∈ D.core
  · rw [D.anchor_eq_self hx] at hval
    exact Or.inl (hval ▸ D.anchor_le y)
  · by_cases hy : y ∈ D.core
    · rw [D.anchor_eq_self hy] at hval
      exact Or.inr (hval ▸ D.anchor_le x)
    · have htx := D.tailIndex_spec x hx
      have hty := D.tailIndex_spec y hy
      rw [D.anchor_eq_marker htx, D.anchor_eq_marker hty] at hval
      have hij := D.injective hval
      have hymem : y ∈ D.branch (D.tailIndex x hx) := hij.symm ▸ hty.1
      exact (D.isBranch _).1.total htx.1 hymem

/-- Strict specialization means distinct comparable nodes have different colors. -/
def StrictSpecializes {S : Type*} [PartialOrder S] (f : S → ℕ) : Prop :=
  ∀ ⦃x y⦄, x < y → f x ≠ f y

/-- Extend the core coloring by assigning each removed tail its marker's color. -/
noncomputable def extendColor (f : D.core → ℕ) (x : T) : ℕ := f (D.anchor x)

theorem extendColor_on_core (f : D.core → ℕ) (x : D.core) : D.extendColor f x = f x := by
  apply congrArg f
  exact Subtype.ext (D.anchor_eq_self x.property)

/-- Baumgartner's extension step, Switzer's Claim 3.6. -/
theorem extendColor_weaklySpecializes {f : D.core → ℕ} (hf : StrictSpecializes f) :
    WeaklySpecializes (· ≤ ·) (D.extendColor f) := by
  have heq : ∀ ⦃x y : T⦄, x ≤ y → D.extendColor f x = D.extendColor f y →
      D.anchor x = D.anchor y := by
    intro x y hxy hcolor
    by_contra hne
    exact hf (lt_of_le_of_ne (D.anchor_monotone hxy) hne) hcolor
  intro x y z hxy hxz hfy hfz
  exact D.anchor_fiber_chain ((heq hxy hfy).symm.trans (heq hxz hfz))

/-- If every cofinal branch has a marker, the core contains no cofinal branch. -/
theorem core_no_branch [NoMaxOrder I]
    (hall : ∀ B, R.IsBranch B → ∃ j, D.branch j = B) :
    ¬ ∃ B, R.IsBranch B ∧ B ⊆ D.core := by
  rintro ⟨B, hB, hsub⟩
  obtain ⟨j, rfl⟩ := hall B hB
  obtain ⟨i, hi⟩ := exists_gt (R.rank (D.marker j))
  obtain ⟨x, hx, hrank⟩ := hB.2 i
  have hle : x ≤ D.marker j := hsub hx j hx
  have hrle := R.strictMono.monotone hle
  rw [hrank] at hrle
  exact hi.not_ge hrle

end BranchMarkers

end ZFVP.Schmerl
