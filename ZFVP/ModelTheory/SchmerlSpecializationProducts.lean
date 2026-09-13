import ZFVP.ModelTheory.SchmerlSpecializingForcing
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sum.Order

/-! Disjoint tree sums and products of finite strict-specialization forcings.
The product chain condition is the combinatorial input for the no-new-branch
theorem for forcings whose square is ccc.
-/

namespace ZFVP.Schmerl

open Set

universe u v w

/-- A disjoint sum of tree orders is a tree order. -/
theorem sigma_tree {J : Type u} {S : J → Type v} [∀ j, PartialOrder (S j)]
    (hS : ∀ j, IsTreeOrder (S j)) : IsTreeOrder (Sigma S) := by
  rintro _ _ _ ⟨j, x, z, hxz⟩ ⟨_, y, _, hyz⟩
  exact (hS j hxz hyz).imp (Sigma.LE.fiber j x y) (Sigma.LE.fiber j y x)

/-- Every chain in a disjoint sum lies in one summand. Therefore countability
of chains is preserved even for an uncountable family of summands. -/
theorem sigma_chain_countable {J : Type u} {S : J → Type v} [∀ j, PartialOrder (S j)]
    (hS : ∀ j, ∀ C : Set (S j), IsChain (· ≤ ·) C → C.Countable)
    {C : Set (Sigma S)} (hC : IsChain (· ≤ ·) C) : C.Countable := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | ⟨⟨j, a⟩, ha⟩
  · exact Set.countable_empty
  have hfiber : IsChain (· ≤ ·) {x : S j | Sigma.mk j x ∈ C} := by
    intro x hx y hy _
    exact (hC.total hx hy).imp Sigma.mk_le_mk_iff.mp Sigma.mk_le_mk_iff.mp
  apply ((hS j _ hfiber).image (Sigma.mk j)).mono
  rintro ⟨k, x⟩ hx
  have hkj : k = j := by
    rcases hC.total hx ha with h | h
    · exact (Sigma.le_def.mp h).choose
    · exact (Sigma.le_def.mp h).choose.symm
  subst k
  exact ⟨x, hx, rfl⟩

/-- The finite-support simultaneous specialization of any family of trees with
countable chains is ccc, represented as specialization of their disjoint sum. -/
theorem sigma_specialization_ccc {J : Type u} {S : J → Type v} [∀ j, PartialOrder (S j)]
    (htree : ∀ j, IsTreeOrder (S j))
    (hchains : ∀ j, ∀ C : Set (S j), IsChain (· ≤ ·) C → C.Countable)
    (A : Set (StrictCondition (Sigma S)))
    (hA : A.Pairwise (fun p q ↦ ¬ StrictCondition.Compatible p q)) : A.Countable :=
  StrictCondition.countable_antichains (sigma_tree htree)
    (fun _ hC ↦ sigma_chain_countable hchains hC) A hA

variable {T : Type u} {S : Type v} [PartialOrder T] [PartialOrder S]

theorem sum_tree (hT : IsTreeOrder T) (hS : IsTreeOrder S) : IsTreeOrder (T ⊕ S) := by
  intro x y z hxz hyz
  cases x <;> cases y <;> cases z <;>
    simp only [Sum.inl_le_inl_iff, Sum.inr_le_inr_iff,
      Sum.not_inl_le_inr, Sum.not_inr_le_inl] at hxz hyz ⊢
  · exact hT hxz hyz
  · exact hS hxz hyz

theorem sum_chain_countable
    (hT : ∀ C : Set T, IsChain (· ≤ ·) C → C.Countable)
    (hS : ∀ C : Set S, IsChain (· ≤ ·) C → C.Countable)
    {C : Set (T ⊕ S)} (hC : IsChain (· ≤ ·) C) : C.Countable := by
  have hleft : IsChain (· ≤ ·) {x : T | Sum.inl x ∈ C} := by
    intro x hx y hy _
    exact (hC.total hx hy).imp Sum.inl_le_inl_iff.mp Sum.inl_le_inl_iff.mp
  have hright : IsChain (· ≤ ·) {x : S | Sum.inr x ∈ C} := by
    intro x hx y hy _
    exact (hC.total hx hy).imp Sum.inr_le_inr_iff.mp Sum.inr_le_inr_iff.mp
  apply (((hT _ hleft).image Sum.inl).union ((hS _ hright).image Sum.inr)).mono
  intro x hx
  cases x with
  | inl x => exact Or.inl ⟨x, hx, rfl⟩
  | inr x => exact Or.inr ⟨x, hx, rfl⟩

namespace StrictCondition

/-- Put two finite conditions on disjoint copies of their trees. -/
def pair (p : StrictCondition T) (q : StrictCondition S) : StrictCondition (T ⊕ S) :=
  ofGraph (((fun a : T × ℕ ↦ (Sum.inl a.1, a.2)) '' p.graph) ∪
    ((fun a : S × ℕ ↦ (Sum.inr a.1, a.2)) '' q.graph))
    ((p.finite.image _).union (q.finite.image _))
    (by
      intro x m n hm hn
      cases x with
      | inl x =>
          simp only [Set.mem_union, Set.mem_image, Prod.exists, Prod.mk.injEq,
            Sum.inl.injEq, Sum.inr_ne_inl, false_and, and_false,
            exists_false, or_false, exists_eq_right_right, exists_eq_right] at hm hn
          exact p.functional hm hn
      | inr x =>
          simp only [Set.mem_union, Set.mem_image, Prod.exists, Prod.mk.injEq,
            Sum.inr.injEq, Sum.inl_ne_inr, false_and, and_false,
            exists_false, false_or, exists_eq_right_right, exists_eq_right] at hm hn
          exact q.functional hm hn)
    (by
      intro x y n hx hy hxy
      cases x <;> cases y <;>
        simp only [Sum.inl_le_inl_iff, Sum.inr_le_inr_iff,
          Sum.not_inl_le_inr, Sum.not_inr_le_inl] at hxy
      · simp only [Set.mem_union, Set.mem_image, Prod.exists, Prod.mk.injEq,
          Sum.inl.injEq, Sum.inr_ne_inl, false_and, and_false,
          exists_false, or_false, exists_eq_right_right, exists_eq_right] at hx hy
        exact congrArg Sum.inl (p.strict hx hy hxy)
      · simp only [Set.mem_union, Set.mem_image, Prod.exists, Prod.mk.injEq,
          Sum.inr.injEq, Sum.inl_ne_inr, false_and, and_false,
          exists_false, false_or, exists_eq_right_right, exists_eq_right] at hx hy
        exact congrArg Sum.inr (q.strict hx hy hxy))

@[simp] theorem mem_pair_inl (p : StrictCondition T) (q : StrictCondition S) (x : T) (n : ℕ) :
    (Sum.inl x, n) ∈ (pair p q).graph ↔ (x, n) ∈ p.graph := by
  simp only [pair, graph, ofGraph, Set.mem_union, Set.mem_image, Prod.exists, Prod.mk.injEq,
    Sum.inl.injEq, Sum.inr_ne_inl, false_and, and_false, exists_false, or_false,
    exists_eq_right_right, exists_eq_right]

@[simp] theorem mem_pair_inr (p : StrictCondition T) (q : StrictCondition S) (x : S) (n : ℕ) :
    (Sum.inr x, n) ∈ (pair p q).graph ↔ (x, n) ∈ q.graph := by
  simp only [pair, graph, ofGraph, Set.mem_union, Set.mem_image, Prod.exists, Prod.mk.injEq,
    Sum.inr.injEq, Sum.inl_ne_inr, false_and, and_false, exists_false, false_or,
    exists_eq_right_right, exists_eq_right]

theorem pair_injective : Function.Injective
    (fun p : StrictCondition T × StrictCondition S ↦ pair p.1 p.2) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ heq
  have hg := congrArg graph heq
  apply Prod.ext
  · apply ext
    apply Set.ext
    rintro ⟨x, n⟩
    simpa only [mem_pair_inl] using Set.ext_iff.mp hg (Sum.inl x, n)
  · apply ext
    apply Set.ext
    rintro ⟨x, n⟩
    simpa only [mem_pair_inr] using Set.ext_iff.mp hg (Sum.inr x, n)

theorem pair_le_pair_iff {p p' : StrictCondition T} {q q' : StrictCondition S} :
    pair p q ≤ pair p' q' ↔ p ≤ p' ∧ q ≤ q' := by
  constructor
  · intro h
    constructor
    · rintro ⟨x, n⟩ hx
      exact (mem_pair_inl p q x n).mp (h ((mem_pair_inl p' q' x n).mpr hx))
    · rintro ⟨x, n⟩ hx
      exact (mem_pair_inr p q x n).mp (h ((mem_pair_inr p' q' x n).mpr hx))
  · rintro ⟨hp, hq⟩ ⟨x, n⟩ hx
    cases x with
    | inl x => exact (mem_pair_inl p q x n).mpr (hp ((mem_pair_inl p' q' x n).mp hx))
    | inr x => exact (mem_pair_inr p q x n).mpr (hq ((mem_pair_inr p' q' x n).mp hx))

/-- Tagged union preserves and reflects compatibility of pairs of conditions. -/
theorem pair_compatible_iff {p p' : StrictCondition T} {q q' : StrictCondition S} :
    Compatible (pair p q) (pair p' q') ↔ Compatible p p' ∧ Compatible q q' := by
  constructor
  · intro h
    obtain ⟨hfun, hstrict⟩ := compatible_iff.mp h
    constructor
    · apply compatible_iff.mpr
      constructor
      · intro x m n hm hn
        exact hfun (Sum.inl x) m n ((mem_pair_inl p q x m).mpr hm)
          ((mem_pair_inl p' q' x n).mpr hn)
      · intro x y n hx hy hxy
        apply Sum.inl_injective
        exact hstrict (Sum.inl x) (Sum.inl y) n ((mem_pair_inl p q x n).mpr hx)
          ((mem_pair_inl p' q' y n).mpr hy)
          (hxy.imp Sum.inl_le_inl_iff.mpr Sum.inl_le_inl_iff.mpr)
    · apply compatible_iff.mpr
      constructor
      · intro x m n hm hn
        exact hfun (Sum.inr x) m n ((mem_pair_inr p q x m).mpr hm)
          ((mem_pair_inr p' q' x n).mpr hn)
      · intro x y n hx hy hxy
        apply Sum.inr_injective
        exact hstrict (Sum.inr x) (Sum.inr y) n ((mem_pair_inr p q x n).mpr hx)
          ((mem_pair_inr p' q' y n).mpr hy)
          (hxy.imp Sum.inr_le_inr_iff.mpr Sum.inr_le_inr_iff.mpr)
  · rintro ⟨⟨s, hsp, hsp'⟩, ⟨t, htq, htq'⟩⟩
    exact ⟨pair s t, pair_le_pair_iff.mpr ⟨hsp, htq⟩,
      pair_le_pair_iff.mpr ⟨hsp', htq'⟩⟩

/-- Products of two finite strict-specialization forcings satisfy ccc. In
particular, each such forcing has ccc square. -/
theorem product_countable_antichains (htree : IsTreeOrder T) (stree : IsTreeOrder S)
    (hchains : ∀ C : Set T, IsChain (· ≤ ·) C → C.Countable)
    (schains : ∀ C : Set S, IsChain (· ≤ ·) C → C.Countable)
    (A : Set (StrictCondition T × StrictCondition S))
    (hA : A.Pairwise (fun p q ↦ ¬ ∃ r, r ≤ p ∧ r ≤ q)) : A.Countable := by
  let f (p : StrictCondition T × StrictCondition S) := pair p.1 p.2
  have hanti : (f '' A).Pairwise (fun p q ↦ ¬ Compatible p q) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne hcomp
    obtain ⟨⟨s, hsp, hsq⟩, ⟨t, htp, htq⟩⟩ := pair_compatible_iff.mp hcomp
    exact hA hp hq (fun heq ↦ hne (congrArg f heq))
      ⟨(s, t), ⟨hsp, htp⟩, ⟨hsq, htq⟩⟩
  exact Set.countable_of_injective_of_countable_image pair_injective.injOn
    (countable_antichains (sum_tree htree stree)
      (fun _ hC ↦ sum_chain_countable hchains schains hC) _ hanti)

end StrictCondition

end ZFVP.Schmerl
