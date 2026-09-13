import ZFVP.ModelTheory.SchmerlSpecializationProducts

/-! The combinatorial no-new-branch theorem for a forcing with ccc square.
A cofinal branch name is represented by its monotone node-forcing relation,
the local chain clause, and dense cofinal decisions. From these local clauses
we prove that densely many conditions decide one ground branch. This is the
name-level argument underlying Friedman, *Trees, Reflection and Approachability*,
Lemma 12(a).
-/

namespace ZFVP.Schmerl

open Set Order

universe u v w

namespace Poset

variable {P : Type u} [Preorder P]

def Compatible (p q : P) : Prop := ∃ r, r ≤ p ∧ r ≤ q

theorem compatible_self (p : P) : Compatible p p := ⟨p, le_rfl, le_rfl⟩

theorem compatible_symm {p q : P} (h : Compatible p q) : Compatible q p := by
  obtain ⟨r, hrp, hrq⟩ := h
  exact ⟨r, hrq, hrp⟩

theorem compatible_of_le_left {p q r : P} (hpq : p ≤ q)
    (h : Compatible p r) : Compatible q r := by
  obtain ⟨s, hsp, hsr⟩ := h
  exact ⟨s, hsp.trans hpq, hsr⟩

/-- A maximal antichain in any specified set is predense in that set. -/
theorem exists_predense_antichain (S : Set P) :
    ∃ A ⊆ S, A.Pairwise (fun p q ↦ ¬ Compatible p q) ∧
      ∀ p ∈ S, ∃ q ∈ A, Compatible p q := by
  classical
  let F : Set (Set P) := {A | A ⊆ S ∧ A.Pairwise (fun p q ↦ ¬ Compatible p q)}
  obtain ⟨A, hA, hmax⟩ := zorn_subset F (by
    intro C hCF hC
    refine ⟨⋃₀ C, ⟨?_, ?_⟩, fun D hD ↦ Set.subset_sUnion_of_mem hD⟩
    · rintro p ⟨D, hD, hp⟩
      exact (hCF hD).1 hp
    · rintro p ⟨D, hD, hp⟩ q ⟨E, hE, hq⟩ hpq
      rcases hC.total hD hE with hDE | hED
      · exact (hCF hE).2 (hDE hp) hq hpq
      · exact (hCF hD).2 hp (hED hq) hpq)
  refine ⟨A, hA.1, hA.2, ?_⟩
  intro p hp
  by_contra hn
  have hnone : ∀ q ∈ A, ¬ Compatible p q := by
    simpa only [not_exists, not_and] using hn
  have hinsert : Set.insert p A ∈ F := by
    refine ⟨Set.insert_subset hp hA.1, hA.2.insert ?_⟩
    intro q hq _
    exact ⟨hnone q hq, fun h ↦ hnone q hq (compatible_symm h)⟩
  have hpA : p ∈ A := hmax hinsert (Set.subset_insert p A) (Set.mem_insert p A)
  exact hnone p hpA (compatible_self p)

end Poset

variable {P : Type u} [Preorder P]
variable {T : Type v} {I : Type w} [PartialOrder T] [LinearOrder I]

/-- The local semantic clauses for a name forced to be a cofinal branch.
They assert monotonicity, coherence at each condition, and dense node decisions.
The global branch-preservation conclusion is proved from these clauses below. -/
structure CofinalBranchName (P : Type u) [Preorder P] (R : RankedTree T I) where
  forces : P → T → Prop
  monotone : ∀ ⦃p q⦄, p ≤ q → ∀ x, forces q x → forces p x
  chain : ∀ p, IsChain (· ≤ ·) {x | forces p x}
  cofinal : ∀ p i, ∃ q ≤ p, ∃ x, forces q x ∧ i ≤ R.rank x

namespace CofinalBranchName

variable {R : RankedTree T I} (N : CofinalBranchName P R)

theorem comparable_of_compatible {p q : P} (hpq : Poset.Compatible p q)
    {x y : T} (hx : N.forces p x) (hy : N.forces q y) : x ≤ y ∨ y ≤ x := by
  obtain ⟨r, hrp, hrq⟩ := hpq
  exact (N.chain r).total (N.monotone hrp x hx) (N.monotone hrq y hy)

/-- Nodes which some strengthening can put on the named branch. -/
def possible (p : P) : Set T := {x | ∃ q ≤ p, N.forces q x}

/-- A stabilizing condition leaves only one possible cofinal branch. -/
def Stabilizes (p : P) : Prop := IsChain (· ≤ ·) (N.possible p)

/-- Product conditions that already force the two branch copies apart. -/
def splits : Set (P × P) := {p | ∃ x y, N.forces p.1 x ∧ N.forces p.2 y ∧
  ¬ (x ≤ y ∨ y ≤ x)}

/-- If the forcing square is ccc and rank cofinality is uncountable, densely
many conditions stabilize the branch name. No global preservation property is
assumed as an input. -/
theorem stabilizes_dense (hI : Cardinal.aleph0 < Order.cof I)
    (hccc : ∀ A : Set (P × P), A.Pairwise (fun p q ↦ ¬ Poset.Compatible p q) →
      A.Countable) (p : P) : ∃ q ≤ p, N.Stabilizes q := by
  classical
  obtain ⟨A, hAsplit, hanti, hpredense⟩ := Poset.exists_predense_antichain N.splits
  have hcount := hccc A hanti
  let : Countable A := hcount.to_subtype
  have hsplit (a : A) : ∃ x y, N.forces a.val.1 x ∧ N.forces a.val.2 y ∧
      ¬ (x ≤ y ∨ y ≤ x) := hAsplit a.property
  choose left right hleft hright hincomp using hsplit
  obtain ⟨i, hi⟩ := exists_bound_of_countable hI
    ((Set.countable_range (fun a ↦ R.rank (left a))).union
      (Set.countable_range (fun a ↦ R.rank (right a))))
  obtain ⟨q, hqp, z, hqz, hiz⟩ := N.cofinal p i
  have hnone : ∀ a ∈ A, ¬ Poset.Compatible (q, q) a := by
    intro a ha hqa
    obtain ⟨s, hsq, hsa⟩ := hqa
    have hl := N.comparable_of_compatible ⟨s.1, hsa.1, hsq.1⟩ (hleft ⟨a, ha⟩) hqz
    have hr := N.comparable_of_compatible ⟨s.2, hsa.2, hsq.2⟩ (hright ⟨a, ha⟩) hqz
    have hlrank : R.rank (left ⟨a, ha⟩) < R.rank z :=
      (hi _ (Or.inl (Set.mem_range_self ⟨a, ha⟩))).trans_le hiz
    have hrrank : R.rank (right ⟨a, ha⟩) < R.rank z :=
      (hi _ (Or.inr (Set.mem_range_self ⟨a, ha⟩))).trans_le hiz
    have hlz := hl.resolve_right (fun h ↦ hlrank.not_ge (R.strictMono.monotone h))
    have hrz := hr.resolve_right (fun h ↦ hrrank.not_ge (R.strictMono.monotone h))
    exact hincomp ⟨a, ha⟩ (R.tree hlz hrz)
  refine ⟨q, hqp, ?_⟩
  rintro x ⟨r, hrq, hrx⟩ y ⟨s, hsq, hsy⟩ _
  by_contra hxy
  obtain ⟨a, ha, hcomp⟩ := hpredense (r, s) ⟨x, y, hrx, hsy, hxy⟩
  exact hnone a ha (Poset.compatible_of_le_left ⟨hrq, hsq⟩ hcomp)

/-- The ground branch selected by a stabilizing condition. -/
def decidedBranch (p : P) : Set T := {x | ∃ y ∈ N.possible p, x ≤ y}

theorem decidedBranch_isBranch {p : P} (hp : N.Stabilizes p) :
    R.IsBranch (N.decidedBranch p) := by
  apply R.downClosure_isBranch hp
  intro i
  obtain ⟨q, hqp, x, hx, hix⟩ := N.cofinal p i
  exact ⟨R.rank x, ⟨x, ⟨q, hqp, hx⟩, rfl⟩, hix⟩

theorem forced_mem_decidedBranch {p q : P} (hqp : q ≤ p) {x : T}
    (hx : N.forces q x) : x ∈ N.decidedBranch p :=
  ⟨x, ⟨q, hqp, hx⟩, le_rfl⟩

/-- Interpret a branch name through a directed family of conditions. The
downward closure is included so that this is a set of all branch nodes. -/
def interpretation (G : Set P) : Set T :=
  {x | ∃ p ∈ G, ∃ y, N.forces p y ∧ x ≤ y}

theorem interpretation_isChain {G : Set P} (hG : DirectedOn (· ≥ ·) G) :
    IsChain (· ≤ ·) (N.interpretation G) := by
  rintro x ⟨p, hp, a, ha, hxa⟩ y ⟨q, hq, b, hb, hyb⟩ _
  obtain ⟨r, _, hrp, hrq⟩ := hG p hp q hq
  have hab := N.comparable_of_compatible ⟨r, hrp, hrq⟩ ha hb
  rcases hab with hab | hba
  · exact R.tree (hxa.trans hab) hyb
  · exact R.tree hxa (hyb.trans hba)

theorem interpretation_isBranch {G : Set P} (hG : DirectedOn (· ≥ ·) G)
    (hmeets : ∀ i, ∃ p ∈ G, ∃ x, N.forces p x ∧ i ≤ R.rank x) :
    R.IsBranch (N.interpretation G) := by
  apply R.isBranch_of_cofinal_rank (N.interpretation_isChain hG)
  · rintro x y ⟨p, hp, z, hz, hyz⟩ hxy
    exact ⟨p, hp, z, hz, hxy.trans hyz⟩
  · intro i
    obtain ⟨p, hp, x, hx, hix⟩ := hmeets i
    exact ⟨R.rank x, ⟨x, ⟨p, hp, x, hx, le_rfl⟩, rfl⟩, hix⟩

/-- Once the directed family meets the dense stabilizing set, its interpreted
branch equals the ground branch attached to that condition. -/
theorem interpretation_eq_decidedBranch {G : Set P} (hG : DirectedOn (· ≥ ·) G)
    (hmeets : ∀ i, ∃ p ∈ G, ∃ x, N.forces p x ∧ i ≤ R.rank x)
    {p : P} (hpG : p ∈ G) (hp : N.Stabilizes p) :
    N.interpretation G = N.decidedBranch p := by
  apply (N.interpretation_isBranch hG hmeets).isMaxChain.2
    (N.decidedBranch_isBranch hp).1
  rintro x ⟨q, hq, y, hy, hxy⟩
  obtain ⟨r, _, hrp, hrq⟩ := hG p hpG q hq
  exact ⟨y, ⟨r, hrp, N.monotone hrq y hy⟩, hxy⟩

end CofinalBranchName

end ZFVP.Schmerl
