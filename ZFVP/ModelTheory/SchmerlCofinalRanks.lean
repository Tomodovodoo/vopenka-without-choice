import ZFVP.ModelTheory.SchmerlAronszajnCore

/-! Restrict ranked trees to a cofinal sequence of ranks. This is needed for
the class tree of a possibly ill-founded model: its ordinal rank order has
omega-one cofinality but need not have countable initial segments. Restricting
to cofinally many ranks preserves the branch set exactly.
-/

namespace ZFVP.Schmerl

open Set Order Cardinal

universe u v w

/-- Every linear order of cofinality aleph-one has a strictly increasing
cofinal omega-one sequence, constructed without assuming countable initial
segments of the original order. -/
theorem exists_omegaOne_cofinal_embedding {I : Type v} [LinearOrder I]
    (hI : Order.cof I = Cardinal.aleph 1) :
    ∃ c : Ordinal.ToType (Ordinal.omega.{v} 1) ↪o I, IsCofinal (Set.range c) := by
  classical
  let Ω := Ordinal.ToType (Ordinal.omega.{v} 1)
  have hunc : Cardinal.aleph0 < Order.cof I := by
    rw [hI]; exact Cardinal.aleph0_lt_aleph_one
  obtain ⟨A, hAcof, hAcard⟩ := Order.exists_cof_eq I
  obtain ⟨e⟩ : Nonempty (A ≃ Ω) := Cardinal.eq.mp (by
    rw [hAcard, hI, Cardinal.mk_toType, Ordinal.card_omega])
  have step (j : Ω) (previous : ∀ i, i < j → I) :
      ∃ x : I, (e.symm j).val < x ∧ ∀ i (hij : i < j), previous i hij < x := by
    let : Countable (Set.Iio j) := (omegaOne_initial_countable j).to_subtype
    obtain ⟨x, hx⟩ := exists_bound_of_countable hunc
      ((Set.countable_range (fun i : Set.Iio j ↦ previous i i.property)).union
        (Set.countable_singleton (e.symm j).val))
    exact ⟨x, hx _ (Or.inr (Set.mem_singleton _)),
      fun i hij ↦ hx _ (Or.inl (Set.mem_range_self (show Set.Iio j from ⟨i, hij⟩)))⟩
  choose pick hpick using step
  let run : Ω → I := wellFounded_lt.fix pick
  have hrun (j : Ω) : (e.symm j).val < run j ∧ ∀ i, i < j → run i < run j := by
    have heq : run j = pick j (fun i _ ↦ run i) := WellFounded.fix_eq wellFounded_lt pick j
    rw [heq]
    exact hpick j (fun i _ ↦ run i)
  refine ⟨OrderEmbedding.ofStrictMono run (fun i j hij ↦ (hrun j).2 i hij), ?_⟩
  intro i
  obtain ⟨a, ha, hia⟩ := hAcof i
  refine ⟨run (e ⟨a, ha⟩), ⟨e ⟨a, ha⟩, rfl⟩, hia.trans ?_⟩
  simpa only [Equiv.symm_apply_apply] using (hrun (e ⟨a, ha⟩)).1.le

variable {T : Type u} {I : Type v} {K : Type w}
  [PartialOrder T] [LinearOrder I] [LinearOrder K]

namespace RankedTree

variable (R : RankedTree T I) (c : K ↪o I)

/-- Nodes on the selected ranks. -/
def RankRestriction := {x : T // R.rank x ∈ Set.range c}

instance : PartialOrder (R.RankRestriction c) := inferInstanceAs (PartialOrder (Subtype _))

/-- The selected-rank index of a restricted node. -/
noncomputable def restrictedRank (x : R.RankRestriction c) : K :=
  Classical.choose x.property

@[simp] theorem coe_restrictedRank (x : R.RankRestriction c) :
    c (R.restrictedRank c x) = R.rank x.val := Classical.choose_spec x.property

/-- A ranked tree on a cofinal family of selected levels. -/
noncomputable def restrictRanks : RankedTree (R.RankRestriction c) K where
  tree := by
    intro x y z hx hy
    exact R.tree hx hy
  rank := R.restrictedRank c
  strictMono := by
    intro x y hxy
    apply c.lt_iff_lt.mp
    simpa only [coe_restrictedRank] using R.strictMono hxy
  onto := by
    intro k
    obtain ⟨x, hx⟩ := R.onto (c k)
    refine ⟨⟨x, ⟨k, hx.symm⟩⟩, ?_⟩
    apply c.injective
    exact (R.coe_restrictedRank c _).trans hx
  predecessor := by
    intro x k hk
    have hkr : c k < R.rank x.val := by
      rw [← R.coe_restrictedRank c x]
      exact c.strictMono hk
    obtain ⟨y, hyx, hyr⟩ := R.predecessor x.val (c k) hkr
    refine ⟨⟨y, ⟨k, hyr.symm⟩⟩, hyx, ?_⟩
    apply c.injective
    exact (R.coe_restrictedRank c _).trans hyr

/-- Restriction of a branch to the selected ranks. -/
def restrictBranch (B : Set T) : Set (R.RankRestriction c) := {x | x.val ∈ B}

theorem restrictBranch_isBranch {B : Set T} (hB : R.IsBranch B) :
    (R.restrictRanks c).IsBranch (R.restrictBranch c B) := by
  refine ⟨fun x hx y hy _ ↦ hB.1.total hx hy, ?_⟩
  intro k
  obtain ⟨x, hx, hxrank⟩ := hB.2 (c k)
  refine ⟨⟨x, ⟨k, hxrank.symm⟩⟩, hx, ?_⟩
  change R.restrictedRank c ⟨x, ⟨k, hxrank.symm⟩⟩ = k
  apply c.injective
  exact (R.coe_restrictedRank c ⟨x, ⟨k, hxrank.symm⟩⟩).trans hxrank

/-- Expand a restricted branch by downward closure in the original tree. -/
def expandBranch (B : Set (R.RankRestriction c)) : Set T :=
  {x | ∃ y ∈ B, x ≤ y.val}

theorem expandBranch_isBranch (hcof : IsCofinal (Set.range c))
    {B : Set (R.RankRestriction c)} (hB : (R.restrictRanks c).IsBranch B) :
    R.IsBranch (R.expandBranch c B) := by
  apply R.isBranch_of_cofinal_rank
  · rintro x ⟨a, ha, hxa⟩ y ⟨b, hb, hyb⟩ _
    rcases hB.1.total ha hb with hab | hba
    · exact R.tree (hxa.trans hab) hyb
    · exact R.tree hxa (hyb.trans hba)
  · rintro x y ⟨z, hz, hyz⟩ hxy
    exact ⟨z, hz, hxy.trans hyz⟩
  · intro i
    obtain ⟨_, ⟨k, rfl⟩, hik⟩ := hcof i
    obtain ⟨x, hx, hxrank⟩ := hB.2 k
    change R.restrictedRank c x = k at hxrank
    refine ⟨R.rank x.val, ⟨x.val, ⟨x, hx, le_rfl⟩, rfl⟩, hik.trans_eq ?_⟩
    exact (congrArg c hxrank).symm.trans (R.coe_restrictedRank c x)

theorem expand_restrictBranch (hcof : IsCofinal (Set.range c))
    {B : Set T} (hB : R.IsBranch B) :
    R.expandBranch c (R.restrictBranch c B) = B := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, hxy⟩
    exact branch_downward_closed R.tree hB.isMaxChain hy hxy
  · intro x hx
    obtain ⟨_, ⟨k, rfl⟩, hxk⟩ := hcof (R.rank x)
    obtain ⟨y, hy, hyrank⟩ := hB.2 (c k)
    refine ⟨⟨y, ⟨k, hyrank.symm⟩⟩, hy, ?_⟩
    apply (R.le_iff_rank_le hB.1 hx hy).mpr
    exact hxk.trans_eq hyrank.symm

theorem restrict_expandBranch {B : Set (R.RankRestriction c)}
    (hB : (R.restrictRanks c).IsBranch B) :
    R.restrictBranch c (R.expandBranch c B) = B := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, hxy⟩
    exact branch_downward_closed (R.restrictRanks c).tree hB.isMaxChain hy hxy
  · intro x hx
    exact ⟨x, hx, le_rfl⟩

/-- Cofinal rank restriction preserves the complete branch set. -/
noncomputable def branchRestrictionEquiv (hcof : IsCofinal (Set.range c)) :
    {B : Set T // R.IsBranch B} ≃
      {B : Set (R.RankRestriction c) // (R.restrictRanks c).IsBranch B} where
  toFun B := ⟨R.restrictBranch c B.val, R.restrictBranch_isBranch c B.property⟩
  invFun B := ⟨R.expandBranch c B.val, R.expandBranch_isBranch c hcof B.property⟩
  left_inv B := Subtype.ext (R.expand_restrictBranch c hcof B.property)
  right_inv B := Subtype.ext (R.restrict_expandBranch c B.property)

end RankedTree

end ZFVP.Schmerl
