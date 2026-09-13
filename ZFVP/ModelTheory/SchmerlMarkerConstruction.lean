import ZFVP.ModelTheory.SchmerlBranchMarkers

/-! Construction of the separated branch markers used by Baumgartner's reduction.
At each countable stage choose a node above earlier markers and past the split
from each earlier branch. Uncountable rank cofinality supplies the bound.
-/

namespace ZFVP.Schmerl

open Set Order Cardinal

universe u v w

variable {T : Type u} {I : Type v} [PartialOrder T] [LinearOrder I]

/-- Countable sets are strictly bounded in an order of uncountable cofinality. -/
theorem exists_bound_of_countable (hI : Cardinal.aleph0 < Order.cof I)
    {A : Set I} (hA : A.Countable) : ∃ i, ∀ a ∈ A, a < i := by
  apply not_isCofinal_iff.mp
  intro hcof
  have : Cardinal.mk A ≤ Cardinal.aleph0 := by
    let : Countable A := hA.to_subtype
    exact Cardinal.mk_le_aleph0
  exact (hI.trans_le (Order.cof_le hcof)).not_ge this

namespace RankedTree

theorem IsBranch.exists_mem_not_mem {R : RankedTree T I} {A B : Set T}
    (hA : R.IsBranch A) (hB : R.IsBranch B) (hne : A ≠ B) : ∃ x ∈ A, x ∉ B := by
  apply Set.not_subset.mp
  intro hsub
  exact hne (hA.isMaxChain.2 hB.1 hsub)

end RankedTree

variable {R : RankedTree T I} {J : Type w} [LinearOrder J]

/-- The successor construction works for arbitrary previous choices. -/
theorem exists_branch_marker_step (hI : Cardinal.aleph0 < Order.cof I)
    (B : J → Set T) (hB : ∀ j, R.IsBranch (B j)) (hinj : Function.Injective B)
    (j : J) (hsmall : (Set.Iio j).Countable) (previous : Set.Iio j → T) :
    ∃ x ∈ B j, ∀ i : Set.Iio j, R.rank (previous i) < R.rank x ∧ x ∉ B i := by
  classical
  let : Countable (Set.Iio j) := hsmall.to_subtype
  have hsplit : ∀ i : Set.Iio j, ∃ x ∈ B j, x ∉ B i := by
    intro i
    exact (hB j).exists_mem_not_mem (hB i) (fun heq ↦ i.property.ne' (hinj heq))
  choose split hsplit_mem hsplit_not using hsplit
  let bounds : Set I := Set.range (fun i ↦ R.rank (previous i)) ∪
    Set.range (fun i ↦ R.rank (split i))
  have hbounds : bounds.Countable :=
    (Set.countable_range _).union (Set.countable_range _)
  obtain ⟨l, hl⟩ := exists_bound_of_countable hI hbounds
  obtain ⟨x, hx, hrank⟩ := (hB j).2 l
  refine ⟨x, hx, ?_⟩
  intro i
  refine ⟨by rw [hrank]; exact hl _ (Or.inl (Set.mem_range_self i)), ?_⟩
  intro hxi
  have hsplit_lt : R.rank (split i) < R.rank x := by
    rw [hrank]
    exact hl _ (Or.inr (Set.mem_range_self i))
  have hle : split i ≤ x :=
    (R.le_iff_rank_le (hB j).1 (hsplit_mem i) hx).mpr hsplit_lt.le
  exact hsplit_not i (branch_downward_closed R.tree (hB i).isMaxChain hxi hle)

/-- Construct separated markers for any injectively indexed branch family whose
index order is well founded and has countable initial segments. This includes
all families of at most omega-one branches after choosing their enumeration. -/
theorem exists_branchMarkers [WellFoundedLT J] (hI : Cardinal.aleph0 < Order.cof I)
    (B : J → Set T) (hB : ∀ j, R.IsBranch (B j)) (hinj : Function.Injective B)
    (hsmall : ∀ j : J, (Set.Iio j).Countable) :
    ∃ D : BranchMarkers R J, D.branch = B := by
  classical
  have step (j : J) (previous : ∀ i, i < j → T) :
      ∃ x ∈ B j, ∀ i (hij : i < j), R.rank (previous i hij) < R.rank x ∧ x ∉ B i := by
    obtain ⟨x, hx, h⟩ := exists_branch_marker_step hI B hB hinj j (hsmall j)
      (fun i ↦ previous i i.property)
    exact ⟨x, hx, fun i hij ↦ h ⟨i, hij⟩⟩
  choose pick hpick using step
  let run : J → T := wellFounded_lt.fix pick
  have hrun (j : J) : run j ∈ B j ∧
      ∀ i, i < j → R.rank (run i) < R.rank (run j) ∧ run j ∉ B i := by
    have heq : run j = pick j (fun i _ ↦ run i) := WellFounded.fix_eq wellFounded_lt pick j
    rw [heq]
    exact hpick j (fun i _ ↦ run i)
  have hstrict : StrictMono (R.rank ∘ run) := fun i j hij ↦ ((hrun j).2 i hij).1
  refine ⟨{ branch := B
            isBranch := hB
            marker := run
            marker_mem := fun j ↦ (hrun j).1
            injective := fun i j hij ↦ hstrict.injective (congrArg R.rank hij)
            separates := ?_ }, rfl⟩
  intro i j hij
  have hrij := R.strictMono hij
  have hij' : i < j := hstrict.lt_iff_lt.mp hrij
  exact ((hrun j).2 i hij').2

omit [LinearOrder J] in
/-- Baumgartner's marker construction for an arbitrary family of at most
aleph-one distinct branches. The well-order and countable-stage condition are
chosen from the cardinal bound rather than assumed separately. -/
theorem exists_branchMarkers_of_card_le (hI : Cardinal.aleph0 < Order.cof I)
    (B : J → Set T) (hB : ∀ j, R.IsBranch (B j)) (hinj : Function.Injective B)
    (hcard : Cardinal.mk J ≤ Cardinal.aleph 1) :
    ∃ D : BranchMarkers R J, D.branch = B := by
  classical
  let Ω : Type w := Ordinal.ToType (Ordinal.omega.{w} 1)
  have hΩ : Cardinal.mk Ω = Cardinal.aleph 1 := by
    rw [Cardinal.mk_toType, Ordinal.card_omega]
  obtain ⟨e⟩ : Nonempty (J ↪ Ω) := (Cardinal.le_def J Ω).mp (hcard.trans_eq hΩ.symm)
  let : LinearOrder J := LinearOrder.lift' e e.injective
  let : WellFoundedLT J := ⟨InvImage.wf e wellFounded_lt⟩
  have hsmallΩ (a : Ω) : (Set.Iio a).Countable := by
    have hord : (Cardinal.mk Ω).ord = Ordinal.type (fun x y : Ω ↦ x < y) := by
      rw [hΩ, Cardinal.ord_aleph]
      exact (Ordinal.type_toType _).symm
    have hlt : Cardinal.mk (Set.Iio a) < Cardinal.aleph 1 := by
      simpa only [hΩ] using Cardinal.mk_Iio_lt a hord
    exact Set.countable_coe_iff.mp
      (Cardinal.mk_le_aleph0_iff.mp (Cardinal.lt_aleph_one_iff.mp hlt))
  apply exists_branchMarkers hI B hB hinj
  intro j
  exact (hsmallΩ (e j)).preimage e.injective

end ZFVP.Schmerl
