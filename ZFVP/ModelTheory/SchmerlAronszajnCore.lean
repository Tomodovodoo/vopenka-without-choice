import ZFVP.ModelTheory.SchmerlMarkerConstruction

/-! The core of the separated-marker construction has only countable chains.
The argument applies to rank orders with countable strict initial segments;
in particular, the usual omega-one rank order satisfies the hypothesis.
-/

namespace ZFVP.Schmerl

open Set Order Cardinal

universe u v w

variable {T : Type u} {I : Type v} [PartialOrder T] [LinearOrder I]

namespace RankedTree

/-- The downward closure of a chain in a tree is a chain. -/
theorem downClosure_isChain (R : RankedTree T I) {C : Set T}
    (hC : IsChain (· ≤ ·) C) :
    IsChain (· ≤ ·) {x | ∃ y ∈ C, x ≤ y} := by
  rintro x ⟨a, ha, hxa⟩ y ⟨b, hb, hyb⟩ _
  rcases hC.total ha hb with hab | hba
  · exact R.tree (hxa.trans hab) hyb
  · exact R.tree hxa (hyb.trans hba)

/-- Every chain meeting cofinally many ranks determines a branch. -/
theorem downClosure_isBranch (R : RankedTree T I) {C : Set T}
    (hC : IsChain (· ≤ ·) C) (hcof : IsCofinal (R.rank '' C)) :
    R.IsBranch {x | ∃ y ∈ C, x ≤ y} := by
  apply R.isBranch_of_cofinal_rank (R.downClosure_isChain hC)
  · rintro x y ⟨z, hz, hyz⟩ hxy
    exact ⟨z, hz, hxy.trans hyz⟩
  · intro i
    obtain ⟨j, ⟨x, hx, rfl⟩, hij⟩ := hcof i
    exact ⟨R.rank x, ⟨x, ⟨x, hx, le_rfl⟩, rfl⟩, hij⟩

/-- A chain whose ranks are bounded is countable when rank initial segments are countable. -/
theorem countable_chain_of_not_cofinal (R : RankedTree T I)
    (hsmall : ∀ i : I, (Set.Iio i).Countable) {C : Set T}
    (hC : IsChain (· ≤ ·) C) (hcof : ¬ IsCofinal (R.rank '' C)) : C.Countable := by
  obtain ⟨i, hi⟩ := not_isCofinal_iff.mp hcof
  have himage : (R.rank '' C).Countable :=
    (hsmall i).mono (fun j hj ↦ hi j hj)
  have hinj : Set.InjOn R.rank C := by
    intro x hx y hy hxy
    apply le_antisymm
    · exact (R.le_iff_rank_le hC hx hy).mpr hxy.le
    · exact (R.le_iff_rank_le hC hy hx).mpr hxy.ge
  exact Set.countable_of_injective_of_countable_image hinj himage

end RankedTree

namespace BranchMarkers

variable {R : RankedTree T I} {J : Type w} (D : BranchMarkers R J)

/-- If all branches are marked, no chain in the core has cofinal ranks. -/
theorem core_chain_not_cofinal [NoMaxOrder I]
    (hall : ∀ B, R.IsBranch B → ∃ j, D.branch j = B)
    {C : Set T} (hC : IsChain (· ≤ ·) C) (hsub : C ⊆ D.core) :
    ¬ IsCofinal (R.rank '' C) := by
  intro hcof
  obtain ⟨j, hj⟩ := hall _ (R.downClosure_isBranch hC hcof)
  obtain ⟨i, hi⟩ := exists_gt (R.rank (D.marker j))
  obtain ⟨r, ⟨x, hx, rfl⟩, hir⟩ := hcof i
  have hmem : x ∈ D.branch j := by
    rw [hj]
    exact ⟨x, hx, le_rfl⟩
  have hle := R.strictMono.monotone (hsub hx j hmem)
  exact hi.not_ge (hir.trans hle)

/-- The unmarked core is Aronszajn: every chain is countable. -/
theorem core_chain_countable [NoMaxOrder I]
    (hsmall : ∀ i : I, (Set.Iio i).Countable)
    (hall : ∀ B, R.IsBranch B → ∃ j, D.branch j = B)
    {C : Set T} (hC : IsChain (· ≤ ·) C) (hsub : C ⊆ D.core) : C.Countable :=
  R.countable_chain_of_not_cofinal hsmall hC (D.core_chain_not_cofinal hall hC hsub)

/-- Intrinsic version for chains in the subtype of core nodes. -/
theorem core_subtype_chain_countable [NoMaxOrder I]
    (hsmall : ∀ i : I, (Set.Iio i).Countable)
    (hall : ∀ B, R.IsBranch B → ∃ j, D.branch j = B)
    {C : Set D.core} (hC : IsChain (· ≤ ·) C) : C.Countable := by
  have hchain : IsChain (· ≤ ·) (Subtype.val '' C) := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ _
    exact hC.total ha hb
  have hcount := D.core_chain_countable hsmall hall hchain
    (by rintro x ⟨a, _, rfl⟩; exact a.property)
  exact Set.countable_of_injective_of_countable_image Subtype.val_injective.injOn hcount

end BranchMarkers

/-- Countable strict initial segments of the omega-one rank order. -/
theorem omegaOne_initial_countable (a : Ordinal.ToType (Ordinal.omega.{v} 1)) :
    (Set.Iio a).Countable := by
  have hord : (Cardinal.mk (Ordinal.ToType (Ordinal.omega.{v} 1))).ord =
      Ordinal.type (fun x y : Ordinal.ToType (Ordinal.omega.{v} 1) ↦ x < y) := by
    rw [Cardinal.mk_toType, Ordinal.card_omega, Cardinal.ord_aleph]
    exact (Ordinal.type_toType _).symm
  have hlt : Cardinal.mk (Set.Iio a) < Cardinal.aleph 1 := by
    simpa only [Cardinal.mk_toType, Ordinal.card_omega] using Cardinal.mk_Iio_lt a hord
  exact Set.countable_coe_iff.mp
    (Cardinal.mk_le_aleph0_iff.mp (Cardinal.lt_aleph_one_iff.mp hlt))

/-- The branch bound suffices to construct the Aronszajn core in the
omega-one case. The exhaustive branch indexing and countable-chain property
are conclusions, rather than auxiliary assumptions on the construction. -/
theorem exists_aronszajn_core
    (R : RankedTree T (Ordinal.ToType (Ordinal.omega.{v} 1)))
    (hcard : Cardinal.mk {B : Set T // R.IsBranch B} ≤ Cardinal.aleph 1) :
    ∃ D : BranchMarkers R {B : Set T // R.IsBranch B},
      (∀ j, D.branch j = j.val) ∧
      ∀ C : Set D.core, IsChain (· ≤ ·) C → C.Countable := by
  have hI : Cardinal.aleph0 < Order.cof (Ordinal.ToType (Ordinal.omega.{v} 1)) := by
    rw [Ordinal.cof_toType, Cardinal.cof_omega_one]
    exact Cardinal.aleph0_lt_aleph_one
  let : NoMaxOrder (Ordinal.ToType (Ordinal.omega.{v} 1)) := ⟨fun i ↦ by
    obtain ⟨j, hj⟩ := exists_bound_of_countable hI (Set.countable_singleton i)
    exact ⟨j, hj i (Set.mem_singleton i)⟩⟩
  obtain ⟨D, hD⟩ := exists_branchMarkers_of_card_le hI Subtype.val
    (fun j ↦ j.property) Subtype.val_injective hcard
  refine ⟨D, fun j ↦ congrFun hD j, ?_⟩
  intro C hC
  apply D.core_subtype_chain_countable omegaOne_initial_countable _ hC
  intro B hB
  exact ⟨⟨B, hB⟩, congrFun hD ⟨B, hB⟩⟩

end ZFVP.Schmerl
