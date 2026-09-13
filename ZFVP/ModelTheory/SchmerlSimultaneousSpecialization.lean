import ZFVP.ModelTheory.SchmerlCofinalSpecialization

/-! One finite-support forcing for a whole family of ranked trees. The forcing
strictly specializes the disjoint union of their constructed Aronszajn cores.
Its square is ccc, and its directed generic union defines every branch of every
original tree by a node parameter and the selected-level predicate.
-/

namespace ZFVP.Schmerl

open Set Order

universe u v w z

variable {J : Type z} {T : J → Type u} {I : J → Type v}
  [∀ j, PartialOrder (T j)] [∀ j, LinearOrder (I j)]

theorem simultaneous_weak_coloring_of_directed
    (R : ∀ j, RankedTree (T j) (I j)) {K : J → Type w}
    (D : ∀ j, BranchMarkers (R j) (K j))
    {G : Set (StrictCondition (Σ j, (D j).core))}
    (hG : DirectedOn (· ≥ ·) G)
    (hmeets : ∀ x, ∃ p ∈ G, p ∈ StrictCondition.decides x) :
    ∃ f : ∀ j, T j → ℕ, ∀ j, WeaklySpecializes (· ≤ ·) (f j) := by
  obtain ⟨g, hg, _⟩ := StrictCondition.exists_coloring hG hmeets
  have hgj (j : J) : BranchMarkers.StrictSpecializes (fun x : (D j).core ↦ g ⟨j, x⟩) := by
    intro x y hxy
    exact hg (Sigma.mk_lt_mk_iff.mpr hxy)
  exact ⟨fun j ↦ (D j).extendColor (fun x ↦ g ⟨j, x⟩),
    fun j ↦ (D j).extendColor_weaklySpecializes (hgj j)⟩

/-- The coloring interface retains weak specialization explicitly, so it can
be used directly in the model-construction direction of the fixed sentence. -/
theorem exists_simultaneous_ccc_weak_specialization
    (R : ∀ j, RankedTree (T j) (I j))
    (hcof : ∀ j, Order.cof (I j) = Cardinal.aleph 1)
    (hcard : ∀ j, Cardinal.mk {B : Set (T j) // (R j).IsBranch B} ≤ Cardinal.aleph 1) :
    ∃ c : ∀ j, Ordinal.ToType (Ordinal.omega.{v} 1) ↪o I j,
      (∀ j, IsCofinal (Set.range (c j))) ∧
      ∃ D : ∀ j, BranchMarkers ((R j).restrictRanks (c j))
        {B : Set ((R j).RankRestriction (c j)) // ((R j).restrictRanks (c j)).IsBranch B},
        (∀ A : Set (StrictCondition (Σ j, (D j).core) × StrictCondition (Σ j, (D j).core)),
          A.Pairwise (fun p q ↦ ¬ Poset.Compatible p q) → A.Countable) ∧
        (∀ x, ∀ p : StrictCondition (Σ j, (D j).core),
          ∃ q ≤ p, q ∈ StrictCondition.decides x) ∧
        (∀ G : Set (StrictCondition (Σ j, (D j).core)), DirectedOn (· ≥ ·) G →
          (∀ x, ∃ p ∈ G, p ∈ StrictCondition.decides x) →
          ∃ f : ∀ j, (R j).RankRestriction (c j) → ℕ,
            ∀ j, WeaklySpecializes (· ≤ ·) (f j)) := by
  classical
  choose c hc using fun j ↦ exists_omegaOne_cofinal_embedding (hcof j)
  have hnewcard (j : J) : Cardinal.mk {B : Set ((R j).RankRestriction (c j)) //
      ((R j).restrictRanks (c j)).IsBranch B} ≤ Cardinal.aleph 1 := by
    rw [← Cardinal.mk_congr ((R j).branchRestrictionEquiv (c j) (hc j))]
    exact hcard j
  choose D _ hchains using fun j ↦ exists_aronszajn_core ((R j).restrictRanks (c j)) (hnewcard j)
  have htree : IsTreeOrder (Σ j, (D j).core) := sigma_tree (fun j ↦ (D j).core_tree)
  have hsumchains (B : Set (Σ j, (D j).core)) (hB : IsChain (· ≤ ·) B) : B.Countable :=
    sigma_chain_countable hchains hB
  exact ⟨c, hc, D,
    StrictCondition.product_countable_antichains htree htree hsumchains hsumchains,
    StrictCondition.decides_dense,
    fun _ hG hmeets ↦ simultaneous_weak_coloring_of_directed
      (fun j ↦ (R j).restrictRanks (c j)) D hG hmeets⟩

/-- Simultaneous corrected specialization, including the actual ccc-square
and dense deciding sets. The family may have arbitrary cardinality. -/
theorem exists_simultaneous_ccc_branch_definitions
    (R : ∀ j, RankedTree (T j) (I j))
    (hcof : ∀ j, Order.cof (I j) = Cardinal.aleph 1)
    (hcard : ∀ j, Cardinal.mk {B : Set (T j) // (R j).IsBranch B} ≤ Cardinal.aleph 1) :
    ∃ c : ∀ j, Ordinal.ToType (Ordinal.omega.{v} 1) ↪o I j,
      (∀ j, IsCofinal (Set.range (c j))) ∧
      ∃ D : ∀ j, BranchMarkers ((R j).restrictRanks (c j))
        {B : Set ((R j).RankRestriction (c j)) // ((R j).restrictRanks (c j)).IsBranch B},
        (∀ A : Set (StrictCondition (Σ j, (D j).core) × StrictCondition (Σ j, (D j).core)),
          A.Pairwise (fun p q ↦ ¬ Poset.Compatible p q) → A.Countable) ∧
        (∀ x, ∀ p : StrictCondition (Σ j, (D j).core),
          ∃ q ≤ p, q ∈ StrictCondition.decides x) ∧
        (∀ G : Set (StrictCondition (Σ j, (D j).core)), DirectedOn (· ≥ ·) G →
          (∀ x, ∃ p ∈ G, p ∈ StrictCondition.decides x) →
          ∃ f : ∀ j, T j → ℕ, ∀ j B, (R j).IsBranch B →
            ∃ b ∈ B, (R j).rank b ∈ Set.range (c j) ∧ ∀ x,
              cofinalBranchDefinition {y | (R j).rank y ∈ Set.range (c j)} (f j) b x ↔ x ∈ B) := by
  classical
  choose c hc using fun j ↦ exists_omegaOne_cofinal_embedding (hcof j)
  have hnewcard (j : J) : Cardinal.mk {B : Set ((R j).RankRestriction (c j)) //
      ((R j).restrictRanks (c j)).IsBranch B} ≤ Cardinal.aleph 1 := by
    rw [← Cardinal.mk_congr ((R j).branchRestrictionEquiv (c j) (hc j))]
    exact hcard j
  choose D _ hchains using fun j ↦ exists_aronszajn_core ((R j).restrictRanks (c j)) (hnewcard j)
  have htree : IsTreeOrder (Σ j, (D j).core) := sigma_tree (fun j ↦ (D j).core_tree)
  have hsumchains (B : Set (Σ j, (D j).core)) (hB : IsChain (· ≤ ·) B) : B.Countable :=
    sigma_chain_countable hchains hB
  refine ⟨c, hc, D,
    StrictCondition.product_countable_antichains htree htree hsumchains hsumchains,
    StrictCondition.decides_dense, ?_⟩
  intro G hG hmeets
  obtain ⟨g, hg⟩ := simultaneous_weak_coloring_of_directed
    (fun j ↦ (R j).restrictRanks (c j)) D hG hmeets
  let f (j : J) (x : T j) : ℕ :=
    if h : (R j).rank x ∈ Set.range (c j) then g j ⟨x, h⟩ else 0
  have hf (j : J) : WeaklySpecializes (· ≤ ·)
      (fun x : (R j).RankRestriction (c j) ↦ f j x.val) := by
    have heq : (fun x : (R j).RankRestriction (c j) ↦ f j x.val) = g j := by
      funext x
      simp only [f, dite_eq_left x.property]
      exact congrArg (g j) (Subtype.ext rfl)
    rw [heq]
    exact hg j
  let : Nonempty (Ordinal.ToType (Ordinal.omega.{v} 1)) :=
    Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos 1).ne'
  have hΩ : Cardinal.aleph0 < Order.cof (Ordinal.ToType (Ordinal.omega.{v} 1)) := by
    rw [Ordinal.cof_toType, Cardinal.cof_omega_one]
    exact Cardinal.aleph0_lt_aleph_one
  exact ⟨f, fun j _ hB ↦ (R j).exists_cofinalBranchDefinition (c j) hΩ (hc j) (hf j) hB⟩

end ZFVP.Schmerl
