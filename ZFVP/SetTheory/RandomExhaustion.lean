import ZFVP.SetTheory.PrunedTrees
import ZFVP.SetTheory.DependentChoice
import ZFVP.SetTheory.CountableUnions
import ZFVP.SetTheory.InfiniteDependentChoice
import ZFVP.SetTheory.PulledWellOrder
import ZFVP.SetTheory.CountableSets

/-! Exhaustion for the random conditions: every dense set `D` of positive trees contains a
countable family with pairwise disjoint bodies whose union is co-null, together with a finitary
certificate of co-nullness: for each precision `m`, levels `Mseq` and a cover `f` of measure
`2^{-m}` which enumerates the sequences leaving each `E n` above `Mseq n` and a small level of the
tree of reals avoiding all `E n` at the levels `Mseq n`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Density bounded below by `2^{-m}` at every level. -/
def HasDensity (m T : V) : Prop :=
  ∀ M ∈ (ω : V), ¬ levelSet T M ×ˢ (((2 : ℕ) : V) ^ m) ≤# ((2 : ℕ) : V) ^ M

instance hasDensity_definable : ℒₛₑₜ-relation[V] HasDensity := by
  unfold HasDensity levelSet
  definability

/-- The members of `A` of density at least `2^{-m}`. -/
noncomputable def densityBucket (A m : V) : V := {T ∈ A ; HasDensity m T}

instance densityBucket_definable (A : V) : ℒₛₑₜ-function₁[V] (densityBucket A) := by
  have h : ℒₛₑₜ-relation (fun B m : V ↦ ∀ T, T ∈ B ↔ T ∈ A ∧ HasDensity m T) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = densityBucket A (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [densityBucket, mem_sep_iff]

theorem mem_densityBucket_iff (A m T : V) : T ∈ densityBucket A m ↔ T ∈ A ∧ HasDensity m T := mem_sep_iff

theorem levelGraph_definable (e L : V) : ℒₛₑₜ-function₁ (fun j : V ↦ levelSet (e ‘ j) L) := by
  unfold levelSet
  definability

/-- Level `M` of the intersection of the pair `p` of trees is empty. -/
def EmptyLevelPred (e p M : V) : Prop := ∀ s, s ∉ levelSet ((e ‘ (kpair.π₁ p)) ∩ (e ‘ (kpair.π₂ p))) M

instance emptyLevelPred_definable₃ : ℒₛₑₜ-relation₃[V] EmptyLevelPred := by
  unfold EmptyLevelPred levelSet
  definability

instance emptyLevelPred_definable (e p : V) : ℒₛₑₜ-predicate[V] (EmptyLevelPred e p) := by
  definability

/-- The empty-level sets of the intersections. -/
noncomputable def emptyLevelSet (e p : V) : V := sep (ω : V) (EmptyLevelPred e p) (emptyLevelPred_definable e p)

instance emptyLevelSet_definable (e : V) : ℒₛₑₜ-function₁[V] (emptyLevelSet e) := by
  have h : ℒₛₑₜ-relation (fun B p : V ↦ ∀ M, M ∈ B ↔ M ∈ (ω : V) ∧ EmptyLevelPred e p M) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = emptyLevelSet e (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [emptyLevelSet, mem_sep_iff]

theorem mem_emptyLevelSet_iff (e p M : V) : M ∈ emptyLevelSet e p ↔ M ∈ (ω : V) ∧ EmptyLevelPred e p M :=
  mem_sep_iff

theorem offDiagonal_definable : ℒₛₑₜ-predicate (fun p : V ↦ kpair.π₁ p ≠ kpair.π₂ p) := by
  definability

/-- A family of trees with pairwise disjoint bodies has at most `2^m` members of density `2^{-m}`. -/
theorem densityBucket_cardLE (hAC : InternalChoice V) {A m : V} (hm : m ∈ (ω : V))
    (hA : ∀ T ∈ A, IsTree T)
    (hdisj : ∀ T ∈ A, ∀ T' ∈ A, T ≠ T' → ∀ x, x ∈ treeBody T → x ∈ treeBody T' → False) :
    densityBucket A m ≤# ((2 : ℕ) : V) ^ m := by
  by_contra hnot
  obtain ⟨n₂, hn₂, h2n⟩ := internallyFinite_two_pow (V := V) hm
  have hN : succ n₂ ∈ (ω : V) := ω_succ_closed hn₂
  -- an injection of `succ n₂` into the bucket
  have hinj : succ n₂ ≤# densityBucket A m := by
    by_cases hfin : IsInternallyFinite (densityBucket A m)
    · have h1 := insert_self_cardLE_of_not_cardLE hfin (internallyFinite_two_pow hm) hnot
      have h2 : insert n₂ n₂ ≤# insert (((2 : ℕ) : V) ^ m) (((2 : ℕ) : V) ^ m) :=
        cardLE_insert_fresh h2n.ge (mem_irrefl _) (mem_irrefl _)
      have : succ n₂ ≤# insert (((2 : ℕ) : V) ^ m) (((2 : ℕ) : V) ^ m) := by simpa only [succ] using h2
      exact this.trans h1
    · exact (cardLE_of_subset (IsTransitive.ω.transitive _ hN)).trans
        (omega_cardLE_of_infinite_dependentChoice (dependentChoice_of_internalChoice hAC) hfin)
  obtain ⟨e, he, heinj⟩ := hinj
  have hef : IsFunction e := IsFunction.of_mem he
  have hedom : domain e = succ n₂ := domain_eq_of_mem_function he
  have hval : ∀ j ∈ succ n₂, e ‘ j ∈ A ∧ HasDensity m (e ‘ j) := fun j hj ↦
    (mem_densityBucket_iff _ _ _).mp (function_value_mem he hj)
  have hne : ∀ j ∈ succ n₂, ∀ j' ∈ succ n₂, j ≠ j' → e ‘ j ≠ e ‘ j' := fun j hj j' hj' hne h ↦
    hne (injective_value_eq he heinj hj hj' h)
  -- disjoint levels via chosen empty levels
  obtain ⟨P₂, hP₂def⟩ : ∃ P : V, P = sep ((succ n₂) ×ˢ (succ n₂)) (fun p ↦ kpair.π₁ p ≠ kpair.π₂ p)
    offDiagonal_definable := ⟨_, rfl⟩
  have hP₂mem : ∀ p, p ∈ P₂ ↔ p ∈ (succ n₂) ×ˢ (succ n₂) ∧ kpair.π₁ p ≠ kpair.π₂ p := by
    intro p
    rw [hP₂def]
    exact mem_sep_iff
  have hlevne : ∀ p ∈ P₂, IsNonempty (emptyLevelSet e p) := by
    intro p hp
    obtain ⟨hpprod, hpne⟩ := (hP₂mem p).mp hp
    obtain ⟨j, hj, j', hj', rfl⟩ := mem_prod_iff.mp hpprod
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hpne ⊢
    obtain ⟨M, hM, hMempty⟩ := exists_disjoint_level (hA _ (hval j hj).1) (hA _ (hval j' hj').1)
      (hdisj _ (hval j hj).1 _ (hval j' hj').1 (hne j hj j' hj' hpne))
    refine ⟨M, (mem_emptyLevelSet_iff _ _ _).mpr ⟨hM, ?_⟩⟩
    unfold EmptyLevelPred
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact hMempty
  obtain ⟨ℒ, hℒdef⟩ : ∃ L : V, L = repl (emptyLevelSet e) (emptyLevelSet_definable e) P₂ := ⟨_, rfl⟩
  obtain ⟨c, -, hcval⟩ := hAC ℒ (fun X hX ↦ by
    rw [hℒdef] at hX
    obtain ⟨p, hp, rfl⟩ := (repl_spec (emptyLevelSet_definable e)).mp hX
    exact hlevne p hp)
  have hc : ∀ p ∈ P₂, c ‘ (emptyLevelSet e p) ∈ emptyLevelSet e p := fun p hp ↦
    hcval _ (by rw [hℒdef]; exact (repl_spec (emptyLevelSet_definable e)).mpr ⟨p, hp, rfl⟩)
  -- a common level
  have hP₂fin : IsInternallyFinite P₂ :=
    internallyFinite_subset (internallyFinite_prod ⟨_, hN, CardEQ.refl _⟩ ⟨_, hN, CardEQ.refl _⟩)
      (fun p hp ↦ ((hP₂mem p).mp hp).1)
  obtain ⟨L, hL, hLbound⟩ := internallyFinite_naturals_bounded
    (internallyFinite_repl (fun p ↦ c ‘ (emptyLevelSet e p)) (by definability) hP₂fin) (fun x hx ↦ by
      obtain ⟨p, hp, rfl⟩ := (repl_spec (by definability)).mp hx
      exact ((mem_emptyLevelSet_iff _ _ _).mp (hc p hp)).1)
  have : IsOrdinal L := IsOrdinal.nat hL
  have hlevL : ∀ j ∈ succ n₂, ∀ j' ∈ succ n₂, j ≠ j' → ∀ s, s ∉ levelSet ((e ‘ j) ∩ (e ‘ j')) L := by
    intro j hj j' hj' hjj'
    have hp : ⟨j, j'⟩ₖ ∈ P₂ := (hP₂mem _).mpr ⟨kpair_mem_iff.mpr ⟨hj, hj'⟩, by
      simp only [kpair.π₁_kpair, kpair.π₂_kpair]; exact hjj'⟩
    obtain ⟨hMω, hMempty⟩ := (mem_emptyLevelSet_iff _ _ _).mp (hc _ hp)
    unfold EmptyLevelPred at hMempty
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hMempty
    have hML : c ‘ (emptyLevelSet e ⟨j, j'⟩ₖ) ⊆ L :=
      IsOrdinal.toIsTransitive.transitive _ (hLbound _ ((repl_spec (by definability)).mpr ⟨_, hp, rfl⟩))
    exact levelSet_empty_mono (tree_inter (hA _ (hval j hj).1) (hA _ (hval j' hj').1)) hMω hML hMempty
  -- the counting
  obtain ⟨X, hXdef⟩ : ∃ X : V, X = definableGraph (succ n₂) (fun j ↦ levelSet (e ‘ j) L)
    (levelGraph_definable e L) := ⟨_, rfl⟩
  have hXval : ∀ j ∈ succ n₂, X ‘ j = levelSet (e ‘ j) L := by
    intro j hj
    rw [hXdef]
    exact value_definableGraph _ _ _ hj
  have hX : X ∈ (℘ (((2 : ℕ) : V) ^ L)) ^ succ n₂ := by
    rw [hXdef]
    exact definableGraph_mem_function_of_mapsTo _ _ _ _
      (fun j _ ↦ mem_power_iff.mpr (fun s hs ↦ ((mem_levelSet_iff _ _ _).mp hs).2))
  have hle := disjoint_family_cardLE hAC hN (internallyFinite_two_pow hL) hm hX (by
    intro j hj j' hj' hjj' x hx hx'
    rw [hXval j hj] at hx
    rw [hXval j' hj'] at hx'
    apply hlevL j hj j' hj' hjj' x
    rw [levelSet_inter]
    exact mem_inter_iff.mpr ⟨hx, hx'⟩) (by
    intro j hj
    rw [hXval j hj]
    exact (hval j hj).2 L hL)
  exact not_succ_cardLE_self hn₂ (hle.trans h2n.le)

/-- A family of positive trees with pairwise disjoint bodies is countable. -/
theorem disjoint_positive_family_countable (hAC : InternalChoice V) {A : V}
    (hA : ∀ T ∈ A, IsPositiveTree T)
    (hdisj : ∀ T ∈ A, ∀ T' ∈ A, T ≠ T' → ∀ x, x ∈ treeBody T → x ∈ treeBody T' → False) :
    IsInternallyCountable A := by
  obtain ⟨C, hCdef⟩ : ∃ C : V, C = definableGraph (ω : V) (densityBucket A) (densityBucket_definable A) :=
    ⟨_, rfl⟩
  have hCf : IsFunction C := by rw [hCdef]; exact definableGraph_isFunction _ _ _
  have hCdom : domain C = (ω : V) := by rw [hCdef]; exact domain_definableGraph _ _ _
  have hCval : ∀ m ∈ (ω : V), C ‘ m = densityBucket A m := by
    intro m hm
    rw [hCdef]
    exact value_definableGraph _ _ _ hm
  have hunion : A ⊆ ⋃ˢ range C := by
    intro T hT
    obtain ⟨-, m, hm, hdens⟩ := hA T hT
    refine mem_sUnion_iff.mpr ⟨C ‘ m, ?_, (mem_densityBucket_iff _ _ _).mpr ⟨hT, hdens⟩ |> fun h ↦ by
      rw [hCval m hm]; exact h⟩
    exact mem_range_iff.mpr ⟨m, kpair_value_mem (by rw [hCdom]; exact hm)⟩
  refine internallyCountable_subset (countable_union_of_countableChoice (countableChoice_of_internalChoice hAC)
    hCdom (fun m hm ↦ ?_)) hunion
  rw [hCval m hm]
  obtain ⟨n, hn, h2n⟩ := internallyFinite_two_pow (V := V) hm
  exact ((densityBucket_cardLE hAC hm (fun T hT ↦ (hA T hT).1) hdisj).trans h2n.le).trans
    (cardLE_of_subset (IsTransitive.ω.transitive n hn))

/-- The sequences avoiding `E n` at level `Mseq n` for every `n`. -/
def Avoids (E Mseq s : V) : Prop := ∀ n ∈ (ω : V), Mseq ‘ n ⊆ domain s → s ↾ (Mseq ‘ n) ∉ E ‘ n

instance avoids_definable (E Mseq : V) : ℒₛₑₜ-predicate[V] (Avoids E Mseq) := by
  unfold Avoids
  definability

/-- The tree of sequences avoiding all `E n` at the levels `Mseq n`. -/
noncomputable def avoidTree (E Mseq : V) : V := sep (binarySequences V) (Avoids E Mseq) (avoids_definable E Mseq)

theorem mem_avoidTree_iff (E Mseq s : V) : s ∈ avoidTree E Mseq ↔ s ∈ binarySequences V ∧ Avoids E Mseq s :=
  mem_sep_iff

theorem avoidTree_isTree (E Mseq : V) : IsTree (avoidTree E Mseq) := by
  refine ⟨fun s hs ↦ ((mem_avoidTree_iff _ _ _).mp hs).1, fun s hs k hk ↦ ?_⟩
  obtain ⟨hsB, hav⟩ := (mem_avoidTree_iff _ _ _).mp hs
  obtain ⟨n, hn, hsn⟩ := (mem_binarySequences_iff _).mp hsB
  have hdn : domain s = n := domain_eq_of_mem_function hsn
  rw [hdn] at hk
  have : IsOrdinal n := IsOrdinal.nat hn
  have hkn : k ⊆ n := IsOrdinal.toIsTransitive.transitive k hk
  have hkω : k ∈ (ω : V) := IsTransitive.ω.transitive n hn k hk
  have hsk : s ↾ k ∈ ((2 : ℕ) : V) ^ k := function_restrict_mem hsn hkn
  refine (mem_avoidTree_iff _ _ _).mpr ⟨(mem_binarySequences_iff _).mpr ⟨k, hkω, hsk⟩, fun i hi hMk ↦ ?_⟩
  rw [domain_eq_of_mem_function hsk] at hMk
  rw [restrict_restrict_of_subset hMk]
  exact hav i hi (by rw [hdn]; exact fun x hx ↦ hkn x (hMk x hx))

theorem mem_treeBody_avoidTree_iff {E Mseq : V} (hMseq : ∀ n ∈ (ω : V), Mseq ‘ n ∈ (ω : V)) (x : V) :
    x ∈ treeBody (avoidTree E Mseq) ↔ x ∈ cantorSpace V ∧ ∀ n ∈ (ω : V), x ↾ (Mseq ‘ n) ∉ E ‘ n := by
  rw [mem_treeBody_iff]
  constructor
  · rintro ⟨hxc, h⟩
    refine ⟨hxc, fun n hn ↦ ?_⟩
    obtain ⟨-, hav⟩ := (mem_avoidTree_iff _ _ _).mp (h (Mseq ‘ n) (hMseq n hn))
    have hd : domain (x ↾ (Mseq ‘ n)) = Mseq ‘ n :=
      domain_eq_of_mem_function (function_restrict_mem hxc (IsTransitive.ω.transitive _ (hMseq n hn)))
    have := hav n hn (by rw [hd])
    rwa [restrict_restrict_of_subset (fun z hz ↦ hz)] at this
  · rintro ⟨hxc, h⟩
    refine ⟨hxc, fun k hk ↦ (mem_avoidTree_iff _ _ _).mpr ⟨restrict_mem_binarySequences hxc hk, fun n hn hMk ↦ ?_⟩⟩
    have hd : domain (x ↾ k) = k := domain_eq_of_mem_function (function_restrict_mem hxc (IsTransitive.ω.transitive _ hk))
    rw [hd] at hMk
    rw [restrict_restrict_of_subset hMk]
    exact h n hn

/-- A level and a cover for the difference at a given precision. -/
def LevelCoverPair (T p q : V) : Prop :=
  IsCoverAt (kpair.π₂ q) (openFrom (levelSet T (kpair.π₁ q)) \ treeBody T) p ∧
    ∀ s ∈ binarySequences V, LeavesTree T (kpair.π₁ q) s → ∃ i ∈ (ω : V), (kpair.π₂ q) ‘ i = s

instance levelCoverPair_definable : ℒₛₑₜ-relation₃[V] LevelCoverPair := by
  unfold LevelCoverPair levelSet
  definability

/-- The level-cover pairs for `E n` at precision `m + n + 2`. -/
noncomputable def levelCoverSet (E m n : V) : V :=
  {q ∈ (ω : V) ×ˢ ((binarySequences V) ^ (ω : V)) ; LevelCoverPair (E ‘ n) (succ (ordinalAdd m (succ n))) q}

instance levelCoverSet_definable (E m : V) : ℒₛₑₜ-function₁[V] (levelCoverSet E m) := by
  have h : ℒₛₑₜ-relation (fun C n : V ↦ ∀ q, q ∈ C ↔ q ∈ (ω : V) ×ˢ ((binarySequences V) ^ (ω : V)) ∧
      LevelCoverPair (E ‘ n) (succ (ordinalAdd m (succ n))) q) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = levelCoverSet E m (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [levelCoverSet, mem_sep_iff]

theorem mem_levelCoverSet_iff (E m n q : V) : q ∈ levelCoverSet E m n ↔
    q ∈ (ω : V) ×ˢ ((binarySequences V) ^ (ω : V)) ∧ LevelCoverPair (E ‘ n) (succ (ordinalAdd m (succ n))) q :=
  mem_sep_iff

theorem levelCoverSet_nonempty (hAC : InternalChoice V) {E m n : V} (hT : IsTree (E ‘ n))
    (hm : m ∈ (ω : V)) (hn : n ∈ (ω : V)) : IsNonempty (levelCoverSet E m n) := by
  have hp : succ (ordinalAdd m (succ n)) ∈ (ω : V) := ω_succ_closed (ordinalAdd_natural hm (ω_succ_closed hn))
  obtain ⟨M, hM, f, hf, hcov, hsurj⟩ := exists_level_cover hAC hT hp
  refine ⟨⟨M, f⟩ₖ, (mem_levelCoverSet_iff _ _ _ _).mpr ⟨kpair_mem_iff.mpr ⟨hM, hf⟩, ?_⟩⟩
  unfold LevelCoverPair
  rw [kpair.π₁_kpair, kpair.π₂_kpair]
  exact ⟨hcov, hsurj⟩

/-- The shifted family of covers: the level cover of the avoiding tree first, then the drop
covers of the `E n`. -/
def ShiftRel (g c E m p : V) : Prop :=
  (kpair.π₁ p = ∅ ∧ kpair.π₂ p = g) ∨
    ∃ n ∈ (ω : V), kpair.π₁ p = succ n ∧ kpair.π₂ p = kpair.π₂ (c ‘ (levelCoverSet E m n))

instance shiftRel_definable (g c E m : V) : ℒₛₑₜ-predicate[V] (ShiftRel g c E m) := by
  unfold ShiftRel
  definability

theorem levelPi1_definable (c E m : V) : ℒₛₑₜ-function₁ (fun n : V ↦ kpair.π₁ (c ‘ (levelCoverSet E m n))) := by
  definability

theorem natural_succ_injective {n n' : V} (hn : n ∈ (ω : V)) (hn' : n' ∈ (ω : V)) (h : succ n = succ n') : n = n' := by
  have : IsOrdinal n := IsOrdinal.nat hn
  have : IsOrdinal n' := IsOrdinal.nat hn'
  exact succ_injective_ordinal h

/-- The exhaustion certificate for a dense set of random conditions. -/
theorem exists_random_certificate (hAC : InternalChoice V) {D : V} (hD : D ⊆ randomConditions V)
    (hdense : ForcingDense (randomConditions V) (inclusionOrder (randomConditions V)) D) :
    ∃ E ∈ (randomConditions V) ^ (ω : V), (∀ n ∈ (ω : V), E ‘ n ∈ D) ∧
      ∀ m ∈ (ω : V), ∃ Mseq ∈ (ω : V) ^ (ω : V), ∃ M ∈ (ω : V), ∃ f ∈ (binarySequences V) ^ (ω : V),
        (∀ k ∈ (ω : V), SmallMeasure (f “ k) m) ∧
        (∀ n ∈ (ω : V), ∀ s ∈ binarySequences V, LeavesTree (E ‘ n) (Mseq ‘ n) s → ∃ i ∈ (ω : V), f ‘ i = s) ∧
        ∀ s ∈ levelSet (avoidTree E Mseq) M, ∃ i ∈ (ω : V), f ‘ i = s := by
  -- a maximal antichain of `D` in the trees with nonempty body
  have hDb : D ⊆ bodyTrees V := fun T hT ↦ randomConditions_subset_bodyTrees T (hD T hT)
  obtain ⟨A, ⟨⟨hAb, hanti⟩, hAD, hmax⟩⟩ := exists_maximalAntichain (inclusionOrder_preorder (bodyTrees V)) hDb
    (wellOrderable_of_internalChoice hAC D)
  have hApos : ∀ T ∈ A, IsPositiveTree T := fun T hT ↦ (mem_randomConditions_iff T).mp (hD T (hAD T hT))
  have hAdisj : ∀ T ∈ A, ∀ T' ∈ A, T ≠ T' → ∀ x, x ∈ treeBody T → x ∈ treeBody T' → False := by
    intro T hT T' hT' hne x hx hx'
    exact hanti T hT T' hT' hne ((bodyTrees_compatible_iff (hAb T hT) (hAb T' hT')).mpr ⟨x, hx, hx'⟩)
  -- `A` is nonempty and countable
  obtain ⟨d₀, hd₀D, -⟩ := hdense.2 (binarySequences V) ((mem_randomConditions_iff _).mpr fullTree_positive)
  obtain ⟨a₀, ha₀A, -⟩ := hmax d₀ hd₀D
  obtain ⟨E, hE, hrange⟩ := exists_surjection_of_cardLE (disjoint_positive_family_countable hAC hApos hAdisj) ha₀A
  have hEf : IsFunction E := IsFunction.of_mem hE
  have hEdom : domain E = (ω : V) := domain_eq_of_mem_function hE
  have hEA : ∀ n ∈ (ω : V), E ‘ n ∈ A := fun n hn ↦ function_value_mem hE hn
  have hEpos : ∀ n ∈ (ω : V), IsPositiveTree (E ‘ n) := fun n hn ↦ hApos _ (hEA n hn)
  have hEtree : ∀ n ∈ (ω : V), IsTree (E ‘ n) := fun n hn ↦ (hEpos n hn).1
  refine ⟨E, mem_function_of_mem_function_of_subset hE (fun T hT ↦ hD T (hAD T hT)), fun n hn ↦ hAD _ (hEA n hn), ?_⟩
  intro m hm
  have : IsOrdinal m := IsOrdinal.nat hm
  -- choose levels and drop covers
  obtain ⟨ℒ, hℒdef⟩ : ∃ L : V, L = repl (levelCoverSet E m) (levelCoverSet_definable E m) (ω : V) := ⟨_, rfl⟩
  obtain ⟨c, -, hcval⟩ := hAC ℒ (fun X hX ↦ by
    rw [hℒdef] at hX
    obtain ⟨n, hn, rfl⟩ := (repl_spec (levelCoverSet_definable E m)).mp hX
    exact levelCoverSet_nonempty hAC (hEtree n hn) hm hn)
  have hc : ∀ n ∈ (ω : V), c ‘ (levelCoverSet E m n) ∈ levelCoverSet E m n := fun n hn ↦
    hcval _ (by rw [hℒdef]; exact (repl_spec (levelCoverSet_definable E m)).mpr ⟨n, hn, rfl⟩)
  have hcpair : ∀ n ∈ (ω : V), kpair.π₁ (c ‘ (levelCoverSet E m n)) ∈ (ω : V) ∧
      kpair.π₂ (c ‘ (levelCoverSet E m n)) ∈ (binarySequences V) ^ (ω : V) := by
    intro n hn
    obtain ⟨hprod, -⟩ := (mem_levelCoverSet_iff _ _ _ _).mp (hc n hn)
    obtain ⟨a, ha, b, hb, hab⟩ := mem_prod_iff.mp hprod
    rw [hab, kpair.π₁_kpair, kpair.π₂_kpair]
    exact ⟨ha, hb⟩
  have hcprop : ∀ n ∈ (ω : V), LevelCoverPair (E ‘ n) (succ (ordinalAdd m (succ n))) (c ‘ (levelCoverSet E m n)) :=
    fun n hn ↦ ((mem_levelCoverSet_iff _ _ _ _).mp (hc n hn)).2
  obtain ⟨Mseq, hMseqdef⟩ : ∃ Ms : V, Ms = definableGraph (ω : V) (fun n ↦ kpair.π₁ (c ‘ (levelCoverSet E m n)))
    (levelPi1_definable c E m) := ⟨_, rfl⟩
  have hMseq : Mseq ∈ (ω : V) ^ (ω : V) := by
    rw [hMseqdef]
    exact definableGraph_mem_function_of_mapsTo _ _ _ _ (fun n hn ↦ (hcpair n hn).1)
  have hMseqval : ∀ n ∈ (ω : V), Mseq ‘ n = kpair.π₁ (c ‘ (levelCoverSet E m n)) := by
    intro n hn
    rw [hMseqdef]
    exact value_definableGraph _ _ _ hn
  have hMseqω : ∀ n ∈ (ω : V), Mseq ‘ n ∈ (ω : V) := fun n hn ↦ function_value_mem hMseq hn
  -- the avoiding tree is not positive
  have hnotpos : ¬ IsPositiveTree (avoidTree E Mseq) := by
    intro hpos
    obtain ⟨d, hdD, hdle⟩ := hdense.2 _ ((mem_randomConditions_iff _).mpr hpos)
    obtain ⟨-, -, hdsub⟩ := (pair_mem_inclusionOrder _ _ _).mp hdle
    obtain ⟨a, haA, hcompat⟩ := hmax d hdD
    obtain ⟨x, hxa, hxd⟩ := (bodyTrees_compatible_iff (hAb a haA) (hDb d hdD)).mp hcompat
    have hxK : x ∈ treeBody (avoidTree E Mseq) := treeBody_mono hdsub x hxd
    obtain ⟨-, hav⟩ := (mem_treeBody_avoidTree_iff hMseqω x).mp hxK
    have har : a ∈ range E := by rw [hrange]; exact haA
    obtain ⟨n, hn⟩ := mem_range_iff.mp har
    have hnω : n ∈ (ω : V) := by rw [← hEdom]; exact mem_domain_of_kpair_mem hn
    rw [← value_eq_of_kpair_mem hn] at hxa
    exact hav n hnω (((mem_treeBody_iff _ _).mp hxa).2 _ (hMseqω n hnω))
  have hsmallK : ∃ M ∈ (ω : V), levelSet (avoidTree E Mseq) M ×ˢ (((2 : ℕ) : V) ^ succ m) ≤# ((2 : ℕ) : V) ^ M := by
    by_contra hcon
    push Not at hcon
    exact hnotpos ⟨avoidTree_isTree E Mseq, succ m, ω_succ_closed hm, hcon⟩
  obtain ⟨M, hM, hMsmall⟩ := hsmallK
  -- the cover of the small level of the avoiding tree
  have hDω : levelSet (avoidTree E Mseq) M ≤# (ω : V) := by
    obtain ⟨n, hn, hle⟩ := levelSet_finite (T := avoidTree E Mseq) hM
    exact hle.le.trans (cardLE_of_subset (IsTransitive.ω.transitive n hn))
  have hsmallg : ∀ F, F ⊆ levelSet (avoidTree E Mseq) M → IsInternallyFinite F → SmallMeasure F (succ m) := by
    intro F hF _
    refine ⟨M, hM, fun s hs ↦ by rw [domain_eq_of_mem_function ((mem_levelSet_iff _ _ _).mp (hF s hs)).2], ?_⟩
    rw [shadow_self (fun s hs ↦ ((mem_levelSet_iff _ _ _).mp (hF s hs)).2)]
    exact (prod_cardLE_prod (cardLE_of_subset hF) (CardLE.refl _)).trans hMsmall
  obtain ⟨g, hg, hgcov, hgsurj⟩ := exists_cover_of_enumerable (A := (∅ : V)) (ω_succ_closed hm)
    (levelSet_subset_binarySequences hM) hDω (fun x hx ↦ (not_mem_empty hx).elim) hsmallg
  -- the shifted family
  obtain ⟨cov, hcovdef⟩ : ∃ cov : V, cov = sep ((ω : V) ×ˢ ((binarySequences V) ^ (ω : V))) (ShiftRel g c E m)
    (shiftRel_definable g c E m) := ⟨_, rfl⟩
  have hcovmem : ∀ k y, ⟨k, y⟩ₖ ∈ cov ↔ k ∈ (ω : V) ∧ y ∈ (binarySequences V) ^ (ω : V) ∧ ShiftRel g c E m ⟨k, y⟩ₖ := by
    intro k y
    rw [hcovdef, mem_sep_iff, kpair_mem_iff, and_assoc]
  have hrel0 : ShiftRel g c E m ⟨∅, g⟩ₖ := Or.inl ⟨by rw [kpair.π₁_kpair], by rw [kpair.π₂_kpair]⟩
  have hrelsucc : ∀ n ∈ (ω : V), ShiftRel g c E m ⟨succ n, kpair.π₂ (c ‘ (levelCoverSet E m n))⟩ₖ :=
    fun n hn ↦ Or.inr ⟨n, hn, by rw [kpair.π₁_kpair], by rw [kpair.π₂_kpair]⟩
  have huniq : ∀ k y y', ShiftRel g c E m ⟨k, y⟩ₖ → ShiftRel g c E m ⟨k, y'⟩ₖ → y = y' := by
    intro k y y' h1 h2
    rcases h1 with ⟨hk, hy⟩ | ⟨n, hn, hk, hy⟩ <;> rcases h2 with ⟨hk', hy'⟩ | ⟨n', hn', hk', hy'⟩
    · rw [kpair.π₂_kpair] at hy hy'
      rw [hy, hy']
    · rw [kpair.π₁_kpair] at hk hk'
      exact absurd (hk'.symm.trans hk) (fun h ↦ not_mem_empty (h ▸ mem_succ_self n'))
    · rw [kpair.π₁_kpair] at hk hk'
      exact absurd (hk.symm.trans hk') (fun h ↦ not_mem_empty (h ▸ mem_succ_self n))
    · rw [kpair.π₁_kpair] at hk hk'
      rw [kpair.π₂_kpair] at hy hy'
      have := natural_succ_injective hn hn' (hk.symm.trans hk')
      rw [hy, hy', this]
  have hcov : cov ∈ ((binarySequences V) ^ (ω : V)) ^ (ω : V) := by
    rw [mem_function_iff]
    refine ⟨fun p hp ↦ by rw [hcovdef] at hp; exact (mem_sep_iff.mp hp).1, fun k hk ↦ ?_⟩
    rcases internalNatural_cases hk with rfl | ⟨n, hn, rfl⟩
    · exact ⟨g, (hcovmem _ _).mpr ⟨hk, hg, hrel0⟩, fun y hy ↦ huniq _ _ _ ((hcovmem _ _).mp hy).2.2 hrel0⟩
    · exact ⟨_, (hcovmem _ _).mpr ⟨hk, (hcpair n hn).2, hrelsucc n hn⟩,
        fun y hy ↦ huniq _ _ _ ((hcovmem _ _).mp hy).2.2 (hrelsucc n hn)⟩
  have hcovf : IsFunction cov := IsFunction.of_mem hcov
  have hcov0 : cov ‘ (∅ : V) = g := value_eq_of_kpair_mem ((hcovmem _ _).mpr ⟨zero_mem_ω, hg, hrel0⟩)
  have hcovsucc : ∀ n ∈ (ω : V), cov ‘ (succ n) = kpair.π₂ (c ‘ (levelCoverSet E m n)) := fun n hn ↦
    value_eq_of_kpair_mem ((hcovmem _ _).mpr ⟨ω_succ_closed hn, (hcpair n hn).2, hrelsucc n hn⟩)
  -- the combined cover
  obtain ⟨f, hf, hfsmall, hfval⟩ := exists_combined_cover hm hcov (by
    intro n hn k hk
    rcases internalNatural_cases hn with rfl | ⟨n', hn', rfl⟩
    · change SmallMeasure ((cov ‘ (∅ : V)) “ k) (succ (ordinalAdd m (∅ : V)))
      rw [hcov0, ordinalAdd_zero]
      exact hgcov.2 k hk
    · rw [hcovsucc n' hn']
      exact (hcprop n' hn').1.2 k hk)
  refine ⟨Mseq, hMseq, M, hM, f, hf, hfsmall, ?_, ?_⟩
  · intro n hn s hs hl
    rw [hMseqval n hn] at hl
    obtain ⟨i, hi, hgi⟩ := (hcprop n hn).2 s hs hl
    obtain ⟨k, hk, hfk⟩ := hfval (succ n) (ω_succ_closed hn) i hi
    refine ⟨k, hk, ?_⟩
    rw [hfk, hcovsucc n hn, hgi]
  · intro s hs
    obtain ⟨i, hi, hgi⟩ := hgsurj s hs
    obtain ⟨k, hk, hfk⟩ := hfval ∅ zero_mem_ω i hi
    refine ⟨k, hk, ?_⟩
    rw [hfk, hcov0, hgi]

end ZFVP
