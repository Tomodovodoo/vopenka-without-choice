import ZFVP.SetTheory.ColumnPermutations
import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.NaturalIteration
import ZFVP.SetTheory.Hartogs
import ZFVP.SetTheory.CheckNames
import ZFVP.SetTheory.WellOrderingChoice

/-! The Feferman-Levy forcing: the finite-support product of the collapses of a sequence
of cardinals to omega. Column `m` collapses `flCardinal m`, the Hartogs number of the
set of nice names for reals of the product of the earlier columns. Conditions are finite
partial functions on `ω × ω` whose value at `(m, k)` lies in `flCardinal m`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Conditions with columns in `domain s` and values in `s ‘ m` at column `m`. -/
noncomputable def flStageConditions (s : V) : V :=
  {p ∈ finitePartialFunctions (domain s ×ˢ (ω : V)) (⋃ˢ range s) ;
    ∀ z ∈ p, kpair.π₂ z ∈ s ‘ (kpair.π₁ (kpair.π₁ z))}

theorem mem_flStageConditions (s p : V) : p ∈ flStageConditions s ↔
    p ∈ finitePartialFunctions (domain s ×ˢ (ω : V)) (⋃ˢ range s) ∧
      ∀ z ∈ p, kpair.π₂ z ∈ s ‘ (kpair.π₁ (kpair.π₁ z)) := mem_sep_iff

instance flStageConditions_definable : ℒₛₑₜ-function₁[V] flStageConditions := by
  have h : ℒₛₑₜ-relation[V] (fun Q s ↦ ∀ p, p ∈ Q ↔
      p ∈ finitePartialFunctions (domain s ×ˢ (ω : V)) (⋃ˢ range s) ∧
        ∀ z ∈ p, kpair.π₂ z ∈ s ‘ (kpair.π₁ (kpair.π₁ z))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = flStageConditions (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_flStageConditions]

/-- The nice names for reals over the stage forcing: sets of pairs of a check natural and
a stage condition. -/
noncomputable def flNiceNames (s : V) : V :=
  ℘ (repl (fun z ↦ ⟨checkName ∅ (kpair.π₁ z), kpair.π₂ z⟩ₖ) (by definability)
    ((ω : V) ×ˢ flStageConditions s))

instance flNiceNames_definable : ℒₛₑₜ-function₁[V] flNiceNames := by
  unfold flNiceNames
  definability

theorem mem_flNiceNames (s τ : V) : τ ∈ flNiceNames s ↔
    ∀ z ∈ τ, ∃ k ∈ (ω : V), ∃ q ∈ flStageConditions s, z = ⟨checkName ∅ k, q⟩ₖ := by
  simp only [flNiceNames, mem_power_iff]
  constructor
  · intro h z hz
    obtain ⟨u, hu, rfl⟩ := (repl_spec _).mp (h z hz)
    obtain ⟨k, hk, q, hq, rfl⟩ := mem_prod_iff.mp hu
    exact ⟨k, hk, q, hq, by simp⟩
  · intro h z hz
    obtain ⟨k, hk, q, hq, rfl⟩ := h z hz
    exact (repl_spec _).mpr ⟨⟨k, q⟩ₖ, kpair_mem_iff.mpr ⟨hk, hq⟩, by simp⟩

/-- One recursion step: append the Hartogs number of the nice names of the current stage. -/
noncomputable def flStep (s : V) : V := insert ⟨domain s, hartogsNumber (flNiceNames s)⟩ₖ s

theorem mem_flStep (s z : V) : z ∈ flStep s ↔ z = ⟨domain s, hartogsNumber (flNiceNames s)⟩ₖ ∨ z ∈ s :=
  mem_insert

theorem flStep_definable : ℒₛₑₜ-function₁[V] flStep := by
  have h : ℒₛₑₜ-relation[V] (fun t s ↦ ∀ z, z ∈ t ↔
      z = ⟨domain s, hartogsNumber (flNiceNames s)⟩ₖ ∨ z ∈ s) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = flStep (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_flStep]

noncomputable def flSequence (n : V) : V := naturalIteration flStep flStep_definable ∅ n

instance flSequence_definable : ℒₛₑₜ-function₁[V] flSequence := by
  unfold flSequence
  exact naturalIteration_definable _ _ _

theorem flSequence_zero : flSequence (0 : V) = ∅ := naturalIteration_zero _ _ _

theorem flSequence_succ {n : V} (hn : n ∈ (ω : V)) : flSequence (succ n) = flStep (flSequence n) :=
  naturalIteration_succ _ _ _ hn

theorem flSequence_function_domain : ∀ n ∈ (ω : V), IsFunction (flSequence n) ∧ domain (flSequence n) = n := by
  apply naturalNumber_induction (fun n ↦ IsFunction (flSequence n) ∧ domain (flSequence n) = n)
    (by definability)
  · rw [flSequence_zero]
    refine ⟨inferInstance, ?_⟩
    rw [show (0 : V) = ∅ from rfl]
    simp
  · intro n hn ih
    have : IsFunction (flSequence n) := ih.1
    rw [flSequence_succ hn]
    unfold flStep
    rw [ih.2]
    have hfresh : n ∉ domain (flSequence n) := by rw [ih.2]; exact mem_irrefl n
    refine ⟨IsFunction.insert (flSequence n) n _ hfresh, ?_⟩
    rw [domain_insert, ih.2]
    rfl

noncomputable def flCardinal (m : V) : V := hartogsNumber (flNiceNames (flSequence m))

instance flCardinal_definable : ℒₛₑₜ-function₁[V] flCardinal := by
  unfold flCardinal
  definability

instance flCardinal_ordinal (m : V) : IsOrdinal (flCardinal m) := hartogsNumber_ordinal _

theorem flSequence_subset_succ {n : V} (hn : n ∈ (ω : V)) : flSequence n ⊆ flSequence (succ n) := by
  rw [flSequence_succ hn]
  exact subset_insert _ _

theorem flSequence_value_succ {n : V} (hn : n ∈ (ω : V)) :
    (flSequence (succ n)) ‘ n = flCardinal n := by
  have hf := (flSequence_function_domain (succ n) (ω_succ_closed hn)).1
  apply value_eq_of_kpair_mem
  rw [flSequence_succ hn]
  unfold flStep
  rw [(flSequence_function_domain n hn).2]
  exact mem_insert.mpr (Or.inl rfl)

/-- The sequence of all column cardinals. -/
noncomputable def flCardinals : V := definableGraph (ω : V) flCardinal (by definability)

instance flCardinals_isFunction : IsFunction (flCardinals : V) := definableGraph_isFunction _ _ _

theorem domain_flCardinals : domain (flCardinals : V) = ω := domain_definableGraph _ _ _

theorem flCardinals_value {m : V} (hm : m ∈ (ω : V)) : (flCardinals : V) ‘ m = flCardinal m :=
  value_definableGraph _ _ _ hm

theorem flSequence_value {n m : V} (hn : n ∈ (ω : V)) (hm : m ∈ n) :
    (flSequence n) ‘ m = flCardinal m := by
  revert m
  apply naturalNumber_induction (fun n ↦ ∀ m ∈ n, (flSequence n) ‘ m = flCardinal m)
    (by definability) ?_ ?_ n hn
  · intro m hm
    exact (not_mem_empty hm).elim
  · intro n hn ih m hm
    rcases mem_succ_iff.mp hm with rfl | hmn
    · exact flSequence_value_succ hn
    · have hf := (flSequence_function_domain (succ n) (ω_succ_closed hn)).1
      have hf' := (flSequence_function_domain n hn).1
      have hmem : ⟨m, flCardinal m⟩ₖ ∈ flSequence n := by
        rw [← ih m hmn]
        exact kpair_value_mem (by rw [(flSequence_function_domain n hn).2]; exact hmn)
      exact value_eq_of_kpair_mem (flSequence_subset_succ hn _ hmem)

/-- Stage `n` of the cardinal sequence is the restriction of the full sequence. -/
theorem flSequence_eq_restrict {n : V} (hn : n ∈ (ω : V)) :
    flSequence n = (flCardinals : V) ↾ n := by
  have hf := (flSequence_function_domain n hn).1
  have hd := (flSequence_function_domain n hn).2
  have : IsFunction ((flCardinals : V) ↾ n) := IsFunction.ofSubset _ _ (restrict_subset _ _)
  apply functions_eq_of_domain_values
  · rw [hd, domain_restrict_eq, domain_flCardinals]
    apply mem_ext
    intro x
    simp only [mem_inter_iff]
    exact ⟨fun hx ↦ ⟨IsOrdinal.toIsTransitive.mem_trans hx hn, hx⟩, And.right⟩
  · intro m hm
    rw [hd] at hm
    have hmω : m ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hm hn
    rw [flSequence_value hn hm, value_restrict (by rw [domain_flCardinals]; exact hmω) hm,
      flCardinals_value hmω]

/-! ### The forcing and its stages -/

/-- Conditions supported in the columns below `n`: finite partial functions on `n × ω` whose
value at `(m, k)` lies in `flCardinal m`. The full forcing is the stage at `ω`. -/
noncomputable def flStage (n : V) : V :=
  {p ∈ finitePartialFunctions (n ×ˢ (ω : V)) (⋃ˢ repl flCardinal (by definability) n) ;
    ∀ z ∈ p, kpair.π₂ z ∈ flCardinal (kpair.π₁ (kpair.π₁ z))}

theorem mem_flStage (n p : V) : p ∈ flStage n ↔
    p ∈ finitePartialFunctions (n ×ˢ (ω : V)) (⋃ˢ repl flCardinal (by definability) n) ∧
      ∀ z ∈ p, kpair.π₂ z ∈ flCardinal (kpair.π₁ (kpair.π₁ z)) := mem_sep_iff

instance flStage_definable : ℒₛₑₜ-function₁[V] flStage := by
  have h : ℒₛₑₜ-relation[V] (fun Q n ↦ ∀ p, p ∈ Q ↔
      p ∈ finitePartialFunctions (n ×ˢ (ω : V)) (⋃ˢ repl flCardinal (by definability) n) ∧
        ∀ z ∈ p, kpair.π₂ z ∈ flCardinal (kpair.π₁ (kpair.π₁ z))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = flStage (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_flStage]

noncomputable abbrev flConditions (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  flStage (ω : V)

noncomputable def flOrder (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  reverseInclusionOrder (flConditions V)

theorem fl_poset : IsForcingPoset (flConditions V) (flOrder V) := reverseInclusionOrder_poset _

theorem pair_mem_flOrder (p q : V) :
    ⟨p, q⟩ₖ ∈ flOrder V ↔ p ∈ flConditions V ∧ q ∈ flConditions V ∧ q ⊆ p :=
  pair_mem_reverseInclusionOrder _ _ _

theorem flStage_function {n p : V} (hp : p ∈ flStage n) : IsFunction p :=
  ((mem_finitePartialFunctions _ _ _).mp ((mem_flStage n p).mp hp).1).2.1

theorem flStage_finite_domain {n p : V} (hp : p ∈ flStage n) : IsInternallyFinite (domain p) :=
  ((mem_finitePartialFunctions _ _ _).mp ((mem_flStage n p).mp hp).1).2.2

theorem flStage_finite {n p : V} (hp : p ∈ flStage n) : IsInternallyFinite p := by
  have : IsFunction p := flStage_function hp
  exact internallyFinite_function (flStage_finite_domain hp)

theorem flStage_domain {n p : V} (hp : p ∈ flStage n) : domain p ⊆ n ×ˢ (ω : V) :=
  finitePartialFunction_domain ((mem_flStage n p).mp hp).1

theorem flStage_values {n p : V} (hp : p ∈ flStage n) :
    ∀ z ∈ p, kpair.π₂ z ∈ flCardinal (kpair.π₁ (kpair.π₁ z)) := ((mem_flStage n p).mp hp).2

/-- A finite function on `n × ω` with column-bounded values is a stage condition. -/
theorem flStage_of_bounds {n p : V} [IsFunction p] (hfin : IsInternallyFinite (domain p))
    (hdom : domain p ⊆ n ×ˢ (ω : V))
    (hval : ∀ z ∈ p, kpair.π₂ z ∈ flCardinal (kpair.π₁ (kpair.π₁ z))) : p ∈ flStage n := by
  refine (mem_flStage n p).mpr ⟨(mem_finitePartialFunctions _ _ _).mpr ⟨?_, inferInstance, hfin⟩, hval⟩
  intro z hz
  obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
  have hx : x ∈ n ×ˢ (ω : V) := hdom x (mem_domain_of_kpair_mem hz)
  obtain ⟨m, hm, k, hk, rfl⟩ := mem_prod_iff.mp hx
  have hy := hval _ hz
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hy
  refine kpair_mem_iff.mpr ⟨hx, mem_sUnion_iff.mpr ⟨flCardinal m, (repl_spec _).mpr ⟨m, hm, rfl⟩, hy⟩⟩

theorem flStage_mono {n n' : V} (h : n ⊆ n') : flStage n ⊆ flStage n' := by
  intro p hp
  have : IsFunction p := flStage_function hp
  apply flStage_of_bounds (flStage_finite_domain hp) ?_ (flStage_values hp)
  intro z hz
  obtain ⟨m, hm, k, hk, rfl⟩ := mem_prod_iff.mp (flStage_domain hp z hz)
  exact kpair_mem_iff.mpr ⟨h m hm, hk⟩

theorem flStage_subset {n : V} (hn : n ∈ (ω : V)) : flStage n ⊆ flConditions V :=
  flStage_mono (IsOrdinal.toIsTransitive.transitive n hn)

theorem mem_flStage_iff {n : V} (p : V) : p ∈ flStage n ↔ p ∈ flStage n := Iff.rfl

theorem flCondition_subset {n p q : V} (hp : p ∈ flStage n) (hq : q ⊆ p) : q ∈ flStage n :=
  mem_sep_iff.mpr ⟨finitePartialFunction_subset ((mem_flStage n p).mp hp).1 hq,
    fun z hz ↦ flStage_values hp z (hq z hz)⟩

theorem flCondition_union {n p q : V} (hp : p ∈ flStage n) (hq : q ∈ flStage n)
    (hc : ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z) : p ∪ q ∈ flStage n := by
  refine mem_sep_iff.mpr ⟨finitePartialFunction_union ((mem_flStage n p).mp hp).1
    ((mem_flStage n q).mp hq).1 hc, ?_⟩
  intro z hz
  exact (mem_union_iff.mp hz).elim (flStage_values hp z) (flStage_values hq z)

theorem fl_top : IsForcingTop (flConditions V) (flOrder V) ∅ := by
  have h0 : (∅ : V) ∈ flConditions V :=
    mem_sep_iff.mpr ⟨empty_mem_finitePartialFunctions _ _, fun z hz ↦ (not_mem_empty hz).elim⟩
  exact ⟨h0, fun p hp ↦ (pair_mem_flOrder _ _).mpr ⟨hp, h0, by simp⟩⟩

theorem fl_compatible_iff {p q : V} (hp : p ∈ flConditions V) (hq : q ∈ flConditions V) :
    ForcingCompatible (flConditions V) (flOrder V) p q ↔
      ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z := by
  constructor
  · rintro ⟨r, hr, hrp, hrq⟩ x y z hxy hxz
    have : IsFunction r := flStage_function hr
    exact IsFunction.unique (((pair_mem_flOrder _ _).mp hrp).2.2 _ hxy)
      (((pair_mem_flOrder _ _).mp hrq).2.2 _ hxz)
  · intro hc
    have hu := flCondition_union hp hq hc
    exact ⟨p ∪ q, hu, (pair_mem_flOrder _ _).mpr ⟨hu, hp, fun z hz ↦ mem_union_iff.mpr (Or.inl hz)⟩,
      (pair_mem_flOrder _ _).mpr ⟨hu, hq, fun z hz ↦ mem_union_iff.mpr (Or.inr hz)⟩⟩

theorem zero_mem_flCardinal (m : V) : (0 : V) ∈ flCardinal m :=
  ordinal_cardLE_iff_mem_hartogsNumber.mp (cardLE_empty _)

theorem flCondition_insert {p m k v : V} (hp : p ∈ flConditions V) (hm : m ∈ (ω : V))
    (hk : k ∈ (ω : V)) (hv : v ∈ flCardinal m) (hfresh : ⟨m, k⟩ₖ ∉ domain p) :
    insert ⟨⟨m, k⟩ₖ, v⟩ₖ p ∈ flConditions V := by
  have : IsFunction p := flStage_function hp
  have hfun : IsFunction (insert ⟨⟨m, k⟩ₖ, v⟩ₖ p) := IsFunction.insert p _ v hfresh
  apply flStage_of_bounds
  · rw [domain_insert]
    exact internallyFinite_insert (flStage_finite_domain hp) _
  · rw [domain_insert]
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact kpair_mem_iff.mpr ⟨hm, hk⟩
    · exact flStage_domain hp z hz
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · simpa using hv
    · exact flStage_values hp z hz

/-- Some fresh position in column `m`. -/
theorem flCondition_fresh_position {p m : V} (hp : p ∈ flConditions V) :
    ∃ k ∈ (ω : V), ⟨m, k⟩ₖ ∉ domain p := by
  obtain ⟨k, hk, hkout⟩ := internallyFinite_fresh_natural
    (internallyFinite_repl kpair.π₂ (by definability) (flStage_finite_domain hp))
  refine ⟨k, hk, fun hmem ↦ hkout ?_⟩
  exact (repl_spec _).mpr ⟨⟨m, k⟩ₖ, hmem, by simp⟩

/-- Every value of a column is taken at some position: the collapse density. -/
theorem fl_column_value_dense {m v : V} (hm : m ∈ (ω : V)) (hv : v ∈ flCardinal m) :
    ForcingDense (flConditions V) (flOrder V)
      {p ∈ flConditions V ; ∃ k ∈ (ω : V), ⟨⟨m, k⟩ₖ, v⟩ₖ ∈ p} := by
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  obtain ⟨k, hk, hfresh⟩ := flCondition_fresh_position (m := m) hp
  have hq := flCondition_insert hp hm hk hv hfresh
  exact ⟨insert ⟨⟨m, k⟩ₖ, v⟩ₖ p, mem_sep_iff.mpr ⟨hq, k, hk, mem_insert.mpr (Or.inl rfl)⟩,
    (pair_mem_flOrder _ _).mpr ⟨hq, hp, subset_insert _ _⟩⟩

/-- Every coordinate receives a value. -/
theorem fl_coordinate_dense {m k : V} (hm : m ∈ (ω : V)) (hk : k ∈ (ω : V)) :
    ForcingDense (flConditions V) (flOrder V) {p ∈ flConditions V ; ⟨m, k⟩ₖ ∈ domain p} := by
  classical
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  by_cases hmem : ⟨m, k⟩ₖ ∈ domain p
  · exact ⟨p, mem_sep_iff.mpr ⟨hp, hmem⟩, fl_poset.1.2.1 p hp⟩
  · have hq := flCondition_insert hp hm hk (zero_mem_flCardinal m) hmem
    refine ⟨insert ⟨⟨m, k⟩ₖ, (0 : V)⟩ₖ p, mem_sep_iff.mpr ⟨hq, ?_⟩,
      (pair_mem_flOrder _ _).mpr ⟨hq, hp, subset_insert _ _⟩⟩
    exact mem_domain_of_kpair_mem (mem_insert.mpr (Or.inl rfl))

/-- Restriction to the first `n` columns. -/
theorem flRestrict_mem {p : V} (hp : p ∈ flConditions V) (n : V) :
    p ↾ (n ×ˢ (ω : V)) ∈ flStage n := by
  have : IsFunction p := flStage_function hp
  have : IsFunction (p ↾ (n ×ˢ (ω : V))) := IsFunction.ofSubset _ _ (restrict_subset _ _)
  apply flStage_of_bounds
  · exact internallyFinite_subset (flStage_finite_domain hp)
      (by rw [domain_restrict_eq]; exact fun z hz ↦ (mem_inter_iff.mp hz).1)
  · rw [domain_restrict_eq]
    exact fun z hz ↦ (mem_inter_iff.mp hz).2
  · intro z hz
    exact flStage_values hp z (restrict_subset _ _ z hz)

theorem flRestrict_le {p : V} (hp : p ∈ flConditions V) {n : V} (hn : n ∈ (ω : V)) :
    ⟨p, p ↾ (n ×ˢ (ω : V))⟩ₖ ∈ flOrder V :=
  (pair_mem_flOrder _ _).mpr ⟨hp, flStage_subset hn _ (flRestrict_mem hp n), restrict_subset _ _⟩

theorem flStage_restrict_self {n p : V} (hp : p ∈ flStage n) : p ↾ (n ×ˢ (ω : V)) = p := by
  have : IsFunction p := flStage_function hp
  apply mem_ext
  intro z
  constructor
  · intro hz
    exact (mem_restrict_iff.mp hz).1
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact mem_restrict_iff.mpr ⟨hz, x, flStage_domain hp x (mem_domain_of_kpair_mem hz), y, rfl⟩

theorem flStage_of_restrict {p n : V} (hp : p ∈ flConditions V) (h : p ↾ (n ×ˢ (ω : V)) = p) :
    p ∈ flStage n := by
  rw [← h]
  exact flRestrict_mem hp n

/-- The stage-`n` forcing is the stage forcing of the restricted cardinal sequence. -/
theorem flStage_eq_stageConditions {n : V} (hn : n ∈ (ω : V)) :
    flStage n = flStageConditions (flSequence n) := by
  have hf := (flSequence_function_domain n hn).1
  have hd := (flSequence_function_domain n hn).2
  apply mem_ext
  intro p
  constructor
  · intro hp
    have : IsFunction p := flStage_function hp
    refine (mem_flStageConditions _ _).mpr ⟨(mem_finitePartialFunctions _ _ _).mpr
      ⟨?_, inferInstance, flStage_finite_domain hp⟩, ?_⟩
    · intro z hz
      obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
      have hx : x ∈ n ×ˢ (ω : V) := flStage_domain hp x (mem_domain_of_kpair_mem hz)
      obtain ⟨m, hm, k, hk, rfl⟩ := mem_prod_iff.mp hx
      have hy := flStage_values hp _ hz
      simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hy
      rw [hd]
      refine kpair_mem_iff.mpr ⟨hx, mem_sUnion_iff.mpr ⟨flCardinal m, ?_, hy⟩⟩
      rw [← flSequence_value hn hm]
      exact mem_range_of_kpair_mem (kpair_value_mem (by rw [hd]; exact hm))
    · intro z hz
      obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
      obtain ⟨m, hm, k, hk, rfl⟩ := mem_prod_iff.mp (flStage_domain hp x (mem_domain_of_kpair_mem hz))
      have hy := flStage_values hp _ hz
      simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hy ⊢
      rwa [flSequence_value hn hm]
  · intro hp
    obtain ⟨hpf, hval⟩ := (mem_flStageConditions _ _).mp hp
    obtain ⟨hpD, hpfun, hpfin⟩ := (mem_finitePartialFunctions _ _ _).mp hpf
    have : IsFunction p := hpfun
    rw [hd] at hpD
    have hdom : domain p ⊆ n ×ˢ (ω : V) := by
      intro x hx
      obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
      exact (kpair_mem_iff.mp (hpD _ hxy)).1
    apply flStage_of_bounds hpfin hdom
    intro z hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    obtain ⟨m, hm, k, hk, rfl⟩ := mem_prod_iff.mp (hdom x (mem_domain_of_kpair_mem hz))
    have hy := hval _ hz
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hy ⊢
    rwa [flSequence_value hn hm] at hy

/-- Under choice, the nice names of stage `n` inject into the next cardinal. -/
theorem flNiceNames_cardLE (hAC : InternalChoice V) (n : V) :
    flNiceNames (flSequence n) ≤# flCardinal n :=
  (wellOrderable_iff_cardLE_hartogsNumber _).mp (wellOrderable_of_internalChoice hAC _)

end ZFVP
