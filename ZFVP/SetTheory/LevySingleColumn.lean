import ZFVP.SetTheory.LevyColumnSplitting
import ZFVP.SetTheory.SetCollapse

/-! A single column `λ` of the Levy collapse is the collapse `Coll(ω, λ)`: the maps forgetting and
restoring the column index are inverse dense embeddings. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Forget the column index: `⟨⟨n, λ⟩, γ⟩ ↦ ⟨n, γ⟩`. -/
noncomputable def columnToCollapse (p : V) : V :=
  repl (fun z ↦ ⟨kpair.π₁ (kpair.π₁ z), kpair.π₂ z⟩ₖ) (by definability) p

theorem columnToCollapse_definable : ℒₛₑₜ-function₁[V] columnToCollapse := by
  have h : ℒₛₑₜ-relation (fun q p : V ↦ ∀ w, w ∈ q ↔ ∃ z ∈ p, w = ⟨kpair.π₁ (kpair.π₁ z), kpair.π₂ z⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = columnToCollapse (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [columnToCollapse, repl_spec]

/-- Restore the column index: `⟨n, γ⟩ ↦ ⟨⟨n, λ⟩, γ⟩`. -/
noncomputable def collapseToColumn (lam q : V) : V :=
  repl (fun z ↦ ⟨⟨kpair.π₁ z, lam⟩ₖ, kpair.π₂ z⟩ₖ) (by definability) q

theorem collapseToColumn_definable (lam : V) : ℒₛₑₜ-function₁[V] (collapseToColumn lam) := by
  have h : ℒₛₑₜ-relation (fun p q : V ↦ ∀ w, w ∈ p ↔ ∃ z ∈ q, w = ⟨⟨kpair.π₁ z, lam⟩ₖ, kpair.π₂ z⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = collapseToColumn lam (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [collapseToColumn, repl_spec]

section

variable {κ lam : V} [IsOrdinal κ] (hlam : lam ∈ κ)

theorem mem_column_shape {p z : V} (hp : p ∈ levyColumns κ ({lam} : V)) (hz : z ∈ p) :
    ∃ n γ : V, n ∈ (ω : V) ∧ γ ∈ lam ∧ z = ⟨⟨n, lam⟩ₖ, γ⟩ₖ := by
  have hpL := levyColumns_subset κ _ p hp
  obtain ⟨n, α, γ, hn, _, rfl⟩ := levyCollapse_mem_shape hpL hz
  have hα : α = lam := mem_singleton_iff.mp (column_mem_of_levyColumns hp hz)
  subst hα
  exact ⟨n, γ, hn, ((mem_levyCollapse_iff κ p).mp hpL).2 n α γ hz, rfl⟩

theorem pair_mem_columnToCollapse_iff {p : V} (hp : p ∈ levyColumns κ ({lam} : V)) (n γ : V) :
    ⟨n, γ⟩ₖ ∈ columnToCollapse p ↔ ⟨⟨n, lam⟩ₖ, γ⟩ₖ ∈ p := by
  unfold columnToCollapse
  rw [repl_spec]
  constructor
  · rintro ⟨z, hz, he⟩
    obtain ⟨n', γ', _, _, rfl⟩ := mem_column_shape hp hz
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at he
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact hz
  · intro h
    exact ⟨_, h, by simp only [kpair.π₁_kpair, kpair.π₂_kpair]⟩

theorem mem_columnToCollapse_shape {p w : V} (hp : p ∈ levyColumns κ ({lam} : V)) (hw : w ∈ columnToCollapse p) :
    ∃ n γ : V, n ∈ (ω : V) ∧ γ ∈ lam ∧ w = ⟨n, γ⟩ₖ ∧ ⟨⟨n, lam⟩ₖ, γ⟩ₖ ∈ p := by
  obtain ⟨z, hz, rfl⟩ := (repl_spec _).mp hw
  obtain ⟨n, γ, hn, hγ, rfl⟩ := mem_column_shape hp hz
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  exact ⟨n, γ, hn, hγ, rfl, hz⟩

/-- The collapse image of a column condition is a condition of `Coll(ω, λ)`. -/
theorem columnToCollapse_mem {p : V} (hp : p ∈ levyColumns κ ({lam} : V)) :
    columnToCollapse p ∈ collapseConditions lam := by
  have hpL := levyColumns_subset κ _ p hp
  have hpf := levyCollapse_finitePartialFunction hpL
  obtain ⟨_, hpfun, hpfin⟩ := (mem_finitePartialFunctions _ _ _).mp hpf
  refine (mem_finitePartialFunctions _ _ _).mpr ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨n, γ, hn, hγ, rfl, _⟩ := mem_columnToCollapse_shape hp hw
    exact kpair_mem_iff.mpr ⟨hn, hγ⟩
  · apply isFunction_iff.mpr
    apply mem_function.intro
    · intro w hw
      obtain ⟨n, γ, _, _, rfl, _⟩ := mem_columnToCollapse_shape hp hw
      exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hw, mem_range_of_kpair_mem hw⟩
    · intro n hn
      obtain ⟨γ, hγ⟩ := mem_domain_iff.mp hn
      refine ⟨γ, hγ, fun γ' hγ' ↦ ?_⟩
      rw [pair_mem_columnToCollapse_iff hp] at hγ hγ'
      exact IsFunction.unique hγ' hγ
  · apply internallyFinite_subset (internallyFinite_repl (fun x ↦ kpair.π₁ x) (by definability) hpfin)
    intro n hn
    obtain ⟨γ, hγ⟩ := mem_domain_iff.mp hn
    rw [pair_mem_columnToCollapse_iff hp] at hγ
    exact (repl_spec _).mpr ⟨⟨n, lam⟩ₖ, mem_domain_of_kpair_mem hγ, by simp⟩

theorem pair_mem_collapseToColumn_iff {q : V} (hq : q ∈ collapseConditions lam) (n α γ : V) :
    ⟨⟨n, α⟩ₖ, γ⟩ₖ ∈ collapseToColumn lam q ↔ α = lam ∧ ⟨n, γ⟩ₖ ∈ q := by
  unfold collapseToColumn
  rw [repl_spec]
  constructor
  · rintro ⟨z, hz, he⟩
    have hz' := ((mem_finitePartialFunctions _ _ _).mp hq).1 z hz
    obtain ⟨n', _, γ', _, rfl⟩ := mem_prod_iff.mp hz'
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at he
    obtain ⟨h1, rfl⟩ := kpair_iff.mp he
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp h1
    exact ⟨rfl, hz⟩
  · rintro ⟨rfl, h⟩
    exact ⟨_, h, by simp only [kpair.π₁_kpair, kpair.π₂_kpair]⟩

theorem mem_collapseToColumn_shape {q w : V} (hq : q ∈ collapseConditions lam) (hw : w ∈ collapseToColumn lam q) :
    ∃ n γ : V, n ∈ (ω : V) ∧ γ ∈ lam ∧ w = ⟨⟨n, lam⟩ₖ, γ⟩ₖ ∧ ⟨n, γ⟩ₖ ∈ q := by
  obtain ⟨z, hz, rfl⟩ := (repl_spec _).mp hw
  have hz' := ((mem_finitePartialFunctions _ _ _).mp hq).1 z hz
  obtain ⟨n, hn, γ, hγ, rfl⟩ := mem_prod_iff.mp hz'
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  exact ⟨n, γ, hn, hγ, rfl, hz⟩

include hlam in
/-- The column image of a condition of `Coll(ω, λ)` is a condition on the column `λ`. -/
theorem collapseToColumn_mem {q : V} (hq : q ∈ collapseConditions lam) :
    collapseToColumn lam q ∈ levyColumns κ ({lam} : V) := by
  obtain ⟨_, hqfun, hqfin⟩ := (mem_finitePartialFunctions _ _ _).mp hq
  have hlamsub : lam ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hlam
  refine (mem_levyColumns_iff _ _ _).mpr ⟨?_, ?_⟩
  · refine (mem_levyCollapse_iff κ _).mpr ⟨(mem_finitePartialFunctions _ _ _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · intro w hw
      obtain ⟨n, γ, hn, hγ, rfl, _⟩ := mem_collapseToColumn_shape hq hw
      exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hn, hlam⟩, hlamsub γ hγ⟩
    · apply isFunction_iff.mpr
      apply mem_function.intro
      · intro w hw
        obtain ⟨n, γ, _, _, rfl, _⟩ := mem_collapseToColumn_shape hq hw
        exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hw, mem_range_of_kpair_mem hw⟩
      · intro x hx
        obtain ⟨γ, hγ⟩ := mem_domain_iff.mp hx
        obtain ⟨n, γ', _, _, he, _⟩ := mem_collapseToColumn_shape hq hγ
        obtain ⟨hx', _⟩ := kpair_iff.mp he
        subst hx'
        refine ⟨γ, hγ, fun γ'' hγ'' ↦ ?_⟩
        rw [pair_mem_collapseToColumn_iff hq] at hγ hγ''
        exact IsFunction.unique hγ''.2 hγ.2
    · apply internallyFinite_subset (internallyFinite_repl (fun n ↦ ⟨n, lam⟩ₖ) (by definability) hqfin)
      intro x hx
      obtain ⟨γ, hγ⟩ := mem_domain_iff.mp hx
      obtain ⟨n, γ', _, _, he, hq'⟩ := mem_collapseToColumn_shape hq hγ
      obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
      exact (repl_spec _).mpr ⟨n, mem_domain_of_kpair_mem hq', rfl⟩
    · intro n α γ h
      obtain ⟨rfl, hnγ⟩ := (pair_mem_collapseToColumn_iff hq n α γ).mp h
      exact (kpair_mem_iff.mp (((mem_finitePartialFunctions _ _ _).mp hq).1 _ hnγ)).2
  · apply SetTheory.subset_antisymm (levyCut_subset _ _)
    intro w hw
    obtain ⟨n, γ, hn, _, rfl, _⟩ := mem_collapseToColumn_shape hq hw
    exact (kpair_mem_levyCut_iff _ _ _ _).mpr ⟨hw, kpair_mem_iff.mpr ⟨hn, mem_singleton_iff.mpr rfl⟩⟩

theorem columnToCollapse_collapseToColumn {q : V} (hq : q ∈ collapseConditions lam) :
    columnToCollapse (collapseToColumn lam q) = q := by
  apply mem_ext
  intro w
  constructor
  · intro hw
    obtain ⟨z, hz, rfl⟩ := (repl_spec _).mp hw
    obtain ⟨n, γ, _, _, rfl, hnγ⟩ := mem_collapseToColumn_shape hq hz
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hnγ
  · intro hw
    have hw' := ((mem_finitePartialFunctions _ _ _).mp hq).1 w hw
    obtain ⟨n, _, γ, _, rfl⟩ := mem_prod_iff.mp hw'
    refine (repl_spec _).mpr ⟨⟨⟨n, lam⟩ₖ, γ⟩ₖ, (pair_mem_collapseToColumn_iff hq n lam γ).mpr ⟨rfl, hw⟩, ?_⟩
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]

theorem collapseToColumn_columnToCollapse {p : V} (hp : p ∈ levyColumns κ ({lam} : V)) :
    collapseToColumn lam (columnToCollapse p) = p := by
  apply mem_ext
  intro w
  constructor
  · intro hw
    obtain ⟨z, hz, rfl⟩ := (repl_spec _).mp hw
    obtain ⟨n, γ, _, _, rfl, hnγ⟩ := mem_columnToCollapse_shape hp hz
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hnγ
  · intro hw
    obtain ⟨n, γ, _, _, rfl⟩ := mem_column_shape hp hw
    refine (repl_spec _).mpr ⟨⟨n, γ⟩ₖ, (pair_mem_columnToCollapse_iff hp n γ).mpr hw, ?_⟩
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]

theorem columnToCollapse_mono {p q : V} (h : q ⊆ p) : columnToCollapse q ⊆ columnToCollapse p := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := (repl_spec _).mp hw
  exact (repl_spec _).mpr ⟨z, h z hz, rfl⟩

theorem collapseToColumn_mono {p q : V} (h : q ⊆ p) : collapseToColumn lam q ⊆ collapseToColumn lam p := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := (repl_spec _).mp hw
  exact (repl_spec _).mpr ⟨z, h z hz, rfl⟩

/-- Forgetting the column index as a set function on the column. -/
noncomputable def columnToCollapseMap (κ lam : V) : V :=
  definableGraph (levyColumns κ ({lam} : V)) columnToCollapse columnToCollapse_definable

/-- Restoring the column index as a set function on `Coll(ω, λ)`. -/
noncomputable def collapseToColumnMap (lam : V) : V :=
  definableGraph (collapseConditions lam) (collapseToColumn lam) (collapseToColumn_definable lam)

include hlam in
/-- The column `λ` embeds densely (isomorphically) into `Coll(ω, λ)`. -/
theorem columnToCollapseMap_denseEmbedding :
    IsDenseEmbedding (levyColumns κ ({lam} : V)) (levyColumnsOrder κ ({lam} : V))
      (collapseConditions lam) (collapseOrder lam) (columnToCollapseMap κ lam) := by
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ (fun p hp ↦ columnToCollapse_mem hp), ?_, ?_, ?_⟩
  · intro p hp q hq hqp
    obtain ⟨_, _, hpq⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hqp
    unfold columnToCollapseMap
    rw [value_definableGraph _ _ _ hp, value_definableGraph _ _ _ hq]
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨columnToCollapse_mem hq, columnToCollapse_mem hp,
      columnToCollapse_mono hpq⟩
  · intro p hp q hq hinc hc
    unfold columnToCollapseMap at hc
    rw [value_definableGraph _ _ _ hp, value_definableGraph _ _ _ hq] at hc
    obtain ⟨r, hr, hr1, hr2⟩ := hc
    obtain ⟨_, _, h1⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hr1
    obtain ⟨_, _, h2⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hr2
    apply hinc
    refine ⟨collapseToColumn lam r, collapseToColumn_mem hlam hr, ?_, ?_⟩
    · refine (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨collapseToColumn_mem hlam hr, hp, ?_⟩
      rw [← collapseToColumn_columnToCollapse hp]
      exact collapseToColumn_mono h1
    · refine (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨collapseToColumn_mem hlam hr, hq, ?_⟩
      rw [← collapseToColumn_columnToCollapse hq]
      exact collapseToColumn_mono h2
  · intro q hq
    refine ⟨collapseToColumn lam q, collapseToColumn_mem hlam hq, ?_⟩
    unfold columnToCollapseMap
    rw [value_definableGraph _ _ _ (collapseToColumn_mem hlam hq), columnToCollapse_collapseToColumn hq]
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hq, fun z hz ↦ hz⟩

include hlam in
/-- `Coll(ω, λ)` embeds densely (isomorphically) into the column `λ`. -/
theorem collapseToColumnMap_denseEmbedding :
    IsDenseEmbedding (collapseConditions lam) (collapseOrder lam) (levyColumns κ ({lam} : V))
      (levyColumnsOrder κ ({lam} : V)) (collapseToColumnMap lam) := by
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ (fun q hq ↦ collapseToColumn_mem hlam hq), ?_, ?_, ?_⟩
  · intro p hp q hq hqp
    obtain ⟨_, _, hpq⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hqp
    unfold collapseToColumnMap
    rw [value_definableGraph _ _ _ hp, value_definableGraph _ _ _ hq]
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨collapseToColumn_mem hlam hq, collapseToColumn_mem hlam hp,
      collapseToColumn_mono hpq⟩
  · intro p hp q hq hinc hc
    unfold collapseToColumnMap at hc
    rw [value_definableGraph _ _ _ hp, value_definableGraph _ _ _ hq] at hc
    obtain ⟨r, hr, hr1, hr2⟩ := hc
    obtain ⟨_, _, h1⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hr1
    obtain ⟨_, _, h2⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hr2
    apply hinc
    refine ⟨columnToCollapse r, columnToCollapse_mem hr, ?_, ?_⟩
    · refine (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨columnToCollapse_mem hr, hp, ?_⟩
      rw [← columnToCollapse_collapseToColumn hp]
      exact columnToCollapse_mono h1
    · refine (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨columnToCollapse_mem hr, hq, ?_⟩
      rw [← columnToCollapse_collapseToColumn hq]
      exact columnToCollapse_mono h2
  · intro p hp
    refine ⟨columnToCollapse p, columnToCollapse_mem hp, ?_⟩
    unfold collapseToColumnMap
    rw [value_definableGraph _ _ _ (columnToCollapse_mem hp), collapseToColumn_columnToCollapse hp]
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hp, fun z hz ↦ hz⟩

end

end ZFVP
