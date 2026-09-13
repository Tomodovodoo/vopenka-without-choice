import ZFVP.SetTheory.OrdinalClosureClass
import ZFVP.SetTheory.CnExtendibleSmallEmbedding
import ZFVP.SetTheory.PiOneInitialOrdinal

/-! The closed unbounded class used in Bagaria's converse to Theorem 4.11.

Fix `α` and assume no ordinal above `α` is `C(k+1)`-extendible. Then the ordinals `lam` such
that every `β ∈ lam` already has a failure stage below `lam`, and such that `C(k+2)` stages are
cofinal in `lam`, form a closed unbounded class of `C(k+2)` ordinals. The defining formula is
`Pi_{k+2}`: all its quantifiers over `lam` are bounded, and each matrix piece is `Pi_{k+2}`.

Nothing here uses Vopenka's principle. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The `Pi_{k+2}` formula for `IsGoodClosurePoint k`. Free variables: `lam`, `α`. -/
def goodClosurePointFormula (k : ℕ) : SetTheorySemisentence 2 :=
  “lam α. !IsOrdinal.dfn lam ∧ (∃ z ∈ lam, ⊤) ∧
    (∀ β ∈ lam, ∃ μ ∈ lam, !(cnFormula (k + 1)) μ ∧ β ∈ μ ∧
      (¬!piOneInitialOrdinalFormula β ∨ ¬(α ∈ β) ∨
        ¬!(positiveCnExtendibleWitnessFormula k) β μ)) ∧
    (∀ β ∈ lam, ∃ μ ∈ lam, !(cnFormula (k + 2)) μ ∧ β ∈ μ)”

theorem goodClosurePointFormula_pi (k : ℕ) : IsPiFormula (k + 2) (goodClosurePointFormula k) := by
  refine .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.and (.bounded (.exs (.bvar 0) .verum)) (.and ?_ ?_))
  · refine .boundedAll (.bvar 0) (.boundedExs (.bvar 1) ?_)
    refine .and (((cnFormula_pi_bound (k + 1)).subst _).mono (Nat.max_le.mpr ⟨by omega, by omega⟩))
      (.and (.bounded (.rel _ _)) ?_)
    refine .or ((piOneInitialOrdinalFormula_piOne.subst _).neg.raise.mono (by omega))
      (.or (.bounded (IsBoundedSetFormula.rel _ _).neg)
        ((positiveCnExtendibleWitnessFormula_sigma k).subst _).neg)
  · refine .boundedAll (.bvar 0) (.boundedExs (.bvar 1) ?_)
    exact .and (((cnFormula_pi_bound (k + 2)).subst _).mono (Nat.max_le.mpr ⟨by omega, by omega⟩))
      (.bounded (.rel _ _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `β` is a possible `C(n)`-extendible cardinal above `α`. -/
def IsExtendibilityCandidate (α β : V) : Prop := IsInitialOrdinal β ∧ α ∈ β

/-- `μ` witnesses that `β` is not `C(k+1)`-extendible, or that `β` was never a candidate. -/
def IsFailureStage (k : ℕ) (α β μ : V) : Prop :=
  Cn (k + 1) μ ∧ β ∈ μ ∧ (¬ IsExtendibilityCandidate α β ∨ ¬ CnExtendibleWitness (k + 1) β μ)

/-- An ordinal that sees a failure stage for each of its elements, and has `C(k+2)` stages
cofinally below it. -/
def IsGoodClosurePoint (k : ℕ) (α lam : V) : Prop :=
  IsOrdinal lam ∧ IsNonempty lam ∧
    (∀ β ∈ lam, ∃ μ ∈ lam, IsFailureStage k α β μ) ∧
    (∀ β ∈ lam, ∃ μ ∈ lam, Cn (k + 2) μ ∧ β ∈ μ)

theorem goodClosurePointFormula_defines (k : ℕ) :
    Defined (fun v : Fin 2 → V ↦ IsGoodClosurePoint k (v 1) (v 0)) (goodClosurePointFormula k) := by
  refine ⟨fun v ↦ ?_⟩
  simp only [goodClosurePointFormula, IsGoodClosurePoint, IsFailureStage,
    IsExtendibilityCandidate]
  simp
  intro _
  classical
  have hkey : ∀ β μ : V,
      ((¬IsInitialOrdinal β ∨ v 1 ∉ β ∨ ¬CnExtendibleWitness (k + 1) β μ) ↔
        ((IsInitialOrdinal β → v 1 ∉ β) ∨ ¬CnExtendibleWitness (k + 1) β μ)) := by
    intro β μ
    tauto
  constructor
  · rintro ⟨hne, h3, h4⟩
    refine ⟨isNonempty_def.mpr hne, ?_, h4⟩
    intro β hβ
    obtain ⟨μ, hμ, h1, h2, h3'⟩ := h3 β hβ
    exact ⟨μ, hμ, h1, h2, (hkey β μ).mp h3'⟩
  · rintro ⟨hne, h3, h4⟩
    refine ⟨isNonempty_def.mp hne, ?_, h4⟩
    intro β hβ
    obtain ⟨μ, hμ, h1, h2, h3'⟩ := h3 β hβ
    exact ⟨μ, hμ, h1, h2, (hkey β μ).mpr h3'⟩

/-! ### Basic consequences -/

theorem IsGoodClosurePoint.cn {k : ℕ} {α lam : V} (h : IsGoodClosurePoint k α lam) :
    Cn (k + 2) lam := by
  have : IsOrdinal lam := h.1
  refine cn_closed (k + 2) h.2.1 ?_
  intro ξ hξ
  obtain ⟨μ, hμ, hcn, hξμ⟩ := h.2.2.2 ξ hξ
  exact ⟨μ, hμ, hξμ, hcn⟩

theorem IsGoodClosurePoint.limit {k : ℕ} {α lam : V} (h : IsGoodClosurePoint k α lam) :
    IsLimitOrdinal lam := by
  refine ⟨h.1, ne_empty_iff_isNonempty.mpr h.2.1, ?_⟩
  rintro ⟨β, rfl⟩
  have hs : IsOrdinal (succ β) := h.1
  have hβ : β ∈ succ β := mem_succ_self β
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  obtain ⟨μ, hμ, _, hβμ⟩ := h.2.2.2 β hβ
  rcases mem_succ_iff.mp hμ with he | hlt
  · exact mem_irrefl β (he ▸ hβμ)
  · exact mem_irrefl β (IsOrdinal.toIsTransitive.mem_trans hβμ hlt)

theorem IsGoodClosurePoint.failure_stage {k : ℕ} {α lam β : V} (h : IsGoodClosurePoint k α lam)
    (hβ : β ∈ lam) (hc : IsExtendibilityCandidate α β) :
    ∃ μ ∈ lam, Cn (k + 1) μ ∧ β ∈ μ ∧ ¬ CnExtendibleWitness (k + 1) β μ := by
  obtain ⟨μ, hμ, hcn, hβμ, hdis⟩ := h.2.2.1 β hβ
  rcases hdis with hbad | hgood
  · exact absurd hc hbad
  · exact ⟨μ, hμ, hcn, hβμ, hgood⟩

/-- The class of good closure points is closed. -/
theorem goodClosurePoint_of_unbounded {k : ℕ} {α κ : V} [IsOrdinal κ] (hne : IsNonempty κ)
    (hub : ∀ ξ ∈ κ, ∃ lam ∈ κ, ξ ∈ lam ∧ IsGoodClosurePoint k α lam) :
    IsGoodClosurePoint k α κ := by
  refine ⟨inferInstance, hne, ?_, ?_⟩
  · intro β hβ
    obtain ⟨lam, hlam, hβlam, hg⟩ := hub β hβ
    obtain ⟨μ, hμ, hf⟩ := hg.2.2.1 β hβlam
    exact ⟨μ, IsOrdinal.toIsTransitive.mem_trans hμ hlam, hf⟩
  · intro β hβ
    obtain ⟨lam, hlam, hβlam, hg⟩ := hub β hβ
    obtain ⟨μ, hμ, hcn, hβμ⟩ := hg.2.2.2 β hβlam
    exact ⟨μ, IsOrdinal.toIsTransitive.mem_trans hμ hlam, hcn, hβμ⟩

/-! ### Unboundedness -/

/-- One value of the class function whose closure points are the good closure points: a `C(k+2)`
stage above `β` that already contains a failure stage for `β`. -/
def GoodStep (k : ℕ) (α β μ : V) : Prop :=
  β ∈ μ ∧ Cn (k + 2) μ ∧ ∃ ν ∈ μ, IsFailureStage k α β ν

theorem goodStep_definable_pred (k : ℕ) (α β : V) : ℒₛₑₜ-predicate[V] (GoodStep k α β) := by
  unfold GoodStep IsFailureStage IsExtendibilityCandidate
  definability

/-- Under the failure hypothesis every ordinal has a failure stage. -/
theorem exists_isFailureStage {k : ℕ} {α : V}
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ)
    (β : V) [IsOrdinal β] : ∃ μ : V, IsFailureStage k α β μ := by
  classical
  by_cases hc : IsExtendibilityCandidate α β
  · by_contra hcon
    refine hno β hc.2 ⟨hc.1, ?_⟩
    intro μ hμ hβμ
    by_contra hw
    exact hcon ⟨μ, hμ, hβμ, Or.inr fun hW ↦ hw hW.2⟩
  · obtain ⟨μ, hβμ, hμ⟩ := cn_unbounded (k + 1) β
    exact ⟨μ, hμ, hβμ, Or.inl hc⟩

theorem exists_goodStep {k : ℕ} {α : V}
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ)
    (β : V) [IsOrdinal β] : ∃ μ : V, IsOrdinal μ ∧ GoodStep k α β μ := by
  obtain ⟨ν, hν⟩ := exists_isFailureStage hno β
  have : IsOrdinal ν := hν.1.ordinal
  obtain ⟨μ, hνμ, hμ⟩ := cn_unbounded (k + 2) ν
  have : IsOrdinal μ := hμ.ordinal
  exact ⟨μ, hμ.ordinal, IsOrdinal.toIsTransitive.mem_trans hν.2.1 hνμ, hμ, ν, hνμ, hν⟩

theorem goodStep_existsUnique (k : ℕ) (α β : V)
    (h : ∃ μ : V, IsOrdinal μ ∧ GoodStep k α β μ) :
    ∃! μ, IsLeastOrdinal (GoodStep k α β) μ :=
  leastOrdinal_existsUnique _ (goodStep_definable_pred k α β) h

/-- The least `C(k+2)` stage above `β` containing a failure stage for `β`, and `∅` when there is
none. -/
noncomputable def goodStep (k : ℕ) (α β : V) : V := by
  classical
  exact if h : ∃ μ : V, IsOrdinal μ ∧ GoodStep k α β μ then
    Classical.choose! (goodStep_existsUnique k α β h) else ∅

theorem goodStep_eq_iff (k : ℕ) (α β μ : V) :
    goodStep k α β = μ ↔ IsLeastOrdinal (GoodStep k α β) μ ∨
      ((¬∃ ν : V, IsOrdinal ν ∧ GoodStep k α β ν) ∧ μ = ∅) := by
  classical
  by_cases h : ∃ ν : V, IsOrdinal ν ∧ GoodStep k α β ν
  · simp only [h, not_true_eq_false, false_and, or_false]
    have hspec : IsLeastOrdinal (GoodStep k α β) (goodStep k α β) := by
      simpa [goodStep, h] using Classical.choose!_spec (goodStep_existsUnique k α β h)
    constructor
    · rintro rfl
      exact hspec
    · intro hμ
      exact (goodStep_existsUnique k α β h).unique hspec hμ
  · have hn : ¬IsLeastOrdinal (GoodStep k α β) μ := fun hl ↦ h ⟨μ, hl.1, hl.2.1⟩
    simp [goodStep, h, hn, eq_comm]

theorem goodStep_definable (k : ℕ) (α : V) : ℒₛₑₜ-function₁ (goodStep k α) := by
  have h : ℒₛₑₜ-relation (fun μ β : V ↦ IsLeastOrdinal (GoodStep k α β) μ ∨
      ((¬∃ ν : V, IsOrdinal ν ∧ GoodStep k α β ν) ∧ μ = ∅)) := by
    unfold IsLeastOrdinal GoodStep IsFailureStage IsExtendibilityCandidate
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (goodStep_eq_iff k α (v 1) (v 0))

theorem goodStep_spec {k : ℕ} {α : V}
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ)
    (β : V) [IsOrdinal β] : IsLeastOrdinal (GoodStep k α β) (goodStep k α β) := by
  rcases (goodStep_eq_iff k α β (goodStep k α β)).mp rfl with h | ⟨h, -⟩
  · exact h
  · exact absurd (exists_goodStep hno β) h

theorem goodStep_isOrdinal {k : ℕ} {α : V}
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ)
    (β : V) [IsOrdinal β] : IsOrdinal (goodStep k α β) := (goodStep_spec hno β).1

theorem mem_goodStep {k : ℕ} {α : V}
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ)
    (β : V) [IsOrdinal β] : β ∈ goodStep k α β := (goodStep_spec hno β).2.1.1

/-- Above every ordinal there is a good closure point. -/
theorem exists_goodClosurePoint_above {k : ℕ} {α : V} [IsOrdinal α]
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ)
    (γ : V) [IsOrdinal γ] : ∃ lam : V, γ ∈ lam ∧ IsGoodClosurePoint k α lam := by
  obtain ⟨lam, hγ, hlam⟩ := exists_ordinalClosurePoint_above (goodStep_definable k α)
    (fun ξ hξ ↦ have : IsOrdinal ξ := hξ; goodStep_isOrdinal hno ξ)
    (fun ξ hξ ↦ have : IsOrdinal ξ := hξ; mem_goodStep hno ξ) γ
  have hord : IsOrdinal lam := hlam.1
  refine ⟨lam, hγ, hord, hlam.2.1, ?_, ?_⟩
  · intro β hβ
    have : IsOrdinal β := IsOrdinal.of_mem hβ
    have hstep : goodStep k α β ∈ lam := hlam.2.2 β hβ
    obtain ⟨-, -, ν, hν, hfail⟩ := (goodStep_spec hno β).2.1
    exact ⟨ν, IsOrdinal.toIsTransitive.mem_trans hν hstep, hfail⟩
  · intro β hβ
    have : IsOrdinal β := IsOrdinal.of_mem hβ
    have hstep : goodStep k α β ∈ lam := hlam.2.2 β hβ
    obtain ⟨hβμ, hcn, -⟩ := (goodStep_spec hno β).2.1
    exact ⟨goodStep k α β, hstep, hcn, hβμ⟩

end ZFVP
