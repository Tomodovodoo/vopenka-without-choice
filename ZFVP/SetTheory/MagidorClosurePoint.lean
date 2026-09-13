import ZFVP.SetTheory.MagidorFailureClassFormula
import ZFVP.SetTheory.FormulaFamilyRank

/-! # Closure points of the Magidor failure function

The `Pi_1` case of Bagaria's Theorem 4.3(2) indexes its class of structures by an ordinal `lam`.
Bagaria takes `lam` to be the least limit ordinal above a marker at which no cardinal of an
interval is `<lam`-supercompact. With that index condition the proof of Magidor's Lemma 3.1 has to
iterate the embedding produced by Vopenka's principle, and the composite of a coded embedding
`V_{lam+ω} → V_{lam'+ω}` with itself is only defined on the part of the source whose forward orbit
stays inside the source (see `ZFVP.SetTheory.MagidorIterationReach`).

This module supplies the other index condition, the one the `C(n)` case of the same theorem uses
(`ZFVP.SetTheory.PiVopenkaCnExtendible`, on top of `ZFVP.SetTheory.GoodLimitPointClass`): index the
class by closure points of the failure function. `magidorFailure ρ ν` is the least ordinal above
`ν` at which the small-embedding property of `ν` fails, and `IsMagidorClosurePoint ρ d` says that
`d` is a limit ordinal above `ρ` closed under that function. At such a `d` the failure stage of any
`κ ∈ d` above `ρ` is again below `d`, hence below the image of a critical point sent to `d` by one
embedding, and one step of the embedding is all the reflection needs.

The escape clause `¬ ρ ⊆ ν` in `MagidorFailureAt` makes the least failure stage defined at every
ordinal, so `magidorFailure` is a definable class function and replacement gives closure points
above every ordinal. That is the trick of `ZFVP.SetTheory.MagidorFailureStages`, with the extra
interval bound `ν ⊆ r` of that module dropped.

Part 2 turns the closure point condition into a bounded formula with the stage argument `W`, on
the model of `ZFVP.SetTheory.MagidorFailureClassFormula`, and Part 3 transfers both the condition
and the value of `magidorFailure` along a coded embedding between two `V_{lam+ω}` stages. Read
literally the small-embedding predicate is `Sigma_1` at best and it appears here under a negation,
so the bounded reading is what makes the transfer work. No `C(n)` and no correctness hypothesis
appears anywhere: the stages are `V_{lam+ω}`, never assumed to be in `C(1)`.

The hypothesis `MagidorFailureTotal ρ` says that every ordinal above `ρ` has a failure stage at
all. It is needed because otherwise `magidorFailure ρ ν` falls back to `∅` and the bounded formula,
which asks for a genuine least failure stage, is not equivalent to membership of that fallback
value. `magidorFailureTotal_of_no_supercompact` discharges it from the hypothesis the main argument
carries, that no ordinal above `ξ` is Magidor supercompact, with `ρ = succ ξ`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## Part 1: the set theory -/

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `γ` is an ordinal above `ν` at which the small embedding for `ν` fails, or `ν` lies below `ρ`
and `γ` is any ordinal above `ν`. The escape clause makes the least such `γ` defined at every
ordinal. -/
def MagidorFailureAt (ρ ν γ : V) : Prop :=
  IsOrdinal γ ∧ ν ∈ γ ∧ (¬ ρ ⊆ ν ∨ ¬ IsMagidorSupercompactAt ν γ)

instance magidorFailureAt_definable : ℒₛₑₜ-relation₃[V] MagidorFailureAt := by
  unfold MagidorFailureAt
  definability

theorem magidorFailureAt_definable_pred (ρ ν : V) : ℒₛₑₜ-predicate[V] (MagidorFailureAt ρ ν) := by
  unfold MagidorFailureAt
  definability

theorem magidorFailure_existsUnique (ρ ν : V)
    (h : ∃ γ : V, IsOrdinal γ ∧ MagidorFailureAt ρ ν γ) :
    ∃! γ, IsLeastOrdinal (MagidorFailureAt ρ ν) γ :=
  leastOrdinal_existsUnique _ (magidorFailureAt_definable_pred ρ ν) h

/-- The least failure stage of `ν` above `ρ`, and `∅` when there is none. -/
noncomputable def magidorFailure (ρ ν : V) : V := by
  classical
  exact if h : ∃ γ : V, IsOrdinal γ ∧ MagidorFailureAt ρ ν γ then
    Classical.choose! (magidorFailure_existsUnique ρ ν h) else ∅

theorem magidorFailure_eq_iff (ρ ν γ : V) :
    magidorFailure ρ ν = γ ↔ IsLeastOrdinal (MagidorFailureAt ρ ν) γ ∨
      ((¬∃ δ : V, IsOrdinal δ ∧ MagidorFailureAt ρ ν δ) ∧ γ = ∅) := by
  classical
  by_cases h : ∃ δ : V, IsOrdinal δ ∧ MagidorFailureAt ρ ν δ
  · simp only [h, not_true_eq_false, false_and, or_false]
    have hspec : IsLeastOrdinal (MagidorFailureAt ρ ν) (magidorFailure ρ ν) := by
      simpa [magidorFailure, h] using Classical.choose!_spec (magidorFailure_existsUnique ρ ν h)
    constructor
    · rintro rfl
      exact hspec
    · intro hγ
      exact (magidorFailure_existsUnique ρ ν h).unique hspec hγ
  · have hn : ¬IsLeastOrdinal (MagidorFailureAt ρ ν) γ := fun hl ↦ h ⟨γ, hl.1, hl.2.1⟩
    simp [magidorFailure, h, hn, eq_comm]

/-- The graph of `magidorFailure`, as a three place relation. -/
def MagidorFailureGraph (ρ ν γ : V) : Prop := magidorFailure ρ ν = γ

instance magidorFailureGraph_definable : ℒₛₑₜ-relation₃[V] MagidorFailureGraph := by
  have h : ℒₛₑₜ-relation₃[V] (fun ρ ν γ : V ↦ IsLeastOrdinal (MagidorFailureAt ρ ν) γ ∨
      ((¬∃ δ : V, IsOrdinal δ ∧ MagidorFailureAt ρ ν δ) ∧ γ = ∅)) := by
    unfold IsLeastOrdinal MagidorFailureAt
    definability
  apply Language.Definable.of_iff h
  intro v
  exact magidorFailure_eq_iff (v 0) (v 1) (v 2)

theorem magidorFailure_definable (ρ : V) : ℒₛₑₜ-function₁ (magidorFailure ρ) := by
  have h : ℒₛₑₜ-relation (fun γ ν : V ↦ IsLeastOrdinal (MagidorFailureAt ρ ν) γ ∨
      ((¬∃ δ : V, IsOrdinal δ ∧ MagidorFailureAt ρ ν δ) ∧ γ = ∅)) := by
    unfold IsLeastOrdinal MagidorFailureAt
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (magidorFailure_eq_iff ρ (v 1) (v 0))

/-! ### Totality of the failure stage -/

/-- Every ordinal above `ρ` fails the small-embedding property at some rank. -/
def MagidorFailureTotal (ρ : V) : Prop :=
  ∀ ν : V, IsOrdinal ν → ρ ⊆ ν → ∃ γ : V, IsOrdinal γ ∧ MagidorFailureAt ρ ν γ

/-- With the escape clause, totality above `ρ` gives a failure stage at every ordinal. -/
theorem exists_magidorFailureAt {ρ : V} (htot : MagidorFailureTotal ρ) (ν : V) [IsOrdinal ν] :
    ∃ γ : V, IsOrdinal γ ∧ MagidorFailureAt ρ ν γ := by
  classical
  by_cases hc : ρ ⊆ ν
  · exact htot ν inferInstance hc
  · exact ⟨succ ν, inferInstance, inferInstance, mem_succ_self ν, Or.inl hc⟩

/-- If no ordinal above `ξ` is Magidor supercompact then the failure stage is total above
`succ ξ`. -/
theorem magidorFailureTotal_of_no_supercompact {ξ : V} [IsOrdinal ξ]
    (hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ) : MagidorFailureTotal (succ ξ : V) := by
  intro ν hν hρν
  have : IsOrdinal ν := hν
  have hξν : ξ ∈ ν := hρν ξ (mem_succ_self ξ)
  by_contra hcon
  push_neg at hcon
  refine hno ν hξν ⟨inferInstance, fun γ hγ hνγ ↦ ?_⟩
  by_contra hsc
  exact hcon γ hγ ⟨hγ, hνγ, Or.inr hsc⟩

/-! ### The least failure stage -/

theorem magidorFailure_spec {ρ : V} (htot : MagidorFailureTotal ρ) (ν : V) [IsOrdinal ν] :
    IsLeastOrdinal (MagidorFailureAt ρ ν) (magidorFailure ρ ν) := by
  rcases (magidorFailure_eq_iff ρ ν (magidorFailure ρ ν)).mp rfl with h | ⟨h, -⟩
  · exact h
  · exact absurd (exists_magidorFailureAt htot ν) h

theorem magidorFailure_isOrdinal {ρ : V} (htot : MagidorFailureTotal ρ) (ν : V) [IsOrdinal ν] :
    IsOrdinal (magidorFailure ρ ν) := (magidorFailure_spec htot ν).1

theorem mem_magidorFailure {ρ : V} (htot : MagidorFailureTotal ρ) (ν : V) [IsOrdinal ν] :
    ν ∈ magidorFailure ρ ν := (magidorFailure_spec htot ν).2.1.2.1

/-- Above `ρ` the least failure stage really is a failure. -/
theorem not_magidorSupercompactAt_magidorFailure {ρ ν : V} (htot : MagidorFailureTotal ρ)
    [IsOrdinal ν] (hρν : ρ ⊆ ν) : ¬ IsMagidorSupercompactAt ν (magidorFailure ρ ν) := by
  rcases (magidorFailure_spec htot ν).2.1.2.2 with hout | hf
  · exact absurd hρν hout
  · exact hf

/-- Below the least failure stage the small-embedding property holds. -/
theorem magidorSupercompactAt_of_mem_magidorFailure {ρ ν γ : V} (htot : MagidorFailureTotal ρ)
    [IsOrdinal ν] (hρν : ρ ⊆ ν) (hγ : γ ∈ magidorFailure ρ ν) (hνγ : ν ∈ γ) :
    IsMagidorSupercompactAt ν γ := by
  have hord : IsOrdinal (magidorFailure ρ ν) := magidorFailure_isOrdinal htot ν
  have hγord : IsOrdinal γ := IsOrdinal.of_mem hγ
  by_contra hsc
  have hsub : magidorFailure ρ ν ⊆ γ :=
    (magidorFailure_spec htot ν).2.2 γ hγord ⟨hγord, hνγ, Or.inr hsc⟩
  exact mem_irrefl γ (hsub γ hγ)

/-! ### Closure points -/

/-- A limit ordinal above `ρ` closed under the failure stage function. -/
def IsMagidorClosurePoint (ρ d : V) : Prop :=
  IsLimitOrdinal d ∧ ρ ∈ d ∧ ∀ ν ∈ d, ρ ⊆ ν → magidorFailure ρ ν ∈ d

/-- The closure clause at a single `ν`, with the value of `magidorFailure` named by its graph so
that the definability tactic can read it. -/
def MagidorFailureClosedAt (ρ d ν : V) : Prop :=
  ρ ⊆ ν → ∃ γ, MagidorFailureGraph ρ ν γ ∧ γ ∈ d

instance magidorFailureClosedAt_definable : ℒₛₑₜ-relation₃[V] MagidorFailureClosedAt := by
  have h : ℒₛₑₜ-relation₃[V] (fun ρ d ν : V ↦ ρ ⊆ ν → ∃ γ,
      (IsLeastOrdinal (MagidorFailureAt ρ ν) γ ∨
        ((¬∃ δ : V, IsOrdinal δ ∧ MagidorFailureAt ρ ν δ) ∧ γ = ∅)) ∧ γ ∈ d) := by
    unfold IsLeastOrdinal MagidorFailureAt
    definability
  apply Language.Definable.of_iff h
  intro v
  simp only [MagidorFailureClosedAt, MagidorFailureGraph, magidorFailure_eq_iff]

/-- The closure point condition with the failure stage named by its graph. -/
def IsMagidorClosurePointGraph (ρ d : V) : Prop :=
  IsLimitOrdinal d ∧ ρ ∈ d ∧ ∀ ν ∈ d, MagidorFailureClosedAt ρ d ν

theorem isMagidorClosurePoint_iff_graph (ρ d : V) :
    IsMagidorClosurePoint ρ d ↔ IsMagidorClosurePointGraph ρ d := by
  unfold IsMagidorClosurePoint IsMagidorClosurePointGraph MagidorFailureClosedAt
    MagidorFailureGraph
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun ν hν hρν ↦ ⟨magidorFailure ρ ν, rfl, h3 ν hν hρν⟩⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun ν hν hρν ↦ ?_⟩
    obtain ⟨γ, rfl, hγ⟩ := h3 ν hν hρν
    exact hγ

instance isMagidorClosurePoint_definable : ℒₛₑₜ-relation[V] IsMagidorClosurePoint := by
  have h : ℒₛₑₜ-relation[V] IsMagidorClosurePointGraph := by
    unfold IsMagidorClosurePointGraph IsLimitOrdinal
    definability
  apply Language.Definable.of_iff h
  intro v
  exact isMagidorClosurePoint_iff_graph (v 0) (v 1)

/-- What the main argument reads off a closure point. -/
theorem magidorFailure_mem_of_closurePoint {ρ d κ : V} (hd : IsMagidorClosurePoint ρ d)
    (hρκ : ρ ⊆ κ) (hκ : κ ∈ d) : magidorFailure ρ κ ∈ d := hd.2.2 κ hκ hρκ

/-- Closure points are unbounded in the ordinals. -/
theorem exists_magidorClosurePoint_above {ρ : V} [IsOrdinal ρ] (htot : MagidorFailureTotal ρ)
    (β : V) [IsOrdinal β] : ∃ d : V, IsMagidorClosurePoint ρ d ∧ β ∈ d := by
  obtain ⟨c, hc, hβc, hρc⟩ := exists_ordinal_upper_bound₂ β ρ
  have : IsOrdinal c := hc
  have hGord : ∀ ν : V, IsOrdinal ν → IsOrdinal (magidorFailure ρ ν) :=
    fun ν hν ↦ have : IsOrdinal ν := hν; magidorFailure_isOrdinal htot ν
  have hGgt : ∀ ν : V, IsOrdinal ν → ν ∈ magidorFailure ρ ν :=
    fun ν hν ↦ have : IsOrdinal ν := hν; mem_magidorFailure htot ν
  obtain ⟨d, hsc, hclosed⟩ :=
    exists_ordinalClosurePoint_above (magidorFailure_definable ρ) hGord hGgt (succ c)
  have hdord : IsOrdinal d := hclosed.1
  have hlim : IsLimitOrdinal d := IsOrdinalClosurePoint.limit hGgt hclosed
  have hβd : β ∈ d := by
    have hβsc : β ∈ succ c := by
      rcases IsOrdinal.subset_iff.mp hβc with rfl | h
      · exact mem_succ_self _
      · exact mem_succ_iff.mpr (Or.inr h)
    exact IsOrdinal.toIsTransitive.mem_trans hβsc hsc
  have hρd : ρ ∈ d := by
    have hρsc : ρ ∈ succ c := by
      rcases IsOrdinal.subset_iff.mp hρc with rfl | h
      · exact mem_succ_self _
      · exact mem_succ_iff.mpr (Or.inr h)
    exact IsOrdinal.toIsTransitive.mem_trans hρsc hsc
  exact ⟨d, ⟨hlim, hρd, fun ν hν _ ↦ hclosed.2.2 ν hν⟩, hβd⟩

/-! ## Part 2: the bounded formula -/

/-- Being the least ordinal with a property, written so that only elements are quantified over. -/
theorem isLeastOrdinal_iff_no_smaller_magidor {P : V → Prop} {d : V} :
    IsLeastOrdinal P d ↔ IsOrdinal d ∧ P d ∧ ∀ ξ ∈ d, ¬ P ξ := by
  constructor
  · rintro ⟨hd, hPd, hmin⟩
    have : IsOrdinal d := hd
    refine ⟨hd, hPd, ?_⟩
    intro ξ hξ hPξ
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    exact mem_irrefl ξ (hmin ξ this hPξ ξ hξ)
  · rintro ⟨hd, hPd, hno⟩
    refine ⟨hd, hPd, ?_⟩
    intro β hβ hPβ
    have : IsOrdinal d := hd
    have : IsOrdinal β := hβ
    rcases IsOrdinal.mem_trichotomy d β with hlt | heq | hgt
    · exact IsOrdinal.toIsTransitive.transitive d hlt
    · exact heq ▸ fun x hx ↦ hx
    · exact absurd hPβ (hno β hgt)

/-- `γ` is the least failure stage of `ν` above `ρ`. Free variables: `ρ`, `ν`, `γ`, `W`. -/
def boundedLeastMagidorFailureFormula : SetTheorySemisentence 4 :=
  “ρ ν γ W. !isSubsetOf ρ ν ∧ !IsOrdinal.dfn γ ∧ ν ∈ γ ∧
    ¬!boundedMagidorSupercompactAtFormula ν γ W ∧
      ∀ δ ∈ γ, ν ∈ δ → !boundedMagidorSupercompactAtFormula ν δ W”

theorem boundedLeastMagidorFailureFormula_bounded :
    IsBoundedSetFormula boundedLeastMagidorFailureFormula :=
  .and (isSubsetOf_bounded.subst _)
    (.and (isOrdinalFormula_bounded.subst _)
      (.and (.rel _ _)
        (.and (boundedMagidorSupercompactAtFormula_bounded.subst _).neg
          (.all (.bvar 2) (.or (.nrel _ _)
            (boundedMagidorSupercompactAtFormula_bounded.subst _))))))

/-- `d` is a limit ordinal above `ρ` closed under the failure stage function, with the failure
stage named by the bounded formula. Free variables: `ρ`, `d`, `W`. -/
def boundedMagidorClosurePointFormula : SetTheorySemisentence 3 :=
  “ρ d W. !boundedLimitOrdinalFormula d ∧ ρ ∈ d ∧
    ∀ ν ∈ d, !isSubsetOf ρ ν → ∃ γ ∈ d, !boundedLeastMagidorFailureFormula ρ ν γ W”

theorem boundedMagidorClosurePointFormula_bounded :
    IsBoundedSetFormula boundedMagidorClosurePointFormula :=
  .and (boundedLimitOrdinalFormula_bounded.subst _)
    (.and (.rel _ _)
      (.all (.bvar 1) (.or (isSubsetOf_bounded.subst _).neg
        (.exs (.bvar 2) (boundedLeastMagidorFailureFormula_bounded.subst _)))))

/-- The literal reading of `boundedLeastMagidorFailureFormula`. -/
def BoundedLeastMagidorFailure (ρ ν γ W : V) : Prop :=
  ρ ⊆ ν ∧ IsOrdinal γ ∧ ν ∈ γ ∧ ¬ BoundedMagidorSupercompactAt ν γ W ∧
    ∀ δ ∈ γ, ν ∈ δ → BoundedMagidorSupercompactAt ν δ W

instance boundedLeastMagidorFailureFormula_defined :
    ℒₛₑₜ-relation₄[V] BoundedLeastMagidorFailure via boundedLeastMagidorFailureFormula :=
  ⟨fun v ↦ by
    simp [boundedLeastMagidorFailureFormula, BoundedLeastMagidorFailure,
      (boundedMagidorSupercompactAtFormula_defined (V := V)).iff,
      Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton]⟩

/-- The literal reading of `boundedMagidorClosurePointFormula`. -/
def BoundedMagidorClosurePoint (ρ d W : V) : Prop :=
  IsLimitOrdinal d ∧ ρ ∈ d ∧
    ∀ ν ∈ d, ρ ⊆ ν → ∃ γ ∈ d, BoundedLeastMagidorFailure ρ ν γ W

instance boundedMagidorClosurePointFormula_defined :
    ℒₛₑₜ-relation₃[V] BoundedMagidorClosurePoint via boundedMagidorClosurePointFormula :=
  ⟨fun v ↦ by
    simp [boundedMagidorClosurePointFormula, BoundedMagidorClosurePoint,
      (boundedLeastMagidorFailureFormula_defined (V := V)).iff,
      Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton]⟩

/-! ### What the bounded readings say at a rank stage -/

/-- At a successor closed rank stage above `ω` that holds the membership formula family and has
`γ` below it, the bounded reading says that `γ` is the least failure stage of `ν`. -/
theorem boundedLeastMagidorFailure_iff {ν₀ ρ ν γ : V} [IsOrdinal ν₀]
    (hω : (ω : V) ∈ ν₀) (hsucc : ∀ ξ ∈ ν₀, succ ξ ∈ ν₀)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy ν₀) (hγν₀ : γ ∈ ν₀) :
    BoundedLeastMagidorFailure ρ ν γ (hierarchy ν₀) ↔
      ρ ⊆ ν ∧ IsLeastOrdinal (MagidorFailureAt ρ ν) γ := by
  unfold BoundedLeastMagidorFailure
  rw [isLeastOrdinal_iff_no_smaller_magidor]
  constructor
  · rintro ⟨hρν, hγord, hνγ, hns, hbelow⟩
    refine ⟨hρν, hγord, ⟨hγord, hνγ, Or.inr ?_⟩, ?_⟩
    · exact fun hsc ↦ hns ((boundedMagidorSupercompactAt_iff hω hsucc hF hνγ hγν₀).mpr hsc)
    · rintro δ hδγ ⟨hδord, hνδ, hcase⟩
      have hδν₀ : δ ∈ ν₀ := IsOrdinal.toIsTransitive.mem_trans hδγ hγν₀
      have hsc : IsMagidorSupercompactAt ν δ :=
        (boundedMagidorSupercompactAt_iff hω hsucc hF hνδ hδν₀).mp (hbelow δ hδγ hνδ)
      rcases hcase with hc | hc
      · exact hc hρν
      · exact hc hsc
  · rintro ⟨hρν, hγord, ⟨-, hνγ, hcase⟩, hbelow⟩
    have hns : ¬ IsMagidorSupercompactAt ν γ := by
      rcases hcase with hc | hc
      · exact absurd hρν hc
      · exact hc
    refine ⟨hρν, hγord, hνγ, ?_, ?_⟩
    · exact fun hb ↦ hns ((boundedMagidorSupercompactAt_iff hω hsucc hF hνγ hγν₀).mp hb)
    · intro δ hδγ hνδ
      have hδν₀ : δ ∈ ν₀ := IsOrdinal.toIsTransitive.mem_trans hδγ hγν₀
      have hδord : IsOrdinal δ := IsOrdinal.of_mem hδν₀
      refine (boundedMagidorSupercompactAt_iff hω hsucc hF hνδ hδν₀).mpr ?_
      by_contra hsc
      exact hbelow δ hδγ ⟨hδord, hνδ, Or.inr hsc⟩

/-- At such a stage the bounded reading of the closure point condition says exactly what
`IsMagidorClosurePoint` says. -/
theorem boundedMagidorClosurePoint_iff {ν₀ ρ d : V} [IsOrdinal ν₀]
    (hω : (ω : V) ∈ ν₀) (hsucc : ∀ ξ ∈ ν₀, succ ξ ∈ ν₀)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy ν₀)
    (htot : MagidorFailureTotal ρ) (hdν₀ : d ∈ ν₀) :
    BoundedMagidorClosurePoint ρ d (hierarchy ν₀) ↔ IsMagidorClosurePoint ρ d := by
  unfold BoundedMagidorClosurePoint IsMagidorClosurePoint
  constructor
  · rintro ⟨hlim, hρd, hcl⟩
    refine ⟨hlim, hρd, fun ν hνd hρν ↦ ?_⟩
    obtain ⟨γ, hγd, hγ⟩ := hcl ν hνd hρν
    have hγν₀ : γ ∈ ν₀ := IsOrdinal.toIsTransitive.mem_trans hγd hdν₀
    have hleast := ((boundedLeastMagidorFailure_iff hω hsucc hF hγν₀).mp hγ).2
    have : magidorFailure ρ ν = γ := (magidorFailure_eq_iff ρ ν γ).mpr (Or.inl hleast)
    exact this ▸ hγd
  · rintro ⟨hlim, hρd, hcl⟩
    refine ⟨hlim, hρd, fun ν hνd hρν ↦ ?_⟩
    have hdord : IsOrdinal d := hlim.1
    have : IsOrdinal ν := IsOrdinal.of_mem hνd
    have hγd : magidorFailure ρ ν ∈ d := hcl ν hνd hρν
    have hγν₀ : magidorFailure ρ ν ∈ ν₀ := IsOrdinal.toIsTransitive.mem_trans hγd hdν₀
    exact ⟨magidorFailure ρ ν, hγd,
      (boundedLeastMagidorFailure_iff hω hsucc hF hγν₀).mpr ⟨hρν, magidorFailure_spec htot ν⟩⟩

/-- The bounded formula, evaluated at the stage `V_{lam+ω}`, says that `d` is a closure point of
the failure function. `lam` has to be a limit ordinal with `d` below it; the formula family side
condition is discharged here, and `ω ⊆ lam`, which is all the stage `V_{lam+ω}` needs, follows
from `lam` being a limit. -/
theorem eval_boundedMagidorClosurePointFormula {lam ρ d : V} [IsOrdinal lam]
    (hlim : IsLimitOrdinal lam) (htot : MagidorFailureTotal ρ) (hd : d ∈ lam) :
    boundedMagidorClosurePointFormula.Evalb ![ρ, d, hierarchy (ordinalAdd lam (ω : V))] ↔
      IsMagidorClosurePoint ρ d := by
  have hωlam : (ω : V) ⊆ lam := omega_subset_of_isLimitOrdinal hlim
  have hlamθ : lam ∈ ordinalAdd lam (ω : V) := ordinalAdd_omega_gt lam
  have hωθ : (ω : V) ∈ ordinalAdd lam (ω : V) := mem_ordinalAdd_omega_of_subset hωlam
  have hsuccθ : ∀ ζ ∈ ordinalAdd lam (ω : V), succ ζ ∈ ordinalAdd lam (ω : V) :=
    fun _ hζ ↦ ordinalAdd_omega_succ_closed lam hζ
  have hFθ : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd lam (ω : V)) :=
    hierarchy_mono (ordinalAdd_omega_subset_of_successor_closed hωθ hsuccθ) _
      formulaFamily_mem_hierarchy_omega_two
  have hdθ : d ∈ ordinalAdd lam (ω : V) := IsOrdinal.toIsTransitive.mem_trans hd hlamθ
  exact ((boundedMagidorClosurePointFormula_defined (V := V)).iff
      ![ρ, d, hierarchy (ordinalAdd lam (ω : V))]).trans
    (boundedMagidorClosurePoint_iff hωθ hsuccθ hFθ htot hdθ)

/-! ## Part 3: transfer along a coded embedding -/

/-- The side conditions on an auxiliary stage cross a coded embedding between rank stages. -/
private theorem transfer_stage_conditions {θ θ' ν₀ f : V} [IsOrdinal θ] [IsOrdinal θ']
    [IsOrdinal ν₀]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hω' : (ω : V) ∈ θ') (hsucc' : ∀ ξ ∈ θ', succ ξ ∈ θ')
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
    (hων₀ : (ω : V) ∈ ν₀) (hsuccν₀ : ∀ ξ ∈ ν₀, succ ξ ∈ ν₀) (hν₀θ : ν₀ ∈ θ)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy ν₀) :
    IsOrdinal (f ‘ ν₀) ∧ f ‘ (hierarchy ν₀) = hierarchy (f ‘ ν₀) ∧ (ω : V) ∈ f ‘ ν₀ ∧
      (∀ ξ ∈ f ‘ ν₀, succ ξ ∈ f ‘ ν₀) ∧
      (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (f ‘ ν₀) := by
  let := hierarchy_transitive θ
  let := hierarchy_transitive θ'
  let := (hierarchy_isSequenceSupport hω hsucc).toIsCodingSupport
  let := (hierarchy_isSequenceSupport hων₀ hsuccν₀).toIsCodingSupport
  have hν₀H : ν₀ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hν₀θ
  have hWH : hierarchy ν₀ ∈ hierarchy θ := hierarchy_mem hν₀θ
  have hωH : (ω : V) ∈ hierarchy θ := ordinal_subset_hierarchy θ _ hω
  have hvpair := supportEmbedding_value_hierarchy hω hsucc hω' hsucc' h inferInstance hν₀H
  have hvord : IsOrdinal (f ‘ ν₀) := hvpair.1
  let := hvord
  have hvW : f ‘ (hierarchy ν₀) = hierarchy (f ‘ ν₀) := hvpair.2
  have hων' : (ω : V) ∈ f ‘ ν₀ := by
    have := (h.value_mem_iff hωH hν₀H).mpr hων₀
    rwa [h.value_omega hωH] at this
  have hsuccν' : ∀ ξ ∈ f ‘ ν₀, succ ξ ∈ f ‘ ν₀ := by
    have h0 := (eval_boundedSuccessorClosedFormula ν₀).mpr hsuccν₀
    have he := (h.bounded_formula_iff boundedSuccessorClosedFormula_bounded ![ν₀]
      (by simp [hν₀H])).mp h0
    have hvec : (fun i ↦ f ‘ ((![ν₀] : Fin 1 → V) i)) = ![f ‘ ν₀] := by
      funext i
      exact Fin.cases rfl (fun t ↦ Fin.elim0 t) i
    rw [hvec] at he
    exact (eval_boundedSuccessorClosedFormula (f ‘ ν₀)).mp he
  have hFθ : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy θ :=
    (hierarchy_transitive θ).mem_trans hF hWH
  have hF' : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (f ‘ ν₀) := by
    have hfix : f ‘ (formulaFamily membershipLanguageCode ∅ : V) =
        formulaFamily membershipLanguageCode ∅ :=
      h.value_membershipFamily_of_support hWH hF (identity_mem_hierarchy_limit hsuccν₀ hF)
    have hm := (h.value_mem_iff hFθ hWH).mpr hF
    rwa [hfix, hvW] at hm
  exact ⟨hvord, hvW, hων', hsuccν', hF'⟩

/-- An auxiliary stage inside `V_{lam+ω}` holding a prescribed ordinal of `lam`. -/
private theorem exists_aux_stage {lam x : V} [IsOrdinal lam] [IsOrdinal x]
    (hlim : IsLimitOrdinal lam) (hωmem : (ω : V) ∈ lam) (hx : x ∈ lam) :
    ∃ ν₀ : V, IsOrdinal ν₀ ∧ (ω : V) ∈ ν₀ ∧ (∀ ξ ∈ ν₀, succ ξ ∈ ν₀) ∧ x ∈ ν₀ ∧
      (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy ν₀ ∧
      ν₀ ∈ ordinalAdd lam (ω : V) := by
  have hlamord : IsOrdinal lam := hlim.1
  have hsucclam : ∀ ξ ∈ lam, succ ξ ∈ lam := fun _ hξ ↦ succ_mem_of_isLimitOrdinal' hlim hξ
  set δ : V := x ∪ (ω : V) with hδdef
  have hδord : IsOrdinal δ := ordinal_union_ordinal x (ω : V)
  let := hδord
  have hδlam : δ ∈ lam := union_mem_of_ordinals hx hωmem
  refine ⟨ordinalAdd δ (ω : V), inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_ordinalAdd_omega_of_subset (fun z hz ↦ mem_union_iff.mpr (Or.inr hz))
  · exact fun _ hξ ↦ ordinalAdd_omega_succ_closed δ hξ
  · exact mem_ordinalAdd_omega_of_subset (fun z hz ↦ mem_union_iff.mpr (Or.inl hz))
  · refine hierarchy_mono (ordinalAdd_omega_subset_of_successor_closed ?_ ?_) _
      formulaFamily_mem_hierarchy_omega_two
    · exact mem_ordinalAdd_omega_of_subset (fun z hz ↦ mem_union_iff.mpr (Or.inr hz))
    · exact fun _ hξ ↦ ordinalAdd_omega_succ_closed δ hξ
  · exact mem_ordinalAdd_omega_of_subset
      (ordinalAdd_omega_subset_of_successor_closed hδlam hsucclam)

/-- The value of the failure stage function commutes with a coded embedding between the stages
`V_{lam+ω}` and `V_{lam'+ω}`, for arguments whose failure stage is still below `lam`. -/
theorem magidorFailure_value {lam lam' f ρ ν : V} [IsOrdinal lam] [IsOrdinal lam'] [IsOrdinal ρ]
    (hlim : IsLimitOrdinal lam) (hωlam : (ω : V) ∈ lam)
    (hlim' : IsLimitOrdinal lam') (hωlam' : (ω : V) ∈ lam')
    (h : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam (ω : V)))
      (hierarchy (ordinalAdd lam' (ω : V))) f)
    (htot : MagidorFailureTotal ρ) (hfρ : f ‘ ρ = ρ)
    (hν : ν ∈ lam) (hρν : ρ ⊆ ν) (hfail : magidorFailure ρ ν ∈ lam) :
    f ‘ (magidorFailure ρ ν) = magidorFailure ρ (f ‘ ν) := by
  have hνord : IsOrdinal ν := IsOrdinal.of_mem hν
  let := hνord
  have hγord : IsOrdinal (magidorFailure ρ ν) := magidorFailure_isOrdinal htot ν
  let := hγord
  set γ : V := magidorFailure ρ ν with hγdef
  -- the auxiliary stage
  obtain ⟨ν₀, hν₀ord, hων₀, hsuccν₀, hγν₀, hFν₀, hν₀θ⟩ := exists_aux_stage hlim hωlam hfail
  let := hν₀ord
  have hνν₀ : ν ∈ ν₀ :=
    IsOrdinal.toIsTransitive.mem_trans (mem_magidorFailure htot ν) hγν₀
  have hρν₀ : ρ ∈ ν₀ := by
    rcases IsOrdinal.subset_iff.mp hρν with he | hlt
    · exact he ▸ hνν₀
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hνν₀
  -- the two big stages
  have hlamθ : lam ∈ ordinalAdd lam (ω : V) := ordinalAdd_omega_gt lam
  have hωθ : (ω : V) ∈ ordinalAdd lam (ω : V) :=
    IsOrdinal.toIsTransitive.mem_trans hωlam hlamθ
  have hsuccθ : ∀ ξ ∈ ordinalAdd lam (ω : V), succ ξ ∈ ordinalAdd lam (ω : V) :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam hξ
  have hωθ' : (ω : V) ∈ ordinalAdd lam' (ω : V) :=
    IsOrdinal.toIsTransitive.mem_trans hωlam' (ordinalAdd_omega_gt lam')
  have hsuccθ' : ∀ ξ ∈ ordinalAdd lam' (ω : V), succ ξ ∈ ordinalAdd lam' (ω : V) :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam' hξ
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  -- the arguments sit inside the source stage
  have hν₀H : ν₀ ∈ hierarchy (ordinalAdd lam (ω : V)) := ordinal_mem_hierarchy_iff.mpr hν₀θ
  have hWH : hierarchy ν₀ ∈ hierarchy (ordinalAdd lam (ω : V)) := hierarchy_mem hν₀θ
  have hρH : ρ ∈ hierarchy (ordinalAdd lam (ω : V)) :=
    (hierarchy_transitive _).mem_trans hρν₀ hν₀H
  have hνH : ν ∈ hierarchy (ordinalAdd lam (ω : V)) :=
    (hierarchy_transitive _).mem_trans hνν₀ hν₀H
  have hγH : γ ∈ hierarchy (ordinalAdd lam (ω : V)) :=
    (hierarchy_transitive _).mem_trans hγν₀ hν₀H
  -- the target side conditions
  obtain ⟨hvord, hvW, hων', hsuccν', hFν'⟩ :=
    transfer_stage_conditions hωθ hsuccθ hωθ' hsuccθ' h hων₀ hsuccν₀ hν₀θ hFν₀
  let := hvord
  have hγν₀' : f ‘ γ ∈ f ‘ ν₀ := (h.value_mem_iff hγH hν₀H).mpr hγν₀
  -- the bounded formula crosses the embedding
  have hsource : BoundedLeastMagidorFailure ρ ν γ (hierarchy ν₀) :=
    (boundedLeastMagidorFailure_iff hων₀ hsuccν₀ hFν₀ hγν₀).mpr
      ⟨hρν, magidorFailure_spec htot ν⟩
  have hv : ∀ i, (![ρ, ν, γ, hierarchy ν₀] : Fin 4 → V) i ∈
      hierarchy (ordinalAdd lam (ω : V)) := by
    simp [Fin.forall_fin_iff_zero_and_forall_succ, hρH, hνH, hγH, hWH]
  have hiff := h.bounded_defined_iff boundedLeastMagidorFailureFormula_bounded
    (fun v ↦ BoundedLeastMagidorFailure (v 0) (v 1) (v 2) (v 3)) ![ρ, ν, γ, hierarchy ν₀] hv
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three] at hiff
  rw [hvW, hfρ] at hiff
  have htarget := hiff.mp hsource
  have hleast := ((boundedLeastMagidorFailure_iff hων' hsuccν' hFν' hγν₀').mp htarget).2
  exact ((magidorFailure_eq_iff ρ (f ‘ ν) (f ‘ γ)).mpr (Or.inl hleast)).symm

/-- Closure points below `lam` go to closure points along a coded embedding between the stages
`V_{lam+ω}` and `V_{lam'+ω}`. -/
theorem magidorClosurePoint_value_iff {lam lam' f ρ d : V} [IsOrdinal lam] [IsOrdinal lam']
    (hlim : IsLimitOrdinal lam) (hωlam : (ω : V) ∈ lam)
    (hlim' : IsLimitOrdinal lam') (hωlam' : (ω : V) ∈ lam')
    (h : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam (ω : V)))
      (hierarchy (ordinalAdd lam' (ω : V))) f)
    (htot : MagidorFailureTotal ρ) (hfρ : f ‘ ρ = ρ) (hd : d ∈ lam) (hρd : ρ ∈ d) :
    IsMagidorClosurePoint ρ d ↔ IsMagidorClosurePoint ρ (f ‘ d) := by
  have hdord : IsOrdinal d := IsOrdinal.of_mem hd
  let := hdord
  obtain ⟨ν₀, hν₀ord, hων₀, hsuccν₀, hdν₀, hFν₀, hν₀θ⟩ := exists_aux_stage hlim hωlam hd
  let := hν₀ord
  have hρν₀ : ρ ∈ ν₀ := IsOrdinal.toIsTransitive.mem_trans hρd hdν₀
  have hlamθ : lam ∈ ordinalAdd lam (ω : V) := ordinalAdd_omega_gt lam
  have hωθ : (ω : V) ∈ ordinalAdd lam (ω : V) :=
    IsOrdinal.toIsTransitive.mem_trans hωlam hlamθ
  have hsuccθ : ∀ ξ ∈ ordinalAdd lam (ω : V), succ ξ ∈ ordinalAdd lam (ω : V) :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam hξ
  have hωθ' : (ω : V) ∈ ordinalAdd lam' (ω : V) :=
    IsOrdinal.toIsTransitive.mem_trans hωlam' (ordinalAdd_omega_gt lam')
  have hsuccθ' : ∀ ξ ∈ ordinalAdd lam' (ω : V), succ ξ ∈ ordinalAdd lam' (ω : V) :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam' hξ
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  have hν₀H : ν₀ ∈ hierarchy (ordinalAdd lam (ω : V)) := ordinal_mem_hierarchy_iff.mpr hν₀θ
  have hWH : hierarchy ν₀ ∈ hierarchy (ordinalAdd lam (ω : V)) := hierarchy_mem hν₀θ
  have hρH : ρ ∈ hierarchy (ordinalAdd lam (ω : V)) :=
    (hierarchy_transitive _).mem_trans hρν₀ hν₀H
  have hdH : d ∈ hierarchy (ordinalAdd lam (ω : V)) :=
    (hierarchy_transitive _).mem_trans hdν₀ hν₀H
  obtain ⟨hvord, hvW, hων', hsuccν', hFν'⟩ :=
    transfer_stage_conditions hωθ hsuccθ hωθ' hsuccθ' h hων₀ hsuccν₀ hν₀θ hFν₀
  let := hvord
  have hdν₀' : f ‘ d ∈ f ‘ ν₀ := (h.value_mem_iff hdH hν₀H).mpr hdν₀
  have hv : ∀ i, (![ρ, d, hierarchy ν₀] : Fin 3 → V) i ∈
      hierarchy (ordinalAdd lam (ω : V)) := by
    simp [Fin.forall_fin_iff_zero_and_forall_succ, hρH, hdH, hWH]
  have hiff := h.bounded_defined_iff boundedMagidorClosurePointFormula_bounded
    (fun v ↦ BoundedMagidorClosurePoint (v 0) (v 1) (v 2)) ![ρ, d, hierarchy ν₀] hv
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hiff
  rw [hvW, hfρ] at hiff
  exact (boundedMagidorClosurePoint_iff hων₀ hsuccν₀ hFν₀ htot hdν₀).symm.trans
    (hiff.trans (boundedMagidorClosurePoint_iff hων' hsuccν' hFν' htot hdν₀'))

end ZFVP
