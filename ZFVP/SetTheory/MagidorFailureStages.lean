import ZFVP.SetTheory.MagidorSupercompact
import ZFVP.SetTheory.OrdinalClosureClass
import ZFVP.SetTheory.Rank

/-! # The least limit stage where supercompactness fails on an interval

Bagaria's Theorem 4.3(2) (`C(n)`-cardinals, section 4) runs Vopenka's principle on the structures
`⟨V_{λ+2}, ∈, α, λ⟩`, where `λ` is the least limit ordinal above `α` such that no cardinal below
`α` is `<λ`-supercompact. This module supplies the pure set theory of that index condition, with
the project's small-embedding predicate `IsMagidorSupercompactUpTo` in the place of
`<λ`-supercompactness. No formulas and no syntax appear here; a later module turns the condition
into a `Pi_1` class formula.

The condition is written with two ordinal parameters. `NoMagidorSupercompactBetween ρ r lam` says
that no ordinal `ν` with `ρ ⊆ ν ⊆ r` is Magidor supercompact for all target ranks below `lam`.
Taking `ρ = succ ξ` this is the interval `ξ < ν ≤ r`, which is what the parameterized form of
Bagaria's argument uses: restricting the failing cardinals to lie above the fixed parameter `ξ`
keeps the index condition satisfiable when there are supercompact cardinals below `ξ`.

`IsLeastMagidorFailureLimit ρ r lam` adds that `lam` is a limit ordinal above `r` and that no
smaller limit ordinal above `r` has the same property. Under the hypothesis that no ordinal above
`ξ` is Magidor supercompact such a `lam` exists above every `r`, and it is unique. The existence
proof takes, for each ordinal `ν`, the least rank at which the small-embedding property for `ν`
fails, and closes an ordinal under that class function; replacement does the work and no choice
is used. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Small ordinal facts

These repeat lemmas that live in modules this file does not import. -/

/-- Below an ordinal, successors stay below. -/
theorem succ_subset_of_mem_ordinal' {α β : V} [IsOrdinal α] (h : β ∈ α) : succ β ⊆ α := by
  intro z hz
  rcases mem_succ_iff.mp hz with rfl | hzb
  · exact h
  · exact IsOrdinal.toIsTransitive.mem_trans hzb h

/-- A limit ordinal is closed under successor. -/
theorem succ_mem_of_isLimitOrdinal' {lam ζ : V} (hlim : IsLimitOrdinal lam) (hζ : ζ ∈ lam) :
    succ ζ ∈ lam := by
  have hlamord : IsOrdinal lam := hlim.1
  have hζord : IsOrdinal ζ := IsOrdinal.of_mem hζ
  rcases IsOrdinal.mem_trichotomy (succ ζ) lam with h | h | h
  · exact h
  · exact absurd ⟨ζ, h.symm⟩ hlim.2.2
  · rcases mem_succ_iff.mp h with rfl | h'
    · exact absurd hζ (mem_irrefl lam)
    · exact absurd (IsOrdinal.toIsTransitive.mem_trans h' hζ) (mem_irrefl lam)

/-- Two ordinals have an ordinal upper bound, namely the larger of the two. -/
theorem exists_ordinal_upper_bound₂ (a b : V) [IsOrdinal a] [IsOrdinal b] :
    ∃ c : V, IsOrdinal c ∧ a ⊆ c ∧ b ⊆ c := by
  rcases IsOrdinal.mem_trichotomy a b with h | h | h
  · exact ⟨b, inferInstance, IsOrdinal.toIsTransitive.transitive a h, fun x hx ↦ hx⟩
  · exact ⟨b, inferInstance, h ▸ fun x hx ↦ hx, fun x hx ↦ hx⟩
  · exact ⟨a, inferInstance, fun x hx ↦ hx, IsOrdinal.toIsTransitive.transitive b h⟩

/-! ### The interval condition -/

/-- No ordinal `ν` with `ρ ⊆ ν ⊆ r` has the small-embedding property at every rank below `lam`. -/
def NoMagidorSupercompactBetween (ρ r lam : V) : Prop :=
  ∀ ν, IsOrdinal ν → ρ ⊆ ν → ν ⊆ r → ¬ IsMagidorSupercompactUpTo ν lam

instance noMagidorSupercompactBetween_definable :
    ℒₛₑₜ-relation₃[V] NoMagidorSupercompactBetween := by
  unfold NoMagidorSupercompactBetween
  definability

/-- Raising the bound keeps the failure: the bounded predicate only gets weaker. -/
theorem NoMagidorSupercompactBetween.mono {ρ r lam lam' : V}
    (h : NoMagidorSupercompactBetween ρ r lam) (hsub : lam ⊆ lam') :
    NoMagidorSupercompactBetween ρ r lam' :=
  fun ν hν hρν hνr hup ↦ h ν hν hρν hνr (hup.mono hsub)

/-- `lam` is the least limit ordinal above `r` at which supercompactness fails on the whole
interval `ρ ⊆ ν ⊆ r`. -/
def IsLeastMagidorFailureLimit (ρ r lam : V) : Prop :=
  IsOrdinal lam ∧ IsLimitOrdinal lam ∧ r ∈ lam ∧ NoMagidorSupercompactBetween ρ r lam ∧
    ∀ μ ∈ lam, IsLimitOrdinal μ → r ∈ μ → ¬ NoMagidorSupercompactBetween ρ r μ

instance isLeastMagidorFailureLimit_definable :
    ℒₛₑₜ-relation₃[V] IsLeastMagidorFailureLimit := by
  unfold IsLeastMagidorFailureLimit NoMagidorSupercompactBetween IsLimitOrdinal
  definability

/-- The stage the main argument ends with: every ordinal of the interval fails to have the
small-embedding property at some rank below `lam`. -/
theorem not_magidorSupercompactUpTo_of_leastLimit {ρ r lam κ : V}
    (h : IsLeastMagidorFailureLimit ρ r lam) (hκ : IsOrdinal κ) (hρκ : ρ ⊆ κ) (hκr : κ ⊆ r) :
    ¬ IsMagidorSupercompactUpTo κ lam :=
  h.2.2.2.1 κ hκ hρκ hκr

/-- There is at most one least failure limit for given parameters. -/
theorem isLeastMagidorFailureLimit_functional {ρ r lam₁ lam₂ : V}
    (h₁ : IsLeastMagidorFailureLimit ρ r lam₁) (h₂ : IsLeastMagidorFailureLimit ρ r lam₂) :
    lam₁ = lam₂ := by
  have : IsOrdinal lam₁ := h₁.1
  have : IsOrdinal lam₂ := h₂.1
  rcases IsOrdinal.mem_trichotomy lam₁ lam₂ with h | h | h
  · exact absurd h₁.2.2.2.1 (h₂.2.2.2.2 lam₁ h h₁.2.1 h₁.2.2.1)
  · exact h
  · exact absurd h₂.2.2.2.1 (h₁.2.2.2.2 lam₂ h h₂.2.1 h₂.2.2.1)

/-! ### The failure stage of a single ordinal -/

/-- `γ` is an ordinal above `ν` at which the small embedding for `ν` fails, or `ν` lies outside
the interval `ρ ⊆ ν ⊆ r` and `γ` is any ordinal above `ν`. The second clause makes the least
such `γ` defined for every ordinal `ν`, which is what replacement needs. -/
def IsMagidorFailureStage (ρ r ν γ : V) : Prop :=
  IsOrdinal γ ∧ ν ∈ γ ∧ (¬ (ρ ⊆ ν ∧ ν ⊆ r) ∨ ¬ IsMagidorSupercompactAt ν γ)

theorem isMagidorFailureStage_definable_pred (ρ r ν : V) :
    ℒₛₑₜ-predicate[V] (IsMagidorFailureStage ρ r ν) := by
  unfold IsMagidorFailureStage
  definability

/-- Under the failure hypothesis every ordinal has a failure stage. -/
theorem exists_isMagidorFailureStage {ξ r : V} [IsOrdinal ξ]
    (hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ) (ν : V) [IsOrdinal ν] :
    ∃ γ : V, IsOrdinal γ ∧ IsMagidorFailureStage (succ ξ) r ν γ := by
  classical
  by_cases hc : succ ξ ⊆ ν ∧ ν ⊆ r
  · have hξν : ξ ∈ ν := hc.1 ξ (mem_succ_self ξ)
    have hfail : ∃ γ : V, IsOrdinal γ ∧ ν ∈ γ ∧ ¬ IsMagidorSupercompactAt ν γ := by
      by_contra hcon
      refine hno ν hξν ⟨inferInstance, fun γ hγ hνγ ↦ ?_⟩
      by_contra h
      exact hcon ⟨γ, hγ, hνγ, h⟩
    obtain ⟨γ, hγ, hνγ, hf⟩ := hfail
    exact ⟨γ, hγ, hγ, hνγ, Or.inr hf⟩
  · exact ⟨succ ν, inferInstance, inferInstance, mem_succ_self ν, Or.inl hc⟩

theorem magidorFailStep_existsUnique (ρ r ν : V)
    (h : ∃ γ : V, IsOrdinal γ ∧ IsMagidorFailureStage ρ r ν γ) :
    ∃! γ, IsLeastOrdinal (IsMagidorFailureStage ρ r ν) γ :=
  leastOrdinal_existsUnique _ (isMagidorFailureStage_definable_pred ρ r ν) h

/-- The least failure stage of `ν`, and `∅` when there is none. -/
noncomputable def magidorFailStep (ρ r ν : V) : V := by
  classical
  exact if h : ∃ γ : V, IsOrdinal γ ∧ IsMagidorFailureStage ρ r ν γ then
    Classical.choose! (magidorFailStep_existsUnique ρ r ν h) else ∅

theorem magidorFailStep_eq_iff (ρ r ν γ : V) :
    magidorFailStep ρ r ν = γ ↔ IsLeastOrdinal (IsMagidorFailureStage ρ r ν) γ ∨
      ((¬∃ δ : V, IsOrdinal δ ∧ IsMagidorFailureStage ρ r ν δ) ∧ γ = ∅) := by
  classical
  by_cases h : ∃ δ : V, IsOrdinal δ ∧ IsMagidorFailureStage ρ r ν δ
  · simp only [h, not_true_eq_false, false_and, or_false]
    have hspec : IsLeastOrdinal (IsMagidorFailureStage ρ r ν) (magidorFailStep ρ r ν) := by
      simpa [magidorFailStep, h] using
        Classical.choose!_spec (magidorFailStep_existsUnique ρ r ν h)
    constructor
    · rintro rfl
      exact hspec
    · intro hγ
      exact (magidorFailStep_existsUnique ρ r ν h).unique hspec hγ
  · have hn : ¬IsLeastOrdinal (IsMagidorFailureStage ρ r ν) γ := fun hl ↦ h ⟨γ, hl.1, hl.2.1⟩
    simp [magidorFailStep, h, hn, eq_comm]

theorem magidorFailStep_definable (ρ r : V) : ℒₛₑₜ-function₁ (magidorFailStep ρ r) := by
  have h : ℒₛₑₜ-relation (fun γ ν : V ↦ IsLeastOrdinal (IsMagidorFailureStage ρ r ν) γ ∨
      ((¬∃ δ : V, IsOrdinal δ ∧ IsMagidorFailureStage ρ r ν δ) ∧ γ = ∅)) := by
    unfold IsLeastOrdinal IsMagidorFailureStage
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (magidorFailStep_eq_iff ρ r (v 1) (v 0))

theorem magidorFailStep_spec {ξ r : V} [IsOrdinal ξ]
    (hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ) (ν : V) [IsOrdinal ν] :
    IsLeastOrdinal (IsMagidorFailureStage (succ ξ) r ν) (magidorFailStep (succ ξ) r ν) := by
  rcases (magidorFailStep_eq_iff (succ ξ) r ν (magidorFailStep (succ ξ) r ν)).mp rfl with h | ⟨h, -⟩
  · exact h
  · exact absurd (exists_isMagidorFailureStage hno ν) h

theorem magidorFailStep_isOrdinal {ξ r : V} [IsOrdinal ξ]
    (hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ) (ν : V) [IsOrdinal ν] :
    IsOrdinal (magidorFailStep (succ ξ) r ν) := (magidorFailStep_spec hno ν).1

theorem mem_magidorFailStep {ξ r : V} [IsOrdinal ξ]
    (hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ) (ν : V) [IsOrdinal ν] :
    ν ∈ magidorFailStep (succ ξ) r ν := (magidorFailStep_spec hno ν).2.1.2.1

/-- Inside the interval the least failure stage really is a failure. -/
theorem not_magidorSupercompactAt_magidorFailStep {ξ r : V} [IsOrdinal ξ]
    (hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ) {ν : V} [IsOrdinal ν]
    (hρν : succ ξ ⊆ ν) (hνr : ν ⊆ r) :
    ¬ IsMagidorSupercompactAt ν (magidorFailStep (succ ξ) r ν) := by
  rcases (magidorFailStep_spec hno ν).2.1.2.2 with hout | hf
  · exact absurd ⟨hρν, hνr⟩ hout
  · exact hf

/-! ### Existence -/

/-- A limit ordinal above `r` on which the whole interval fails, obtained by closing an ordinal
under the least failure stage function. -/
theorem exists_magidorFailureLimit {ξ r : V} [IsOrdinal ξ] [IsOrdinal r]
    (hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ) :
    ∃ lam : V, IsLimitOrdinal lam ∧ r ∈ lam ∧ (∀ x ∈ lam, succ x ∈ lam) ∧
      NoMagidorSupercompactBetween (succ ξ) r lam := by
  have hGord : ∀ ν : V, IsOrdinal ν → IsOrdinal (magidorFailStep (succ ξ) r ν) :=
    fun ν hν ↦ have : IsOrdinal ν := hν; magidorFailStep_isOrdinal hno ν
  have hGgt : ∀ ν : V, IsOrdinal ν → ν ∈ magidorFailStep (succ ξ) r ν :=
    fun ν hν ↦ have : IsOrdinal ν := hν; mem_magidorFailStep hno ν
  obtain ⟨lam, hrlam, hclosed⟩ :=
    exists_ordinalClosurePoint_above (magidorFailStep_definable (succ ξ) r) hGord hGgt r
  have hlim : IsLimitOrdinal lam := IsOrdinalClosurePoint.limit hGgt hclosed
  have hlamord : IsOrdinal lam := hclosed.1
  refine ⟨lam, hlim, hrlam, fun x hx ↦ succ_mem_of_isLimitOrdinal' hlim hx, ?_⟩
  intro ν hν hρν hνr hup
  have : IsOrdinal ν := hν
  have hνlam : ν ∈ lam := by
    rcases IsOrdinal.subset_iff.mp hνr with rfl | hlt
    · exact hrlam
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hrlam
  have hstep : magidorFailStep (succ ξ) r ν ∈ lam := hclosed.2.2 ν hνlam
  exact not_magidorSupercompactAt_magidorFailStep hno hρν hνr
    (hup _ hstep (magidorFailStep_isOrdinal hno ν) (mem_magidorFailStep hno ν))

/-- The least such limit ordinal exists. -/
theorem exists_leastMagidorFailureLimit {ξ r : V} [IsOrdinal ξ] [IsOrdinal r]
    (hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ) (hr : succ ξ ⊆ r) :
    ∃ lam : V, IsLeastMagidorFailureLimit (succ ξ) r lam := by
  obtain ⟨lam₀, hlim₀, hr₀, -, hno₀⟩ := exists_magidorFailureLimit (r := r) hno
  have hex : ∃ x : V, IsOrdinal x ∧
      (IsLimitOrdinal x ∧ r ∈ x ∧ NoMagidorSupercompactBetween (succ ξ) r x) :=
    ⟨lam₀, hlim₀.1, hlim₀, hr₀, hno₀⟩
  have hdef : ℒₛₑₜ-predicate[V]
      (fun x ↦ IsLimitOrdinal x ∧ r ∈ x ∧ NoMagidorSupercompactBetween (succ ξ) r x) := by
    unfold IsLimitOrdinal NoMagidorSupercompactBetween
    definability
  obtain ⟨lam, hlam, -⟩ := leastOrdinal_existsUnique _ hdef hex
  obtain ⟨hord, ⟨hlim, hrlam, hfail⟩, hmin⟩ := hlam
  refine ⟨lam, hord, hlim, hrlam, hfail, fun μ hμ hlimμ hrμ hnoμ ↦ ?_⟩
  exact mem_irrefl μ (hmin μ hlimμ.1 ⟨hlimμ, hrμ, hnoμ⟩ μ hμ)

/-- Unboundedness, in the form the class machinery uses: for every ordinal `γ` there is a
parameter `r` above `γ` and above `ξ` whose least failure limit `lam` contains `γ`, `ω`, `r` and
`succ ξ`, and is closed under successor. -/
theorem leastMagidorFailureLimit_unbounded {ξ : V} [IsOrdinal ξ]
    (hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ) (γ : V) (hγ : IsOrdinal γ) :
    ∃ r lam : V, IsOrdinal r ∧ succ ξ ⊆ r ∧ γ ∈ lam ∧ r ∈ lam ∧ succ ξ ⊆ lam ∧
      (ω : V) ∈ lam ∧ (∀ x ∈ lam, succ x ∈ lam) ∧ IsLeastMagidorFailureLimit (succ ξ) r lam := by
  have : IsOrdinal γ := hγ
  obtain ⟨m₀, hm₀, hγm₀, hξm₀⟩ := exists_ordinal_upper_bound₂ γ ξ
  have : IsOrdinal m₀ := hm₀
  obtain ⟨m, hm, hm₀m, hωm⟩ := exists_ordinal_upper_bound₂ m₀ (ω : V)
  have : IsOrdinal m := hm
  have hmr : IsOrdinal (succ m) := inferInstance
  have hγm : γ ⊆ m := fun x hx ↦ hm₀m _ (hγm₀ _ hx)
  have hξm : ξ ⊆ m := fun x hx ↦ hm₀m _ (hξm₀ _ hx)
  have hγsm : γ ∈ succ m := by
    rcases IsOrdinal.subset_iff.mp hγm with rfl | h
    · exact mem_succ_self _
    · exact mem_succ_iff.mpr (Or.inr h)
  have hξsm : ξ ∈ succ m := by
    rcases IsOrdinal.subset_iff.mp hξm with rfl | h
    · exact mem_succ_self _
    · exact mem_succ_iff.mpr (Or.inr h)
  have hωsm : (ω : V) ∈ succ m := by
    rcases IsOrdinal.subset_iff.mp hωm with rfl | h
    · exact mem_succ_self _
    · exact mem_succ_iff.mpr (Or.inr h)
  have hr : succ ξ ⊆ succ m := succ_subset_of_mem_ordinal' hξsm
  obtain ⟨lam, hlam⟩ := exists_leastMagidorFailureLimit (r := succ m) hno hr
  have hlamord : IsOrdinal lam := hlam.1
  have hrlam : succ m ∈ lam := hlam.2.2.1
  refine ⟨succ m, lam, hmr, hr, ?_, hrlam, ?_, ?_, ?_, hlam⟩
  · exact IsOrdinal.toIsTransitive.mem_trans hγsm hrlam
  · exact succ_subset_of_mem_ordinal'
      (IsOrdinal.toIsTransitive.mem_trans hξsm hrlam)
  · exact IsOrdinal.toIsTransitive.mem_trans hωsm hrlam
  · exact fun x hx ↦ succ_mem_of_isLimitOrdinal' hlam.2.1 hx

end ZFVP
