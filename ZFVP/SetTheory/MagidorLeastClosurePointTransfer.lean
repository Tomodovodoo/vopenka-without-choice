import ZFVP.SetTheory.MagidorClosurePoint

/-! # The least closure point above a marker, and its transfer

`ZFVP.SetTheory.MagidorClosurePoint` shows that the closure points of the failure function
`magidorFailure ρ` transfer along a coded embedding between two rank stages `V_{lam+ω}` and
`V_{lam'+ω}`. The `C(n)` argument needs one more step: it picks the *least* closure point above a
marker `ν`, and it needs that ordinal to be fixed by the embedding once `ν` is.

This module is Part 3 of `MagidorClosurePoint` continued. `IsLeastMagidorClosurePointAbove ρ ν d`
says that `d` is a closure point with `ν ∈ d` and no closure point strictly between `ν` and `d`.
Minimality is written as "no smaller one is a closure point" rather than "`d` is below every
closure point", so that only elements of `d` are quantified over and the condition turns into a
bounded formula on the model of `boundedMagidorClosurePointFormula`.

The transfer then follows the same route as `magidorClosurePoint_value_iff`: one auxiliary stage
`ν₀` inside `lam+ω` holding `d`, the bounded formula crossing the embedding, and the stage lemma on
both sides. The corollary `value_eq_of_isLeastMagidorClosurePointAbove` is what the caller wants:
if the embedding fixes `ν` then it fixes the least closure point above `ν`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ## The set theory -/

/-- `d` is the least closure point of the failure function above `ν`: a closure point containing
`ν` with no closure point strictly between `ν` and `d`. -/
def IsLeastMagidorClosurePointAbove (ρ ν d : V) : Prop :=
  ν ∈ d ∧ IsMagidorClosurePoint ρ d ∧ ∀ ξ ∈ d, ν ∈ ξ → ¬ IsMagidorClosurePoint ρ ξ

/-- There is at most one least closure point above a given `ν`. -/
theorem isLeastMagidorClosurePointAbove_unique {ρ ν d₁ d₂ : V}
    (h₁ : IsLeastMagidorClosurePointAbove ρ ν d₁)
    (h₂ : IsLeastMagidorClosurePointAbove ρ ν d₂) : d₁ = d₂ := by
  obtain ⟨hν₁, hcp₁, hmin₁⟩ := h₁
  obtain ⟨hν₂, hcp₂, hmin₂⟩ := h₂
  have hd₁ : IsOrdinal d₁ := hcp₁.1.1
  have hd₂ : IsOrdinal d₂ := hcp₂.1.1
  have : IsOrdinal d₁ := hd₁
  have : IsOrdinal d₂ := hd₂
  rcases IsOrdinal.mem_trichotomy (α := d₁) (β := d₂) with hlt | heq | hgt
  · exact absurd hcp₁ (hmin₂ d₁ hlt hν₁)
  · exact heq
  · exact absurd hcp₂ (hmin₁ d₂ hgt hν₂)

/-! ## The bounded formula -/

/-- `d` is the least closure point above `ν`, with the closure point condition named by its
bounded formula. Free variables: `ρ`, `ν`, `d`, `W`. -/
def boundedLeastMagidorClosurePointAboveFormula : SetTheorySemisentence 4 :=
  “ρ ν d W. !boundedMagidorClosurePointFormula ρ d W ∧ ν ∈ d ∧
    ∀ ξ ∈ d, ν ∈ ξ → ¬!boundedMagidorClosurePointFormula ρ ξ W”

theorem boundedLeastMagidorClosurePointAboveFormula_bounded :
    IsBoundedSetFormula boundedLeastMagidorClosurePointAboveFormula :=
  .and (boundedMagidorClosurePointFormula_bounded.subst _)
    (.and (.rel _ _)
      (.all (.bvar 2) (.or (.nrel _ _)
        (boundedMagidorClosurePointFormula_bounded.subst _).neg)))

/-- The literal reading of `boundedLeastMagidorClosurePointAboveFormula`. -/
def BoundedLeastMagidorClosurePointAbove (ρ ν d W : V) : Prop :=
  BoundedMagidorClosurePoint ρ d W ∧ ν ∈ d ∧
    ∀ ξ ∈ d, ν ∈ ξ → ¬ BoundedMagidorClosurePoint ρ ξ W

instance boundedLeastMagidorClosurePointAboveFormula_defined :
    ℒₛₑₜ-relation₄[V] BoundedLeastMagidorClosurePointAbove
      via boundedLeastMagidorClosurePointAboveFormula :=
  ⟨fun v ↦ by
    simp [boundedLeastMagidorClosurePointAboveFormula, BoundedLeastMagidorClosurePointAbove,
      (boundedMagidorClosurePointFormula_defined (V := V)).iff,
      Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton]⟩

/-- At a successor closed rank stage above `ω` that holds the membership formula family and has
`d` below it, the bounded reading says exactly that `d` is the least closure point above `ν`.
Every closure point argument quantified in the formula is an element of `d`, hence also below the
stage, so `boundedMagidorClosurePoint_iff` applies to each of them. -/
theorem boundedLeastMagidorClosurePointAbove_iff {ν₀ ρ ν d : V} [IsOrdinal ν₀]
    (hω : (ω : V) ∈ ν₀) (hsucc : ∀ ξ ∈ ν₀, succ ξ ∈ ν₀)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy ν₀)
    (htot : MagidorFailureTotal ρ) (hdν₀ : d ∈ ν₀) :
    BoundedLeastMagidorClosurePointAbove ρ ν d (hierarchy ν₀) ↔
      IsLeastMagidorClosurePointAbove ρ ν d := by
  have hmem : ∀ ξ ∈ d, BoundedMagidorClosurePoint ρ ξ (hierarchy ν₀) ↔
      IsMagidorClosurePoint ρ ξ := by
    intro ξ hξ
    exact boundedMagidorClosurePoint_iff hω hsucc hF htot
      (IsOrdinal.toIsTransitive.mem_trans hξ hdν₀)
  unfold BoundedLeastMagidorClosurePointAbove IsLeastMagidorClosurePointAbove
  constructor
  · rintro ⟨hcp, hνd, hmin⟩
    refine ⟨hνd, (boundedMagidorClosurePoint_iff hω hsucc hF htot hdν₀).mp hcp, ?_⟩
    intro ξ hξ hνξ hcpξ
    exact hmin ξ hξ hνξ ((hmem ξ hξ).mpr hcpξ)
  · rintro ⟨hνd, hcp, hmin⟩
    refine ⟨(boundedMagidorClosurePoint_iff hω hsucc hF htot hdν₀).mpr hcp, hνd, ?_⟩
    intro ξ hξ hνξ hcpξ
    exact hmin ξ hξ hνξ ((hmem ξ hξ).mp hcpξ)

/-! ## Transfer along a coded embedding -/

/-- The side conditions on an auxiliary stage cross a coded embedding between rank stages.
Copied from `ZFVP.SetTheory.MagidorClosurePoint`, where it is private. -/
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

/-- An auxiliary stage inside `V_{lam+ω}` holding a prescribed ordinal of `lam`.
Copied from `ZFVP.SetTheory.MagidorClosurePoint`, where it is private. -/
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

/-- Being the least closure point above `ν` transfers along a coded embedding between the stages
`V_{lam+ω}` and `V_{lam'+ω}`, for markers and closure points below `lam`. -/
theorem leastMagidorClosurePointAbove_value_iff {lam lam' f ρ ν d : V} [IsOrdinal lam]
    [IsOrdinal lam']
    (hlim : IsLimitOrdinal lam) (hωlam : (ω : V) ∈ lam)
    (hlim' : IsLimitOrdinal lam') (hωlam' : (ω : V) ∈ lam')
    (h : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam (ω : V)))
      (hierarchy (ordinalAdd lam' (ω : V))) f)
    (htot : MagidorFailureTotal ρ) (hfρ : f ‘ ρ = ρ) (hd : d ∈ lam) (hρd : ρ ∈ d)
    (hνd : ν ∈ d) :
    IsLeastMagidorClosurePointAbove ρ ν d ↔
      IsLeastMagidorClosurePointAbove ρ (f ‘ ν) (f ‘ d) := by
  have hdord : IsOrdinal d := IsOrdinal.of_mem hd
  let := hdord
  obtain ⟨ν₀, hν₀ord, hων₀, hsuccν₀, hdν₀, hFν₀, hν₀θ⟩ := exists_aux_stage hlim hωlam hd
  let := hν₀ord
  have hρν₀ : ρ ∈ ν₀ := IsOrdinal.toIsTransitive.mem_trans hρd hdν₀
  have hνν₀ : ν ∈ ν₀ := IsOrdinal.toIsTransitive.mem_trans hνd hdν₀
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
  have hνH : ν ∈ hierarchy (ordinalAdd lam (ω : V)) :=
    (hierarchy_transitive _).mem_trans hνν₀ hν₀H
  have hdH : d ∈ hierarchy (ordinalAdd lam (ω : V)) :=
    (hierarchy_transitive _).mem_trans hdν₀ hν₀H
  obtain ⟨hvord, hvW, hων', hsuccν', hFν'⟩ :=
    transfer_stage_conditions hωθ hsuccθ hωθ' hsuccθ' h hων₀ hsuccν₀ hν₀θ hFν₀
  let := hvord
  have hdν₀' : f ‘ d ∈ f ‘ ν₀ := (h.value_mem_iff hdH hν₀H).mpr hdν₀
  have hv : ∀ i, (![ρ, ν, d, hierarchy ν₀] : Fin 4 → V) i ∈
      hierarchy (ordinalAdd lam (ω : V)) := by
    simp [Fin.forall_fin_iff_zero_and_forall_succ, hρH, hνH, hdH, hWH]
  have hiff := h.bounded_defined_iff boundedLeastMagidorClosurePointAboveFormula_bounded
    (fun v ↦ BoundedLeastMagidorClosurePointAbove (v 0) (v 1) (v 2) (v 3))
    ![ρ, ν, d, hierarchy ν₀] hv
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three] at hiff
  rw [hvW, hfρ] at hiff
  exact (boundedLeastMagidorClosurePointAbove_iff hων₀ hsuccν₀ hFν₀ htot hdν₀).symm.trans
    (hiff.trans
      (boundedLeastMagidorClosurePointAbove_iff hων' hsuccν' hFν' htot hdν₀'))

/-- If a coded embedding fixes `ρ` and fixes the marker `ν`, it fixes the least closure point
above `ν`. -/
theorem value_eq_of_isLeastMagidorClosurePointAbove {lam lam' f ρ ν d : V} [IsOrdinal lam]
    [IsOrdinal lam']
    (hlim : IsLimitOrdinal lam) (hωlam : (ω : V) ∈ lam)
    (hlim' : IsLimitOrdinal lam') (hωlam' : (ω : V) ∈ lam')
    (h : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam (ω : V)))
      (hierarchy (ordinalAdd lam' (ω : V))) f)
    (htot : MagidorFailureTotal ρ) (hfρ : f ‘ ρ = ρ) (hd : d ∈ lam) (hρd : ρ ∈ d)
    (hνd : ν ∈ d) (hfν : f ‘ ν = ν) (hleast : IsLeastMagidorClosurePointAbove ρ ν d) :
    f ‘ d = d := by
  have himg : IsLeastMagidorClosurePointAbove ρ (f ‘ ν) (f ‘ d) :=
    (leastMagidorClosurePointAbove_value_iff hlim hωlam hlim' hωlam' h htot hfρ hd hρd hνd).mp
      hleast
  rw [hfν] at himg
  exact isLeastMagidorClosurePointAbove_unique himg hleast

end ZFVP
