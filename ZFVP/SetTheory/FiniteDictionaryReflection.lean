import ZFVP.SetTheory.CnExtendibleSmallEmbedding
import ZFVP.SetTheory.OrdinalAddition
import ZFVP.SetTheory.LevyComplexityBound

/-! Lemma lem:finite-reflection: a finite dictionary `D` of formulas in the six variables
`η δ θ ρ α x` is reflected by a `C(k+1)`-extendible cardinal `δ` from a `C(c)` stage `ρ` (with
an `ω` buffer above `θ`) to a reflected tuple `δ' θ' ρ' α' x'` below `δ`, together with an
elementary `J : V_ρ' → V_ρ` with critical point `δ'` moving `δ' θ' α' x'` to `δ θ α x`.
The reflected statement `Φ` is a fixed Σ_{c+1} formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Conjunction of a finite list of formulas in six variables. -/
def listConj : List (SetTheorySemisentence 6) → SetTheorySemisentence 6
  | [] => ⊤
  | e :: D => e ⋏ listConj D

/-- The largest syntactic Levy bound of a dictionary. -/
def listBound : List (SetTheorySemisentence 6) → ℕ
  | [] => 0
  | e :: D => max (levySyntacticBound e) (listBound D)

theorem listConj_levy (D : List (SetTheorySemisentence 6)) (p : LevyPolarity) :
    IsLevyFormula p (listBound D) (listConj D) := by
  induction D with
  | nil => exact .bounded .verum
  | cons e D ih =>
    exact .and ((isLevyFormula_syntacticBound e p).mono (Nat.le_max_left _ _))
      (ih.mono (Nat.le_max_right _ _))

/-- `γ` is the least successor-closed ordinal above `θ`, i.e. `γ = θ + ω`. -/
def plusOmegaFormula : SetTheorySemisentence 2 :=
  “γ θ. !IsOrdinal.dfn θ ∧ !IsOrdinal.dfn γ ∧ θ ∈ γ ∧ (∀ ξ ∈ γ, ∃ σ ∈ γ, !boundedSuccFormula σ ξ) ∧
    ∀ ξ ∈ γ, θ ∈ ξ → ∃ ζ ∈ ξ, ∀ σ ∈ ξ, ¬!boundedSuccFormula σ ζ”

theorem plusOmegaFormula_bounded : IsBoundedSetFormula plusOmegaFormula := by
  exact .and (isOrdinalFormula_bounded.subst _) (.and (isOrdinalFormula_bounded.subst _)
    (.and (.rel _ _) (.and (.all _ (.exs _ (boundedSuccFormula_bounded.subst _)))
      (.all _ (.or (.nrel _ _) (.exs _ (.all _ ((boundedSuccFormula_bounded.subst _).neg))))))))

theorem eval_listConj {V : Type*} [SetStructure V] (D : List (SetTheorySemisentence 6))
    (v : Fin 6 → V) : (listConj D).Evalb v ↔ ∀ e ∈ D, e.Evalb v := by
  induction D with
  | nil => simp [listConj]
  | cons e D ih => simp [listConj, ih]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The graph of `θ ↦ θ + ω` on ordinals. -/
def IsPlusOmega (γ θ : V) : Prop := IsOrdinal θ ∧ γ = ordinalAdd θ (ω : V)

theorem ordinalAdd_natural_mem_of_succ_closed {θ ξ : V} [IsOrdinal θ] (hθ : θ ∈ ξ)
    (hsucc : ∀ β ∈ ξ, succ β ∈ ξ) : ∀ n ∈ (ω : V), ordinalAdd θ n ∈ ξ := by
  apply naturalNumber_induction (fun n ↦ ordinalAdd θ n ∈ ξ) (by definability)
  · rw [zero_def, ordinalAdd_zero]; exact hθ
  · intro n hn ih
    have : IsOrdinal n := IsOrdinal.of_mem hn
    rw [ordinalAdd_succ]
    exact hsucc _ ih

theorem not_succ_closed_of_mem_ordinalAdd_omega {θ ξ : V} [IsOrdinal θ]
    (hξ : ξ ∈ ordinalAdd θ (ω : V)) (hθ : θ ∈ ξ) : ¬∀ β ∈ ξ, succ β ∈ ξ := by
  intro hsucc
  rcases (mem_ordinalAdd_iff θ ω ξ).mp hξ with h | ⟨n, hn, h⟩
  · exact mem_asymm hθ h
  · have hmem := ordinalAdd_natural_mem_of_succ_closed hθ hsucc n hn
    rcases mem_succ_iff.mp h with rfl | h
    · exact mem_irrefl _ hmem
    · exact mem_asymm hmem h

theorem eval_plusOmegaFormula (γ θ : V) :
    plusOmegaFormula.Evalb ![γ, θ] ↔ IsPlusOmega γ θ := by
  simp only [plusOmegaFormula, IsPlusOmega]
  simp
  intro hθ
  have := hθ
  constructor
  · rintro ⟨hγ, hθγ, hsucc, hmin⟩
    have := hγ
    rcases IsOrdinal.mem_trichotomy (α := γ) (β := ordinalAdd θ ω) with h | h | h
    · exact (not_succ_closed_of_mem_ordinalAdd_omega h hθγ hsucc).elim
    · exact h
    · obtain ⟨ζ, hζ, hζs⟩ := hmin _ h (ordinalAdd_omega_gt θ)
      exact (hζs _ (ordinalAdd_omega_succ_closed θ hζ) rfl).elim
  · rintro rfl
    refine ⟨inferInstance, ordinalAdd_omega_gt θ, fun ξ hξ ↦ ordinalAdd_omega_succ_closed θ hξ, ?_⟩
    intro ξ hξ hθξ
    have h := not_succ_closed_of_mem_ordinalAdd_omega hξ hθξ
    push Not at h
    obtain ⟨ζ, hζ, hζs⟩ := h
    exact ⟨ζ, hζ, fun σ hσ hσζ ↦ hζs (hσζ ▸ hσ)⟩

instance plusOmegaFormula_defined : ℒₛₑₜ-relation[V] IsPlusOmega via plusOmegaFormula :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    change plusOmegaFormula.Evalb v ↔ IsPlusOmega (v 0) (v 1)
    rw [← hv]
    exact eval_plusOmegaFormula _ _⟩

/-- The matrix of the reflected statement, in the variables
`η δ θ ρ α x δ' θ' ρ' α' x' A B J`. -/
def reflectionMatrix (c : ℕ) (D : List (SetTheorySemisentence 6)) : SetTheorySemisentence 14 :=
  “η δ θ ρ α x δ' θ' ρ' α' x' A B J.
    η ∈ δ' ∧ δ' ∈ θ' ∧ (∃ γ ∈ ρ', !plusOmegaFormula γ θ') ∧ ρ' ∈ δ ∧ δ ∈ θ ∧
    (∃ γ ∈ ρ, !plusOmegaFormula γ θ) ∧ α' ∈ θ' ∧
    !piOneHierarchyFormula A ρ' ∧ x' ∈ A ∧ !piOneHierarchyFormula B ρ ∧
    !piOneMembershipEmbeddingFormula A B J ∧ !boundedCriticalPointFormula A J δ' ∧
    !boundedPairMemberFormula J δ' δ ∧ !boundedPairMemberFormula J θ' θ ∧
    !boundedPairMemberFormula J α' α ∧ !boundedPairMemberFormula J x' x ∧
    !(cnFormula c) ρ' ∧ !(listConj D) η δ' θ' ρ' α' x'”

/-- The reflected statement `Φ(η, δ, θ, ρ, α, x)`. -/
def reflectionFormula (c : ℕ) (D : List (SetTheorySemisentence 6)) : SetTheorySemisentence 6 :=
  “η δ θ ρ α x. ∃ δ' θ' ρ' α' x' A B J, !(reflectionMatrix c D) η δ θ ρ α x δ' θ' ρ' α' x' A B J”

theorem reflectionMatrix_pi {c : ℕ} (hc : 2 ≤ c) (D : List (SetTheorySemisentence 6))
    (hD : listBound D ≤ c) : IsPiFormula c (reflectionMatrix c D) := by
  unfold reflectionMatrix
  exact .and (.bounded (.rel _ _)) (.and (.bounded (.rel _ _))
    (.and (.bounded (.exs _ (plusOmegaFormula_bounded.subst _)))
    (.and (.bounded (.rel _ _)) (.and (.bounded (.rel _ _))
    (.and (.bounded (.exs _ (plusOmegaFormula_bounded.subst _)))
    (.and (.bounded (.rel _ _))
    (.and ((piOneHierarchyFormula_piOne.mono (by omega)).subst _)
    (.and (.bounded (.rel _ _))
    (.and ((piOneHierarchyFormula_piOne.mono (by omega)).subst _)
    (.and ((piOneMembershipEmbeddingFormula_piOne.mono (by omega)).subst _)
    (.and (.bounded (boundedCriticalPointFormula_bounded.subst _))
    (.and (.bounded (boundedPairMemberFormula_bounded.subst _))
    (.and (.bounded (boundedPairMemberFormula_bounded.subst _))
    (.and (.bounded (boundedPairMemberFormula_bounded.subst _))
    (.and (.bounded (boundedPairMemberFormula_bounded.subst _))
    (.and ((cnFormula_pi hc).subst _)
      (((listConj_levy D .pi).mono hD).subst _)))))))))))))))))

theorem reflectionFormula_sigma {c : ℕ} (hc : 2 ≤ c) (D : List (SetTheorySemisentence 6))
    (hD : listBound D ≤ c) : IsSigmaFormula (c + 1) (reflectionFormula c D) := by
  unfold reflectionFormula
  repeat' apply IsLevyFormula.exs
  exact ((reflectionMatrix_pi hc D hD).raise).subst _

/-- The matrix as a relation on a 14-tuple. -/
def ReflectionMatrix (c : ℕ) (D : List (SetTheorySemisentence 6)) (w : Fin 14 → V) : Prop :=
  w 0 ∈ w 6 ∧ w 6 ∈ w 7 ∧ (∃ γ ∈ w 8, IsPlusOmega γ (w 7)) ∧ w 8 ∈ w 1 ∧ w 1 ∈ w 2 ∧
    (∃ γ ∈ w 3, IsPlusOmega γ (w 2)) ∧ w 9 ∈ w 7 ∧
    (IsOrdinal (w 8) ∧ w 11 = hierarchy (w 8)) ∧ w 10 ∈ w 11 ∧
    (IsOrdinal (w 3) ∧ w 12 = hierarchy (w 3)) ∧
    IsCodedMembershipEmbedding (w 11) (w 12) (w 13) ∧ CriticalPointGraphSpec (w 11) (w 13) (w 6) ∧
    ⟨w 6, w 1⟩ₖ ∈ w 13 ∧ ⟨w 7, w 2⟩ₖ ∈ w 13 ∧ ⟨w 9, w 4⟩ₖ ∈ w 13 ∧ ⟨w 10, w 5⟩ₖ ∈ w 13 ∧
    Cn c (w 8) ∧ ∀ e ∈ D, e.Evalb ![w 0, w 6, w 7, w 8, w 9, w 10]

theorem eval_reflectionMatrix (c : ℕ) (D : List (SetTheorySemisentence 6)) (w : Fin 14 → V) :
    (reflectionMatrix c D).Evalb w ↔ ReflectionMatrix c D w := by
  simp [reflectionMatrix, ReflectionMatrix, IsHierarchySegment, eval_listConj, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def]

/-- `Φ(η, δ, θ, ρ, α, x)` as a relation on a 6-tuple. -/
def Reflects (c : ℕ) (D : List (SetTheorySemisentence 6)) (v : Fin 6 → V) : Prop :=
  ∃ δ' θ' ρ' α' x' A B J : V,
    ReflectionMatrix c D ![v 0, v 1, v 2, v 3, v 4, v 5, δ', θ', ρ', α', x', A, B, J]

theorem eval_reflectionFormula (c : ℕ) (D : List (SetTheorySemisentence 6)) (v : Fin 6 → V) :
    (reflectionFormula c D).Evalb v ↔ Reflects c D v := by
  simp only [reflectionFormula, Reflects]
  simp [eval_reflectionMatrix, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

instance reflectionFormula_defined (c : ℕ) (D : List (SetTheorySemisentence 6)) :
    Defined (Reflects (V := V) c D) (reflectionFormula c D) :=
  ⟨fun v ↦ eval_reflectionFormula c D v⟩

/-- Lemma lem:finite-reflection. -/
theorem finite_reflection_of_complexity {c k : ℕ} (D : List (SetTheorySemisentence 6))
    (hF : IsSigmaFormula (k + 1) (reflectionFormula c D)) {η δ θ ρ α x : V}
    (hδ : IsCnExtendible (k + 1) δ) (hρ : Cn c ρ)
    (hηδ : η ∈ δ) (hδθ : δ ∈ θ) (hθρ : ordinalAdd θ (ω : V) ∈ ρ) (hαθ : α ∈ θ)
    (hx : x ∈ hierarchy ρ) (hDtrue : ∀ e ∈ D, e.Evalb ![η, δ, θ, ρ, α, x]) :
    Reflects c D ![η, δ, θ, ρ, α, x] := by
  let := hρ.ordinal
  have hθρ' : θ ∈ ρ := IsOrdinal.toIsTransitive.mem_trans (ordinalAdd_omega_gt θ) hθρ
  have hθ : IsOrdinal θ := IsOrdinal.of_mem hθρ'
  have hδρ : δ ∈ ρ := IsOrdinal.toIsTransitive.mem_trans hδθ hθρ'
  have hαρ : α ∈ ρ := IsOrdinal.toIsTransitive.mem_trans hαθ hθρ'
  obtain ⟨μ, hρμ, hμ⟩ := cn_unbounded (k + 1) ρ
  let := hμ.ordinal
  have hδμ : δ ∈ μ := IsOrdinal.toIsTransitive.mem_trans hδρ hρμ
  obtain ⟨ν, e, hμν, hν, he, hcrit, hμeδ⟩ := hδ.2 μ hμ hδμ
  let := hν.ordinal
  let := hierarchy_transitive μ
  let := hierarchy_transitive ν
  let := hierarchy_transitive ρ
  let := IsFunction.of_mem he.function
  have hρV : ρ ∈ hierarchy μ := ordinal_subset_hierarchy μ ρ hρμ
  have hV : ∀ y ∈ ρ, y ∈ hierarchy μ := fun y hy ↦
    ordinal_subset_hierarchy μ y (IsOrdinal.toIsTransitive.mem_trans hy hρμ)
  have hxV : x ∈ hierarchy μ := (hierarchy_transitive μ).mem_trans hx (hierarchy_mem hρμ)
  have hρsub : hierarchy ρ ⊆ hierarchy μ := (hierarchy_transitive μ).transitive _ (hierarchy_mem hρμ)
  -- the restricted embedding `J : V_ρ → V_{e(ρ)}`
  have hr := rankEmbedding_restrict hμ hν he (hierarchy_mem hρμ) ⟨θ, ordinal_subset_hierarchy ρ θ hθρ'⟩
  have hvh := rankEmbedding_value_hierarchy hμ hν he hρ.ordinal hρV
  rw [hvh.2] at hr
  let := IsFunction.of_mem hr.function
  have hcr := hcrit.restrict he.function hρsub (ordinal_subset_hierarchy ρ δ hδρ)
  have hJv : ∀ y ∈ hierarchy ρ, (e ↾ (hierarchy ρ)) ‘ y = e ‘ y := fun y hy ↦
    value_restrict (by rw [domain_eq_of_mem_function he.function]; exact hρsub _ hy) hy
  have hJpair : ∀ y ∈ hierarchy ρ, ⟨y, e ‘ y⟩ₖ ∈ e ↾ (hierarchy ρ) := fun y hy ↦ by
    rw [← hJv y hy]
    exact kpair_value_mem (by rw [domain_eq_of_mem_function hr.function]; exact hy)
  -- the buffer is transported by `e`
  have hbuf : IsPlusOmega (e ‘ (ordinalAdd θ ω)) (e ‘ θ) := by
    have h := (he.bounded_defined_iff plusOmegaFormula_bounded (fun v ↦ IsPlusOmega (v 0) (v 1))
      ![ordinalAdd θ ω, θ] (by simp [Fin.forall_fin_succ, hV _ hθρ, hV _ hθρ'])).mp ⟨hθ, rfl⟩
    simpa using h
  have heδ : IsOrdinal (e ‘ δ) := he.value_ordinal (IsOrdinal.of_mem hδρ) (hV δ hδρ)
  have hρeδ : ρ ∈ e ‘ δ := heδ.toIsTransitive.mem_trans hρμ hμeδ
  have heδθ : e ‘ δ ∈ e ‘ θ := (he.value_mem_iff (hV δ hδρ) (hV θ hθρ')).mpr hδθ
  have hebuf : e ‘ (ordinalAdd θ ω) ∈ e ‘ ρ := (he.value_mem_iff (hV _ hθρ) hρV).mpr hθρ
  have hspec : CriticalPointGraphSpec (hierarchy ρ) (e ↾ (hierarchy ρ)) δ :=
    (criticalPoint_iff_graphSpec hr.function).mp hcr
  have hpδ := hJpair δ (ordinal_subset_hierarchy ρ δ hδρ)
  have hpθ := hJpair θ (ordinal_subset_hierarchy ρ θ hθρ')
  have hpα := hJpair α (ordinal_subset_hierarchy ρ α hαρ)
  have hpx := hJpair x hx
  have hρord : IsOrdinal ρ := hρ.ordinal
  -- the matrix holds in `V` at the image tuple
  have hmat : ReflectionMatrix c D
      ![η, e ‘ δ, e ‘ θ, e ‘ ρ, e ‘ α, e ‘ x, δ, θ, ρ, α, x, hierarchy ρ, hierarchy (e ‘ ρ),
        e ↾ (hierarchy ρ)] :=
    ⟨hηδ, hδθ, ⟨ordinalAdd θ ω, hθρ, hθ, rfl⟩, hρeδ, heδθ, ⟨e ‘ (ordinalAdd θ ω), hebuf, hbuf⟩, hαθ,
      ⟨hρord, rfl⟩, hx, ⟨hvh.1, rfl⟩, hr, hspec, hpδ, hpθ, hpα, hpx, hρ, hDtrue⟩
  have himage : Reflects c D ![η, e ‘ δ, e ‘ θ, e ‘ ρ, e ‘ α, e ‘ x] :=
    ⟨δ, θ, ρ, α, x, hierarchy ρ, hierarchy (e ‘ ρ), e ↾ (hierarchy ρ), hmat⟩
  -- pull back along `e` using Σ_{c+1} ⊆ Σ_{k+1} absoluteness of both stages
  have hηV : η ∈ hierarchy μ := hV η (IsOrdinal.toIsTransitive.mem_trans hηδ hδρ)
  have htransfer := rankEmbedding_defined_iff hμ hν he
    hF (Reflects c D) ![η, δ, θ, ρ, α, x]
    (by simp [Fin.forall_fin_succ, hηV, hV δ hδρ, hV θ hθρ', hρV, hV α hαρ, hxV])
  apply htransfer.mpr
  have hη : e ‘ η = η := hcrit.fixed_below hηδ
  have hvec : (fun i ↦ e ‘ ((![η, δ, θ, ρ, α, x] : Fin 6 → V) i)) =
      ![η, e ‘ δ, e ‘ θ, e ‘ ρ, e ‘ α, e ‘ x] := by
    simp [funext_iff, Fin.forall_fin_succ, hη]
  rw [hvec]
  exact himage

theorem finite_reflection {c k : ℕ} (D : List (SetTheorySemisentence 6)) (hc : 2 ≤ c)
    (hD : listBound D ≤ c) (hck : c ≤ k) {η δ θ ρ α x : V}
    (hδ : IsCnExtendible (k + 1) δ) (hρ : Cn c ρ)
    (hηδ : η ∈ δ) (hδθ : δ ∈ θ) (hθρ : ordinalAdd θ (ω : V) ∈ ρ) (hαθ : α ∈ θ)
    (hx : x ∈ hierarchy ρ) (hDtrue : ∀ e ∈ D, e.Evalb ![η, δ, θ, ρ, α, x]) :
    Reflects c D ![η, δ, θ, ρ, α, x] :=
  finite_reflection_of_complexity D ((reflectionFormula_sigma hc D hD).mono (by omega))
    hδ hρ hηδ hδθ hθρ hαθ hx hDtrue

end ZFVP
