import ZFVP.ModelTheory.FiniteRestorationReflection
import ZFVP.SetTheory.FiniteRestorationLevel
import ZFVP.SetTheory.ChoicelessCorrectness
import ZFVP.SetTheory.CnExtendibleDownward
import ZFVP.SetTheory.CnAbsoluteness
import ZFVP.SetTheory.BoundedOrdinalOmega

/-! The ground-model half of Theorem thm:finite-restoration.

Everything here happens in `V`, before Woodin's forcing is applied: an `E_{t_N}`-cardinal `Λ` is
supercompact in Woodin's sense and lies in `C^(t_N+2)`, the `E_{s_N}`-cardinals and `C^(c_N)` are
unbounded below `Λ`, the two concrete clauses of the stage dictionary `Xi_N` hold at every
`E_{s_N}`-cardinal, and lem:finite-reflection applies to `Xi_N`.  The last theorem packages the
paragraph "Fix eta < Lambda above mu, choose an `E_{s_N}`-cardinal delta > eta ..." into the single
statement the forcing side of the proof consumes.

No forcing appears in this file. -/

set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {N : ℕ} {Q : List (SetTheorySemisentence 6)}

/-- Downward monotonicity of `E_s` in the level, stated without the successor pattern. -/
private theorem cnExtendible_mono {a b : ℕ} {κ : V} (h : IsCnExtendible a κ) (hb : 1 ≤ b)
    (hba : b ≤ a) : IsCnExtendible b κ := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  exact h.of_le (by omega)

private theorem one_le_woodinSupercompactBound : 1 ≤ woodinSupercompactBound :=
  Nat.succ_le_succ (Nat.zero_le _)

/-- Arithmetic helpers.  They are stated for abstract naturals on purpose: `omega` inspects the
head of every atom, and the level definitions of this proof unfold into large formula recursions. -/
private theorem exists_pred {a : ℕ} (h : 1 ≤ a) : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩

private theorem one_le_of_add_two_le {a b : ℕ} (h : a + 2 ≤ b) : 1 ≤ b := by omega

private theorem one_le_of_four_le {a : ℕ} (h : 4 ≤ a) : 1 ≤ a := by omega

private theorem le_add_three {a b c : ℕ} (h : a ≤ b) (hb : b = c + 1) : a ≤ c + 3 := by omega

-- The level definitions of thm:finite-restoration unfold into the recursions that compute Levy
-- bounds from formula codes.  Nothing below needs their values, only the inequalities exported by
-- `ZFVP.SetTheory.FiniteRestorationLevel`, so they are sealed here: otherwise unification loops
-- inside those recursions.
attribute [local irreducible] woodinWindowLevel finiteRestorationReflectionLevel
  finiteRestorationWitnessLevel finiteRestorationLevel

/-- A `Σ_1`-correct rank stage is closed under `θ ↦ θ + ω`.  The graph of that map is bounded, so
the closure comes from the bounded witness property of a correct rank stage. -/
theorem Cn.ordinalAdd_omega_mem {k : ℕ} {Λ θ : V} (hΛ : Cn (k + 1) Λ) (hθ : θ ∈ Λ) :
    ordinalAdd θ (ω : V) ∈ Λ := by
  let := hΛ.ordinal
  let : IsOrdinal θ := IsOrdinal.of_mem hθ
  let := hierarchy_transitive (V := V) Λ
  have hθV : θ ∈ hierarchy Λ := ordinal_subset_hierarchy Λ θ hθ
  have hex : ∃ x : V, boundedOrdinalOmegaFormula.Evalb (x :> ![θ]) :=
    ⟨ordinalAdd θ (ω : V), (eval_boundedOrdinalOmegaFormula _ _).mpr ⟨inferInstance, rfl⟩⟩
  obtain ⟨x, hx, hev⟩ := hΛ.2.bounded_witness boundedOrdinalOmegaFormula_bounded ![θ]
    (fun i ↦ by
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      simpa using hθV) hex
  obtain ⟨-, rfl⟩ := (eval_boundedOrdinalOmegaFormula _ _).mp hev
  exact ordinal_mem_hierarchy_iff.mp hx

/-- An `E_{t_N}`-cardinal is supercompact in Woodin's sense (lem:ordinary-correct-supercompact). -/
theorem isWoodinSupercompact_of_finiteRestorationLevel {Λ : V}
    (hΛ : IsCnExtendible (finiteRestorationLevel N Q) Λ) : IsWoodinSupercompact Λ := by
  refine IsCnExtendible.woodinSupercompact (cnExtendible_mono hΛ one_le_woodinSupercompactBound ?_)
  exact Nat.le_trans woodinSupercompactBound_le_witnessLevel
    (Nat.le_trans (Nat.le_add_right _ 4) witnessLevel_add_four_le_finiteRestorationLevel)

/-- An `E_{t_N}`-cardinal lies in `C^(t_N+2)` (Mohammd, Proposition 2.2). -/
theorem cn_of_finiteRestorationLevel {Λ : V}
    (hΛ : IsCnExtendible (finiteRestorationLevel N Q) Λ) :
    Cn (finiteRestorationLevel N Q + 2) Λ := by
  obtain ⟨m, hm⟩ := exists_pred (one_le_of_four_le four_le_finiteRestorationLevel)
  rw [hm] at hΛ ⊢
  simpa only [show m + 1 + 2 = m + 3 from rfl] using hΛ.cn

/-- The `E_{s_N}`-cardinals are unbounded below `Λ`. -/
theorem exists_witnessLevel_cnExtendible_below {Λ η : V}
    (hΛ : IsCnExtendible (finiteRestorationLevel N Q) Λ)
    (hUE : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsCnExtendible (finiteRestorationWitnessLevel N Q) κ)
    (hη : η ∈ Λ) :
    ∃ δ : V, δ ∈ Λ ∧ η ∈ δ ∧ IsCnExtendible (finiteRestorationWitnessLevel N Q) δ := by
  obtain ⟨k, hk⟩ := exists_pred (one_le_of_four_le four_le_finiteRestorationLevel)
  have hcn : Cn (k + 1) Λ :=
    (cn_of_finiteRestorationLevel hΛ).of_le (by rw [hk]; exact Nat.le_add_right _ 2)
  have hs : IsSigmaFormula (k + 1) (cnExtendibleFormula (finiteRestorationWitnessLevel N Q)) := by
    rw [← hk]; exact cnExtendibleFormula_sigma_finiteRestorationLevel
  exact exists_cnExtendible_mem_of_cn hcn hs hUE hη

/-- `C^(c_N)` is unbounded below `Λ`. -/
theorem exists_reflectionLevel_cn_below {Λ η : V}
    (hΛ : IsCnExtendible (finiteRestorationLevel N Q) Λ) (hη : η ∈ Λ) :
    ∃ ρ : V, ρ ∈ Λ ∧ η ∈ ρ ∧ Cn (finiteRestorationReflectionLevel N Q) ρ := by
  obtain ⟨k, hk⟩ := exists_pred (one_le_of_four_le four_le_finiteRestorationLevel)
  have hcn : Cn (k + 1) Λ :=
    (cn_of_finiteRestorationLevel hΛ).of_le (by rw [hk]; exact Nat.le_add_right _ 2)
  have hc : IsSigmaFormula (k + 1) (cnFormula (finiteRestorationReflectionLevel N Q)) := by
    rw [← hk]; exact cnFormula_sigma_finiteRestorationLevel
  exact exists_cn_mem_of_cn hcn hc hη

/-- An `E_{s_N}`-cardinal lies in `C^(r_{N+1})`, the first clause of `Xi_N`. -/
theorem cn_woodinWindowLevel_of_witnessLevel {θ : V}
    (hθ : IsCnExtendible (finiteRestorationWitnessLevel N Q) θ) : Cn (woodinWindowLevel N) θ := by
  obtain ⟨m, hm⟩ := exists_pred (one_le_of_add_two_le
    (reflectionLevel_add_two_le_witnessLevel (N := N) (Q := Q)))
  rw [hm] at hθ
  exact hθ.cn.of_le (le_add_three (woodinWindowLevel_le_witnessLevel (N := N) (Q := Q)) hm)

/-- An `E_{s_N}`-cardinal is supercompact in Woodin's sense, the second clause of `Xi_N`. -/
theorem isWoodinSupercompact_of_witnessLevel {θ : V}
    (hθ : IsCnExtendible (finiteRestorationWitnessLevel N Q) θ) : IsWoodinSupercompact θ :=
  IsCnExtendible.woodinSupercompact
    (cnExtendible_mono hθ one_le_woodinSupercompactBound woodinSupercompactBound_le_witnessLevel)

/-- The two clauses of `Xi_N` that the codebase can state hold at any `E_{s_N}`-cardinal `θ`:
`θ` lies in `C^(r)` and `θ` is supercompact in Woodin's sense. -/
theorem woodinStageDictionary_concrete_clauses {θ : V}
    (hθ : IsCnExtendible (finiteRestorationWitnessLevel N Q) θ) (η δ ρ α x : V) :
    ∀ e ∈ woodinStageDictionary N ([] : List (SetTheorySemisentence 6)),
      e.Evalb ![η, δ, θ, ρ, α, x] := by
  intro e he
  simp only [woodinStageDictionary, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · have : Cn (woodinWindowLevel N) θ := cn_woodinWindowLevel_of_witnessLevel hθ
    simpa [Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton, eval_cnFormula] using this
  · have heval : woodinSupercompactFormula.Evalb (![θ] : Fin 1 → V) :=
      ((woodinSupercompactFormula_defined (V := V)).iff ![θ]).mpr
        (isWoodinSupercompact_of_witnessLevel hθ)
    simpa [Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton] using heval

/-- The paper's application of lem:finite-reflection to `Xi_N`. -/
theorem reflects_woodinStageDictionary {η δ θ ρ α x : V}
    (hδ : IsCnExtendible (finiteRestorationWitnessLevel N Q) δ)
    (hθ : IsCnExtendible (finiteRestorationWitnessLevel N Q) θ)
    (hρ : Cn (finiteRestorationReflectionLevel N Q) ρ)
    (hηδ : η ∈ δ) (hδθ : δ ∈ θ) (hθρ : ordinalAdd θ (ω : V) ∈ ρ) (hαθ : α ∈ θ)
    (hx : x ∈ hierarchy ρ) (hQ : ∀ e ∈ Q, e.Evalb ![η, δ, θ, ρ, α, x]) :
    Reflects (finiteRestorationReflectionLevel N Q) (woodinStageDictionary N Q)
      ![η, δ, θ, ρ, α, x] := by
  obtain ⟨k, hk, hck⟩ := exists_reflection_predecessor (N := N) (Q := Q)
  rw [hk] at hδ
  refine finite_reflection (woodinStageDictionary N Q) two_le_finiteRestorationReflectionLevel
    listBound_le_finiteRestorationReflectionLevel hck hδ hρ hηδ hδθ hθρ hαθ hx ?_
  intro e he
  simp only [woodinStageDictionary, List.mem_cons] at he
  rcases he with rfl | rfl | he
  · have : Cn (woodinWindowLevel N) θ := cn_woodinWindowLevel_of_witnessLevel hθ
    simpa [Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton, eval_cnFormula] using this
  · have heval : woodinSupercompactFormula.Evalb (![θ] : Fin 1 → V) :=
      ((woodinSupercompactFormula_defined (V := V)).iff ![θ]).mpr
        (isWoodinSupercompact_of_witnessLevel hθ)
    simpa [Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton] using heval
  · exact hQ e he

/-- The paper's paragraph "Fix eta < Lambda above mu, choose an `E_{s_N}`-cardinal delta > eta ...".
`hQ` is the W02 obligation: the code of `Q_θ` with its order and restriction maps lies in `V_ρ` and
satisfies the clause list `Q`. -/
theorem exists_reflected_stage {Λ η : V}
    (hΛ : IsCnExtendible (finiteRestorationLevel N Q) Λ)
    (hUE : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsCnExtendible (finiteRestorationWitnessLevel N Q) κ)
    (hQ : ∀ θ ρ : V, IsCnExtendible (finiteRestorationWitnessLevel N Q) θ →
      Cn (finiteRestorationReflectionLevel N Q) ρ → ordinalAdd θ (ω : V) ∈ ρ →
      ∃ x : V, x ∈ hierarchy ρ ∧ ∀ (a b c : V), ∀ e ∈ Q, e.Evalb ![a, b, θ, ρ, c, x])
    (hη : η ∈ Λ) :
    ∃ δ : V, δ ∈ Λ ∧ η ∈ δ ∧ IsCnExtendible (finiteRestorationWitnessLevel N Q) δ ∧
      ∀ θ : V, θ ∈ Λ → δ ∈ θ → IsCnExtendible (finiteRestorationWitnessLevel N Q) θ →
        ∀ α ∈ θ, ∃ ρ x : V, ρ ∈ Λ ∧ x ∈ hierarchy ρ ∧
          Reflects (finiteRestorationReflectionLevel N Q) (woodinStageDictionary N Q)
            ![η, δ, θ, ρ, α, x] := by
  obtain ⟨δ, hδΛ, hηδ, hδE⟩ := exists_witnessLevel_cnExtendible_below hΛ hUE hη
  refine ⟨δ, hδΛ, hηδ, hδE, ?_⟩
  intro θ hθΛ hδθ hθE α hαθ
  have hΛcn : Cn (finiteRestorationLevel N Q + 1 + 1) Λ := cn_of_finiteRestorationLevel hΛ
  have hbuf : ordinalAdd θ (ω : V) ∈ Λ := hΛcn.ordinalAdd_omega_mem hθΛ
  obtain ⟨ρ, hρΛ, hθρ, hρ⟩ := exists_reflectionLevel_cn_below hΛ hbuf
  obtain ⟨x, hx, hxQ⟩ := hQ θ ρ hθE hρ hθρ
  exact ⟨ρ, x, hρΛ, hx,
    reflects_woodinStageDictionary hδE hθE hρ hηδ hδθ hθρ hαθ hx (hxQ η δ α)⟩

end ZFVP
