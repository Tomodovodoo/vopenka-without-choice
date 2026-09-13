import ZFVP.SetTheory.FiniteDictionaryReflection
import ZFVP.SetTheory.CnExtendibleWoodinSupercompact
import ZFVP.ModelTheory.UniformForcingDefinitions

/-! The integer `t_N` of Theorem thm:finite-restoration.

This file is the first paragraph of that proof and nothing else: it fixes the window level
`r_{N+1}`, the stage dictionary `Xi_N`, the two complexity bounds `c_N` and `s_N`, and the level
`t_N` itself, together with the four Levy certificates that the rest of the proof uses.  There is
no ZF model here beyond the one evaluation lemma at the end; everything else is arithmetic on
natural numbers and on formula codes.

For a fixed clause list `Q` the function `N ↦ finiteRestorationLevel N Q` is built by explicit
primitive recursion on formula codes: `uniformForcingLevelBound`, `levySyntacticBound` and
`listBound` all recurse on the syntax of the formulas involved, and the remaining steps are
`max` and `+ 4`.  Every definition below is a plain computable definition; the only opaque
ingredient is the existing package `woodinSupercompactBound`, which is a fixed constant and does
not depend on `N`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The paper's `r_{N+1}`: a Levy level at which the forcing relation for codes of level `N+1`
is defined for both polarities. -/
def woodinWindowLevel (N : ℕ) : ℕ :=
  max (uniformForcingLevelBound .sigma (N + 1)) (uniformForcingLevelBound .pi (N + 1))

/-- The paper's `Xi_N`, in the six variables `η δ θ ρ α x` used by the dictionaries of
lem:finite-reflection (variable `2` is `θ`, variable `5` is `x`).  The first clause says that the
stage `θ` lies in `C^(r)` for `r = r_{N+1}`, the second says that `θ` is supercompact in Woodin's
sense.  The remaining clauses, saying that `x` codes `Q_θ` with its order and restriction maps,
are the parameter `Q`: they are a named hypothesis here, whose source is the definability of the
Woodin endpoint poset proved elsewhere (node W02).  No formula for that poset is fixed in this
file. -/
def woodinStageDictionary (N : ℕ) (Q : List (SetTheorySemisentence 6)) :
    List (SetTheorySemisentence 6) :=
  “η δ θ ρ α x. !(cnFormula (woodinWindowLevel N)) θ” ::
    “η δ θ ρ α x. !woodinSupercompactFormula θ” :: Q

/-- The paper's `c_N`: a reflection level legal for `lem:finite-reflection` applied to
`Xi_N`, that is, at least `2` and at least the syntactic bound of every clause. -/
def finiteRestorationReflectionLevel (N : ℕ) (Q : List (SetTheorySemisentence 6)) : ℕ :=
  max 2 (listBound (woodinStageDictionary N Q))

/-- The paper's `s_N = max {r, d_W, s_D(Xi_N)}` with `s_D(Xi_N) = c_N + 2`, the level that
`lem:finite-reflection` asks for.  The `+ 2` is what makes the witness level a successor `k + 1`
with `c_N ≤ k`, the shape `finite_reflection` takes. -/
def finiteRestorationWitnessLevel (N : ℕ) (Q : List (SetTheorySemisentence 6)) : ℕ :=
  max (max (woodinWindowLevel N) woodinSupercompactBound)
    (finiteRestorationReflectionLevel N Q + 2)

/-- Every ordinal is below some member of `C^(c)`. -/
def cnUnboundedSentence (c : ℕ) : SetTheorySentence :=
  “∀ α, !IsOrdinal.dfn α → ∃ ρ, α ∈ ρ ∧ !(cnFormula c) ρ”

/-- The paper's `t_N`: four more than the maximum of `s_N` and the Levy complexities of
`E_{s_N}(ξ)`, of the assertion that the `E_{s_N}`-cardinals are unbounded, of membership in
`C^(c_N)`, and of the assertion that `C^(c_N)` is unbounded. -/
def finiteRestorationLevel (N : ℕ) (Q : List (SetTheorySemisentence 6)) : ℕ :=
  4 + max (finiteRestorationWitnessLevel N Q)
    (max (levySyntacticBound (cnExtendibleFormula (finiteRestorationWitnessLevel N Q)))
      (max (levySyntacticBound (unboundedExtendibilitySentence (finiteRestorationWitnessLevel N Q)))
        (max (levySyntacticBound (cnFormula (finiteRestorationReflectionLevel N Q)))
          (levySyntacticBound (cnUnboundedSentence (finiteRestorationReflectionLevel N Q))))))

variable {N : ℕ} {Q : List (SetTheorySemisentence 6)}

theorem two_le_finiteRestorationReflectionLevel : 2 ≤ finiteRestorationReflectionLevel N Q :=
  Nat.le_max_left _ _

theorem listBound_le_finiteRestorationReflectionLevel :
    listBound (woodinStageDictionary N Q) ≤ finiteRestorationReflectionLevel N Q :=
  Nat.le_max_right _ _

theorem finiteRestorationReflectionLevel_le_witnessLevel :
    finiteRestorationReflectionLevel N Q ≤ finiteRestorationWitnessLevel N Q := by
  have := Nat.le_max_right (max (woodinWindowLevel N) woodinSupercompactBound)
    (finiteRestorationReflectionLevel N Q + 2)
  unfold finiteRestorationWitnessLevel
  omega

theorem reflectionLevel_add_two_le_witnessLevel :
    finiteRestorationReflectionLevel N Q + 2 ≤ finiteRestorationWitnessLevel N Q :=
  Nat.le_max_right _ _

/-- The witness level is a successor, so it can be written as `k + 1` with `c ≤ k`, which is the
shape `finite_reflection` wants. -/
theorem exists_reflection_predecessor :
    ∃ k : ℕ, finiteRestorationWitnessLevel N Q = k + 1 ∧
      finiteRestorationReflectionLevel N Q ≤ k := by
  have h : finiteRestorationReflectionLevel N Q + 2 ≤ finiteRestorationWitnessLevel N Q :=
    reflectionLevel_add_two_le_witnessLevel
  exact ⟨finiteRestorationWitnessLevel N Q - 1, by omega, by omega⟩

theorem woodinWindowLevel_le_witnessLevel :
    woodinWindowLevel N ≤ finiteRestorationWitnessLevel N Q :=
  (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)

theorem woodinSupercompactBound_le_witnessLevel :
    woodinSupercompactBound ≤ finiteRestorationWitnessLevel N Q :=
  (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)

theorem witnessLevel_add_four_le_finiteRestorationLevel :
    finiteRestorationWitnessLevel N Q + 4 ≤ finiteRestorationLevel N Q := by
  unfold finiteRestorationLevel
  omega

theorem four_le_finiteRestorationLevel : 4 ≤ finiteRestorationLevel N Q := by
  unfold finiteRestorationLevel
  omega

theorem cnExtendibleFormula_sigma_finiteRestorationLevel :
    IsSigmaFormula (finiteRestorationLevel N Q)
      (cnExtendibleFormula (finiteRestorationWitnessLevel N Q)) :=
  (isLevyFormula_syntacticBound _ .sigma).mono (by unfold finiteRestorationLevel; omega)

theorem unboundedExtendibilitySentence_sigma_finiteRestorationLevel :
    IsSigmaFormula (finiteRestorationLevel N Q)
      (unboundedExtendibilitySentence (finiteRestorationWitnessLevel N Q)) :=
  (isLevyFormula_syntacticBound _ .sigma).mono (by unfold finiteRestorationLevel; omega)

theorem cnFormula_sigma_finiteRestorationLevel :
    IsSigmaFormula (finiteRestorationLevel N Q)
      (cnFormula (finiteRestorationReflectionLevel N Q)) :=
  (isLevyFormula_syntacticBound _ .sigma).mono (by unfold finiteRestorationLevel; omega)

theorem cnUnboundedSentence_sigma_finiteRestorationLevel :
    IsSigmaFormula (finiteRestorationLevel N Q)
      (cnUnboundedSentence (finiteRestorationReflectionLevel N Q)) :=
  (isLevyFormula_syntacticBound _ .sigma).mono (by unfold finiteRestorationLevel; omega)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_cnUnboundedSentence (c : ℕ) :
    V↓[ℒₛₑₜ] ⊧ cnUnboundedSentence c ↔
      ∀ α : V, IsOrdinal α → ∃ ρ : V, α ∈ ρ ∧ Cn c ρ := by
  change (cnUnboundedSentence c).Evalb (![] : Fin 0 → V) ↔ _
  simp [cnUnboundedSentence]

end ZFVP
