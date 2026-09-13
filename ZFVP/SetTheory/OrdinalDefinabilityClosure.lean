import ZFVP.SetTheory.OrdinalDefinability
import ZFVP.SetTheory.FormulaReflection
import ZFVP.Syntax.PackFiniteParameters
import ZFVP.Syntax.CloseParameters

/-! Closure of ordinal definability: a set defined in `V` by a parameter-free formula from
ordinal definable parameters is ordinal definable. The parameters are unwound into one parameter
tree and the resulting definition is reflected to a stage `V_δ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem setDomain_vals_two {A z P : V} (hz : z ∈ A) (hP : P ∈ A) :
    (fun i ↦ ((![⟨z, hz⟩, ⟨P, hP⟩] : Fin 2 → SetDomain A) i).val) = ![z, P] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i

theorem exists_reflecting_stage (Ψ : SetTheorySemisentence 2) (X : V) :
    ∃ δ : V, IsOrdinal δ ∧ X ∈ hierarchy δ ∧ IsFormulaAbsoluteAt Ψ δ := by
  obtain ⟨δ, hδ, hX, -, -, hΦ⟩ := finite_formula_reflection_containing [⟨2, Ψ⟩] X
  exact ⟨δ, hδ, hX, hΦ ⟨2, Ψ⟩ (List.mem_singleton.mpr rfl)⟩

/-- The unwinding of two ordinal definable parameters and a parameter tree into one tree
`⟨α₁, ⟨φ₁, ⟨P₁, ⟨α₂, ⟨φ₂, ⟨P₂, P⟩⟩⟩⟩⟩⟩`. -/
def unwindTwoFormula (Ψ : SetTheorySemisentence 4) : SetTheorySemisentence 2 :=
  f“y T. ∃ q₁ q₂ P,
    q₁ = !decodeFormula (!kpair.π₁.dfn T) (!kpair.π₁.dfn (!kpair.π₂.dfn T))
      (!kpair.π₁.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn T))) ∧
    q₂ = !decodeFormula (!kpair.π₁.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn T))))
      (!kpair.π₁.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn T)))))
      (!kpair.π₁.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn T)))))) ∧
    P = !kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn T))))) ∧
    !Ψ y q₁ q₂ P”

theorem eval_unwindTwoFormula (Ψ : SetTheorySemisentence 4) (y T : V) :
    (unwindTwoFormula Ψ).Evalb ![y, T] ↔
      Ψ.Evalb ![y, decode (kpair.π₁ T) (kpair.π₁ (kpair.π₂ T)) (kpair.π₁ (kpair.π₂ (kpair.π₂ T))),
        decode (kpair.π₁ (kpair.π₂ (kpair.π₂ (kpair.π₂ T))))
          (kpair.π₁ (kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ T)))))
          (kpair.π₁ (kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ T)))))),
        kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ T)))))] := by
  simp [unwindTwoFormula]

/-- The membership relation of the tuple `assignmentPrepend`, as a formula in the tuple of the
remaining entries and the first entry. -/
def prependFormula : SetTheorySemisentence 4 :=
  f“q t x P. q = !kpair.dfn (!isEmpty) x ∨
    ∃ r ∈ t, q = !kpair.dfn (!succ.dfn (!kpair.π₁.dfn r)) (!kpair.π₂.dfn r)”

theorem eval_prependFormula (q t x P : V) :
    prependFormula.Evalb ![q, t, x, P] ↔
      q = ⟨∅, x⟩ₖ ∨ ∃ r ∈ t, q = ⟨succ (kpair.π₁ r), kpair.π₂ r⟩ₖ := by
  simp [prependFormula]

def packedFormula {k : ℕ} (Ψ : SetTheorySemisentence (k + 1)) : SetTheorySemisentence 4 :=
  f“y t x P. !(packFiniteParameters Ψ) y t”

theorem eval_packedFormula {k : ℕ} (Ψ : SetTheorySemisentence (k + 1)) (y t x P : V) :
    (packedFormula Ψ).Evalb ![y, t, x, P] ↔ (packFiniteParameters Ψ).Evalb ![y, t] := by
  simp [packedFormula]

section

variable (Pf : SetTheorySemisentence 2)

/-- Sets defined over a stage by an external formula with a parameter tree are ordinal
definable. -/
theorem isOD_of_stage {α P p b : V} (hα : IsOrdinal α) (hP : IsParameterTree Pf P p)
    (hPα : P ∈ hierarchy α) (ψ : SetTheorySemisentence 2)
    (hb : ∀ z, z ∈ b ↔ ∃ hz : z ∈ hierarchy α,
      Semiformula.Evalb (M := SetDomain (hierarchy α)) ![⟨z, hz⟩, ⟨P, hPα⟩] ψ) :
    IsOD Pf b p := by
  have hne : IsNonempty (hierarchy α) := ⟨⟨P, hPα⟩⟩
  refine ⟨α, encodeMembershipFormula ψ, P, hα,
    (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem ψ), hP, hPα, ?_⟩
  apply mem_ext
  intro z
  rw [hb z, mem_decode_iff]
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, ?_⟩
    have := (membershipSatisfies_encode hne ψ ![⟨z, hz⟩, ⟨P, hPα⟩]).mpr h
    rwa [setDomain_vals_two] at this
  · rintro ⟨hz, h⟩
    refine ⟨hz, ?_⟩
    apply (membershipSatisfies_encode hne ψ ![⟨z, hz⟩, ⟨P, hPα⟩]).mp
    rwa [setDomain_vals_two]

theorem isAllowed_empty (p : V) : IsAllowed Pf (∅ : V) p :=
  Or.inl (IsOrdinal.of_mem (empty_mem_ω : (∅ : V) ∈ ω))

/-- Allowed parameters are ordinal definable. -/
theorem isOD_of_allowed {x p : V} (h : IsAllowed Pf x p) : IsOD Pf x p := by
  obtain ⟨α, hα, hxα⟩ := hierarchy_bound_exists x
  have : IsOrdinal α := hα
  have hx : x ∈ hierarchy (succ α) := by
    rw [hierarchy_succ]
    exact mem_power_iff.mpr hxα
  have htr := hierarchy_transitive (succ α)
  refine isOD_of_stage Pf inferInstance (isParameterTree_of_allowed Pf h) hx “z P. z ∈ P” ?_
  intro z
  constructor
  · intro hz
    exact ⟨htr.mem_trans hz hx, hz⟩
  · rintro ⟨hz, h⟩
    exact h

theorem isOD_empty (p : V) : IsOD Pf (∅ : V) p := isOD_of_allowed Pf (isAllowed_empty Pf p)

/-- Closure under definitions from two ordinal definable parameters and a parameter tree. -/
theorem isOD_of_two (Ψ : SetTheorySemisentence 4) {q₁ q₂ P b p : V}
    (h₁ : IsOD Pf q₁ p) (h₂ : IsOD Pf q₂ p) (hP : IsParameterTree Pf P p)
    (hb : ∀ y, y ∈ b ↔ Ψ.Evalb ![y, q₁, q₂, P]) : IsOD Pf b p := by
  obtain ⟨α₁, φ₁, P₁, hα₁, hφ₁, hP₁, -, rfl⟩ := h₁
  obtain ⟨α₂, φ₂, P₂, hα₂, hφ₂, hP₂, -, rfl⟩ := h₂
  let T : V := ⟨α₁, ⟨φ₁, ⟨P₁, ⟨α₂, ⟨φ₂, ⟨P₂, P⟩ₖ⟩ₖ⟩ₖ⟩ₖ⟩ₖ⟩ₖ
  have hT : IsParameterTree Pf T p := by
    apply isParameterTree_kpair Pf (isParameterTree_of_allowed Pf (Or.inl hα₁))
    apply isParameterTree_kpair Pf (isParameterTree_of_allowed Pf (Or.inr (Or.inl hφ₁)))
    apply isParameterTree_kpair Pf hP₁
    apply isParameterTree_kpair Pf (isParameterTree_of_allowed Pf (Or.inl hα₂))
    apply isParameterTree_kpair Pf (isParameterTree_of_allowed Pf (Or.inr (Or.inl hφ₂)))
    exact isParameterTree_kpair Pf hP₂ hP
  have heval : ∀ y, (unwindTwoFormula Ψ).Evalb ![y, T] ↔
      Ψ.Evalb ![y, decode α₁ φ₁ P₁, decode α₂ φ₂ P₂, P] := by
    intro y
    rw [eval_unwindTwoFormula]
    simp only [T, kpair.π₁_kpair, kpair.π₂_kpair]
  obtain ⟨δ, hδ, hX, habs⟩ := exists_reflecting_stage (unwindTwoFormula Ψ) (insert b ({T} : V))
  have : IsOrdinal δ := hδ
  have htr := hierarchy_transitive δ
  have hbδ : b ∈ hierarchy δ := htr.mem_trans (mem_insert.mpr (Or.inl rfl)) hX
  have hTδ : T ∈ hierarchy δ :=
    htr.mem_trans (mem_insert.mpr (Or.inr (mem_singleton_iff.mpr rfl))) hX
  refine isOD_of_stage Pf hδ hT hTδ (unwindTwoFormula Ψ) ?_
  intro z
  constructor
  · intro hz
    refine ⟨htr.mem_trans hz hbδ, ?_⟩
    rw [habs, setDomain_vals_two, heval]
    exact (hb z).mp hz
  · rintro ⟨hz, h⟩
    rw [habs, setDomain_vals_two, heval] at h
    exact (hb z).mpr h

/-- Tuples of ordinal definable sets are ordinal definable. -/
theorem isOD_standardTuple {p : V} : ∀ {k : ℕ} (v : Fin k → V), (∀ i, IsOD Pf (v i) p) →
    IsOD Pf (standardTuple v) p
  | 0, _, _ => by simpa [standardTuple] using isOD_empty Pf p
  | k + 1, v, hv => by
    have htail := isOD_standardTuple (fun i ↦ v i.succ) (fun i ↦ hv i.succ)
    refine isOD_of_two Pf prependFormula htail (hv 0)
      (isParameterTree_of_allowed Pf (isAllowed_empty Pf p)) ?_
    intro q
    rw [eval_prependFormula, mem_standardTuple_iff]
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact Or.inl rfl
      · refine Or.inr ⟨⟨(j.val : V), v j.succ⟩ₖ, (mem_standardTuple_iff _ _).mpr ⟨j, rfl⟩, ?_⟩
        rw [kpair.π₁_kpair, kpair.π₂_kpair]
        rfl
    · rintro (rfl | ⟨r, hr, rfl⟩)
      · exact ⟨0, rfl⟩
      · obtain ⟨j, rfl⟩ := (mem_standardTuple_iff _ _).mp hr
        refine ⟨j.succ, ?_⟩
        rw [kpair.π₁_kpair, kpair.π₂_kpair]
        rfl

/-- Closure under definitions from finitely many ordinal definable parameters. -/
theorem isOD_of_definable_cons {k : ℕ} (Ψ : SetTheorySemisentence (k + 1)) {q : Fin k → V}
    {b p : V} (hq : ∀ i, IsOD Pf (q i) p) (hb : ∀ y, y ∈ b ↔ Ψ.Evalb (y :> q)) : IsOD Pf b p := by
  refine isOD_of_two Pf (packedFormula Ψ) (isOD_standardTuple Pf q hq) (isOD_empty Pf p)
    (isParameterTree_of_allowed Pf (isAllowed_empty Pf p)) ?_
  intro y
  rw [eval_packedFormula, eval_packFiniteParameters_standardTuple]
  exact hb y

omit [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem append_cast_eq {k : ℕ} (y : V) (q : Fin k → V) :
    (fun i : Fin (1 + k) ↦ (y :> q) (Fin.cast (Nat.add_comm 1 k) i)) = Fin.append ![y] q := by
  funext i
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
  · rw [Fin.append_left]
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    rfl
  · rw [Fin.append_right]
    have hc : Fin.cast (Nat.add_comm 1 k) (Fin.natAdd 1 j) = j.succ := Fin.ext (by simp)
    rw [hc, Matrix.cons_val_succ]

theorem isOD_of_definable_append {k : ℕ} (Ψ : SetTheorySemisentence (1 + k)) {q : Fin k → V}
    {b p : V} (hq : ∀ i, IsOD Pf (q i) p) (hb : ∀ y, y ∈ b ↔ Ψ.Evalb (Fin.append ![y] q)) :
    IsOD Pf b p := by
  let Ψ' : SetTheorySemisentence (k + 1) :=
    Rew.embSubsts (fun i : Fin (1 + k) ↦ Semiterm.bvar (Fin.cast (Nat.add_comm 1 k) i)) ▹ Ψ
  refine isOD_of_definable_cons Pf Ψ' hq ?_
  intro y
  rw [hb y]
  show Ψ.Evalb (Fin.append ![y] q) ↔ Semiformula.Evalb (y :> q) Ψ'
  simp only [Ψ', Semiformula.Evalb, Semiformula.eval_embSubsts, Function.comp_def, Semiterm.val_bvar]
  rw [append_cast_eq]

/-- Sets defined in `V` from ordinal definable class parameters are ordinal definable. -/
theorem isOD_of_classParameters (Φ : SetTheorySemiformula (Option ℕ) 1) (E : Option ℕ → V)
    {b p : V} (hE : ∀ o, IsOD Pf (E o) p) (hb : ∀ y, y ∈ b ↔ Φ.Eval ![y] E) : IsOD Pf b p := by
  let g : Option ℕ → ℕ := fun o ↦ o.elim 0 Nat.succ
  let E₁ : ℕ → V := fun j ↦ Nat.rec (E none) (fun j' _ ↦ E (some j')) j
  have hE₁ : ∀ j, IsOD Pf (E₁ j) p := fun j ↦ by cases j <;> exact hE _
  have hcomp : (fun o ↦ E₁ (g o)) = E := by
    funext o
    cases o <;> rfl
  let Φ₁ : SetTheorySemiproposition 1 := Rew.rewriteMap g ▹ Φ
  have h1 : ∀ y, Φ₁.Eval ![y] E₁ ↔ Φ.Eval ![y] E := by
    intro y
    simp only [Φ₁, Semiformula.eval_rewriteMap]
    rw [hcomp]
  refine isOD_of_definable_append Pf (closeParameters Φ₁) (q := fun i : Fin Φ₁.fvSup ↦ E₁ i.val)
    (fun i ↦ hE₁ _) ?_
  intro y
  rw [hb y, ← h1 y]
  exact (eval_closeParameters Φ₁ ![y] E₁).symm

end

end ZFVP
