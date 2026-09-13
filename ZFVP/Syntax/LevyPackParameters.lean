import ZFVP.Syntax.PackFiniteParameters

/-! Packing finitely many parameters without raising a positive Levy level. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem finiteConjunction_levy {p k n m} (φ : Fin m → SetTheorySemisentence n)
    (hφ : ∀ i, IsLevyFormula p k (φ i)) : IsLevyFormula p k (finiteConjunction φ) := by
  induction m with
  | zero => exact .bounded .verum
  | succ m ih => exact .and (hφ 0) (ih _ (fun i ↦ hφ i.succ))

theorem IsLevyFormula.exsItr {k n m} {φ : SetTheorySemisentence (n + m)}
    (hφ : IsSigmaFormula (k + 1) φ) : IsSigmaFormula (k + 1) (∃¹^[m] φ) := by
  induction m with
  | zero => exact hφ
  | succ m ih =>
    rw [exsItr_succ]
    exact ih (.exs hφ)

theorem IsLevyFormula.allItr {k n m} {φ : SetTheorySemisentence (n + m)}
    (hφ : IsPiFormula (k + 1) φ) : IsPiFormula (k + 1) (∀¹^[m] φ) := by
  induction m with
  | zero => exact hφ
  | succ m ih =>
    rw [allItr_succ]
    exact ih (.all hφ)

def levyPackedEntryFormula (i : ℕ) : SetTheorySemisentence 2 :=
  “x p. ∃ j, !(boundedNumeralFormula i) j ∧ !boundedPairMemberFormula p j x”

def levyPackedEntries (n : ℕ) : SetTheorySemisentence (2 + n) :=
  finiteConjunction (fun i : Fin n ↦
    boundIndexRew ![i.addCast 2, (1 : Fin 2).addNat n] ▹ levyPackedEntryFormula i.val)

def levyPackedBody {n : ℕ} (pol : LevyPolarity) (φ : SetTheorySemisentence (n + 1)) :
    SetTheorySemisentence (2 + n) :=
  let ψ := boundIndexRew (Fin.cases ((0 : Fin 2).addNat n) (fun i : Fin n ↦ i.addCast 2)) ▹ φ
  match pol with
  | .sigma => (levyPackedEntries n).and ψ
  | .pi => (∼levyPackedEntries n).or ψ

def levyPackParameters {n : ℕ} (pol : LevyPolarity) (φ : SetTheorySemisentence (n + 1)) :
    SetTheorySemisentence 2 :=
  match pol with
  | .sigma => ∃¹^[n] levyPackedBody .sigma φ
  | .pi => ∀¹^[n] levyPackedBody .pi φ

theorem levyPackedEntryFormula_sigmaOne (i : ℕ) : IsSigmaFormula 1 (levyPackedEntryFormula i) :=
  .exs (.and (.bounded ((boundedNumeralFormula_bounded i).subst _))
    (.bounded (boundedPairMemberFormula_bounded.subst _)))

theorem levyPackedEntries_sigmaOne (n : ℕ) : IsSigmaFormula 1 (levyPackedEntries n) :=
  finiteConjunction_levy _ (fun i ↦ (levyPackedEntryFormula_sigmaOne i.val).rew _)

theorem levyPackedBody_levy {pol k n} {φ : SetTheorySemisentence (n + 1)}
    (hφ : IsLevyFormula pol k φ) (hk : 0 < k) : IsLevyFormula pol k (levyPackedBody pol φ) := by
  cases pol with
  | sigma => exact .and ((levyPackedEntries_sigmaOne n).mono hk) (hφ.rew _)
  | pi => exact .or ((levyPackedEntries_sigmaOne n).neg.mono hk) (hφ.rew _)

theorem levyPackParameters_levy {pol k n} {φ : SetTheorySemisentence (n + 1)}
    (hφ : IsLevyFormula pol k φ) (hk : 0 < k) : IsLevyFormula pol k (levyPackParameters pol φ) := by
  cases k with
  | zero => omega
  | succ k =>
    cases pol with
    | sigma => exact (levyPackedBody_levy hφ hk).exsItr
    | pi => exact (levyPackedBody_levy hφ hk).allItr

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_levyPackedEntryFormula (i : ℕ) (x p : V) :
    (levyPackedEntryFormula i).Evalb ![x, p] ↔ ⟨(i : V), x⟩ₖ ∈ p := by
  simp [levyPackedEntryFormula]

theorem eval_levyPackedEntries {n : ℕ} (e v : Fin n → V) (x : V) :
    (levyPackedEntries n).Evalb (Matrix.appendr e ![x, standardTuple v]) ↔ e = v := by
  rw [levyPackedEntries, eval_finiteConjunction]
  have he (i : Fin n) :
      ((boundIndexRew ![i.addCast 2, (1 : Fin 2).addNat n] ▹ levyPackedEntryFormula i.val).Evalb
        (Matrix.appendr e ![x, standardTuple v])) ↔ e i = v i := by
    rw [eval_boundIndexRew]
    have hv : Matrix.appendr e ![x, standardTuple v] ∘ ![i.addCast 2, (1 : Fin 2).addNat n] =
        ![e i, standardTuple v] := by
      funext j
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun t ↦ Fin.elim0 t) j) j <;> simp
    rw [hv, eval_levyPackedEntryFormula]
    simp [kpair_mem_iff_value, natCast_mem_of_lt i.isLt, eq_comm]
  simp only [he, funext_iff]

theorem eval_levyPackedBody {n : ℕ} (pol : LevyPolarity) (φ : SetTheorySemisentence (n + 1))
    (e v : Fin n → V) (x : V) :
    (levyPackedBody pol φ).Evalb (Matrix.appendr e ![x, standardTuple v]) ↔
      match pol with
      | .sigma => e = v ∧ φ.Evalb (x :> e)
      | .pi => e = v → φ.Evalb (x :> e) := by
  have hv : Matrix.appendr e ![x, standardTuple v] ∘
      Fin.cases ((0 : Fin 2).addNat n) (fun i : Fin n ↦ i.addCast 2) = x :> e := by
    funext j
    refine Fin.cases ?_ (fun i ↦ ?_) j <;> simp
  have hand (θ ψ : SetTheorySemisentence (2 + n)) (b : Fin (2 + n) → V) :
      (θ.and ψ).Evalb b ↔ θ.Evalb b ∧ ψ.Evalb b := Iff.rfl
  have hor (θ ψ : SetTheorySemisentence (2 + n)) (b : Fin (2 + n) → V) :
      (θ.or ψ).Evalb b ↔ θ.Evalb b ∨ ψ.Evalb b := Iff.rfl
  cases pol <;> simp [levyPackedBody, hand, hor, eval_levyPackedEntries,
    eval_boundIndexRew, hv, ← imp_iff_not_or]

theorem eval_levyPackParameters {n : ℕ} (pol : LevyPolarity) (φ : SetTheorySemisentence (n + 1))
    (x : V) (v : Fin n → V) :
    (levyPackParameters pol φ).Evalb ![x, standardTuple v] ↔ φ.Evalb (x :> v) := by
  cases pol with
  | sigma =>
    change (∃¹^[n] levyPackedBody .sigma φ).Eval ![x, standardTuple v] Empty.elim ↔ _
    rw [Semiformula.eval_exsItr]
    change (∃ e, (levyPackedBody .sigma φ).Evalb (Matrix.appendr e ![x, standardTuple v])) ↔ _
    simp only [eval_levyPackedBody, exists_eq_left]
  | pi =>
    change (∀¹^[n] levyPackedBody .pi φ).Eval ![x, standardTuple v] Empty.elim ↔ _
    rw [Semiformula.eval_allItr]
    change (∀ e, (levyPackedBody .pi φ).Evalb (Matrix.appendr e ![x, standardTuple v])) ↔ _
    simp only [eval_levyPackedBody, forall_eq]

end ZFVP
