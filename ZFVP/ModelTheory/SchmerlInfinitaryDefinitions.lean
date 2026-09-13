import ZFVP.ModelTheory.InfinitaryRenaming
import ZFVP.ModelTheory.SchmerlDefinableBranchBound

/-! An actual countable disjunction expressing definability in the original
language of a reduct. Only original-language formulas occur as disjuncts.
The candidate itself may belong to an expanded infinitary language.
-/

namespace ZFVP.Schmerl

open LO LO.FirstOrder
open ZFVP.Infinitary (Formula)

universe u v

/-- Put a finite tuple before an existing assignment, with the arity written
as `n + k` so that iterated binders reduce definitionally. -/
def prependTuple {M : Type u} {n : ℕ} :
    {k : ℕ} → (Fin k → M) → (Fin n → M) → (Fin (n + k) → M)
  | 0, _, b => b
  | k + 1, a, b => a 0 :> prependTuple (fun i : Fin k ↦ a i.succ) b

@[simp] theorem prependTuple_cons {M : Type u} {n k : ℕ}
    (x : M) (a : Fin k → M) (b : Fin n → M) :
    prependTuple (x :> a) b = x :> prependTuple a b := rfl

theorem prependTuple_left {M : Type u} {n k : ℕ}
    (a : Fin k → M) (b : Fin n → M) (i : Fin k) :
    prependTuple a b ⟨i.val, by omega⟩ = a i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change prependTuple (fun j : Fin k ↦ a j.succ) b ⟨i.val, by omega⟩ = a i.succ
      exact ih (fun j ↦ a j.succ) i

theorem prependTuple_right {M : Type u} {n k : ℕ}
    (a : Fin k → M) (b : Fin n → M) (i : Fin n) :
    prependTuple a b ⟨k + i.val, by omega⟩ = b i := by
  induction k with
  | zero => exact congrArg b (Fin.ext (Nat.zero_add i.val))
  | succ k ih =>
    have he : (⟨k + 1 + i.val, by omega⟩ : Fin (n + (k + 1))) =
        (⟨k + i.val, by omega⟩ : Fin (n + k)).succ :=
      Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [he]
    change prependTuple (fun j : Fin k ↦ a j.succ) b ⟨k + i.val, by omega⟩ = b i
    exact ih (fun j ↦ a j.succ)

/-- Bind `k` parameters while retaining `n` outer variables. -/
def existsTuple {L : Language} {n : ℕ} :
    (k : ℕ) → Formula L (n + k) → Formula L n
  | 0, φ => φ
  | k + 1, φ => existsTuple k (.exs φ)

theorem eval_existsTuple {L : Language} {M : Type u} [Structure L M]
    {n : ℕ} (k : ℕ) (φ : Formula L (n + k)) (b : Fin n → M) :
    (existsTuple k φ).Eval b ↔ ∃ a : Fin k → M, φ.Eval (prependTuple a b) := by
  induction k with
  | zero => exact ⟨fun h ↦ ⟨Fin.elim0, h⟩, fun ⟨_, h⟩ ↦ h⟩
  | succ k ih =>
    rw [existsTuple, ih]
    constructor
    · rintro ⟨a, x, hx⟩
      exact ⟨x :> a, hx⟩
    · rintro ⟨a, ha⟩
      exact ⟨fun i ↦ a i.succ, a 0, ha⟩

/-- A first-order predicate with the finite parameter tuple in successor slots. -/
theorem finite_parameter_definition_iff {L : Language.{0}} {M : Type u}
    [Structure L M] [Nonempty M] (P : M → Prop) :
    (L-predicate[M] P) ↔
      ∃ k : ℕ, ∃ θ : Semisentence L (k + 1), ∃ a : Fin k → M,
        ∀ x, θ.Evalb (x :> a) ↔ P x := by
  constructor
  · intro hP
    obtain ⟨⟨k, θ, a⟩, hθ⟩ := DefinableSetCode.exists_code hP
    refine ⟨k, Rew.map (Fin.cast (Nat.add_comm 1 k)) id ▹ θ, a, fun x ↦ ?_⟩
    rw [Semiformula.eval_map]
    have he : (x :> a) ∘ Fin.cast (Nat.add_comm 1 k) =
        Fin.append (fun _ : Fin 1 ↦ x) a := by
      have hc : (x :> a) = Fin.cons x a := by
        funext i
        cases i using Fin.cases <;> rfl
      rw [hc]
      exact (Fin.append_left_eq_cons (fun _ : Fin 1 ↦ x) a).symm
    rw [he]
    exact hθ x
  · rintro ⟨k, θ, a, hθ⟩
    let ρ : Rew L Empty (k + 1) M 1 :=
      Rew.bind (Fin.cases (.bvar 0) (fun i ↦ .fvar (a i))) Empty.elim
    refine ⟨ρ ▹ θ, fun b ↦ ?_⟩
    rw [Semiformula.eval_rew]
    have he : (Semiterm.val b id ∘ ρ ∘ Semiterm.bvar) = b 0 :> a := by
      funext i
      cases i using Fin.cases <;> rfl
    rw [he]
    simpa only [Empty.eq_elim] using hθ (b 0)

variable {L : Language.{0}} {L' : Language.{v}}

/-- Retain the candidate's object variable and its one outer parameter. -/
def definitionCandidateIndex (k : ℕ) : Fin 2 → Fin (1 + k + 1) :=
  Fin.cases 0 (fun _ ↦ Fin.last (1 + k))

def definitionFormulaIndex (k : ℕ) : Fin (k + 1) → Fin (1 + k + 1) :=
  fun i ↦ ⟨i.val, by omega⟩

/-- One disjunct: a fixed original-language formula defines the candidate for
some finite parameter tuple. The original formula cannot mention new symbols. -/
def originalDefinitionInstance (η : L →ᵥ L') (ψ : Formula L' 2)
    (k : ℕ) (θ : Semisentence L (k + 1)) : Formula L' 1 :=
  existsTuple k (.all (.iff
    (ψ.rename (definitionCandidateIndex k))
    (.fo (Rew.map (definitionFormulaIndex k) id ▹ θ.lMap η))))

theorem definitionCandidate_assignment {M : Type u} {k : ℕ}
    (a : Fin k → M) (b x : M) :
    (x :> prependTuple a ![b]) ∘ definitionCandidateIndex k = ![x, b] := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change (x :> prependTuple a ![b]) (Fin.last (1 + k)) = b
    have he : Fin.last (1 + k) = (⟨k, by omega⟩ : Fin (1 + k)).succ :=
      Fin.ext (by simp only [Fin.val_last, Fin.val_succ]; omega)
    rw [he]
    change prependTuple a ![b] ⟨k, by omega⟩ = b
    exact prependTuple_right a ![b] 0

theorem definitionFormula_assignment {M : Type u} {k : ℕ}
    (a : Fin k → M) (b x : M) :
    (x :> prependTuple a ![b]) ∘ definitionFormulaIndex k = x :> a := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    change prependTuple a ![b] ⟨i.val, by omega⟩ = a i
    exact prependTuple_left a ![b] i

theorem eval_originalDefinitionInstance {M : Type u} [s : Structure L' M]
    (η : L →ᵥ L') (ψ : Formula L' 2) (k : ℕ)
    (θ : Semisentence L (k + 1)) (b : M) :
    (originalDefinitionInstance η ψ k θ).Eval ![b] ↔
      ∃ a : Fin k → M, ∀ x,
        ψ.Eval ![x, b] ↔ θ.Evalb (s := s.lMap η) (x :> a) := by
  simp only [originalDefinitionInstance, eval_existsTuple, Formula.eval_all,
    Formula.eval_iff, Formula.eval_rename, Formula.eval_fo,
    Semiformula.eval_map, Semiformula.eval_lMap]
  simp only [definitionCandidate_assignment, definitionFormula_assignment, Empty.eq_elim]

/-- Original formula codes form one countable family independently of any model. -/
abbrev OriginalDefinitionCode (L : Language.{0}) := Σ k : ℕ, Semisentence L (k + 1)

noncomputable def enumerateOriginalDefinitions (L : Language.{0}) [L.Encodable]
    (i : ℕ) : OriginalDefinitionCode L :=
  (Encodable.decode (α := OriginalDefinitionCode L) i).getD ⟨0, ⊤⟩

theorem enumerateOriginalDefinitions_surjective (L : Language.{0}) [L.Encodable] :
    Function.Surjective (enumerateOriginalDefinitions L) := by
  intro c
  exact ⟨Encodable.encode c, by simp [enumerateOriginalDefinitions]⟩

/-- The corrected infinitary reduct-definability clause. -/
noncomputable def originalDefinabilityClause [L.Encodable]
    (η : L →ᵥ L') (ψ : Formula L' 2) : Formula L' 1 :=
  .disj fun i ↦ let c := enumerateOriginalDefinitions L i
    originalDefinitionInstance η ψ c.1 c.2

/-- The disjunction expresses definability in the reduct, including finite
parameters. It does not merely express definability in the expanded language. -/
theorem eval_originalDefinabilityClause [L.Encodable] {M : Type u}
    [s : Structure L' M] [Nonempty M]
    (η : L →ᵥ L') (ψ : Formula L' 2) (b : M) :
    (originalDefinabilityClause η ψ).Eval ![b] ↔
      let : Structure L M := s.lMap η
      L-predicate[M] (fun x ↦ ψ.Eval ![x, b]) := by
  let : Structure L M := s.lMap η
  rw [finite_parameter_definition_iff]
  simp only [originalDefinabilityClause, Formula.eval_disj, eval_originalDefinitionInstance]
  constructor
  · rintro ⟨i, a, ha⟩
    exact ⟨_, _, a, fun x ↦ (ha x).symm⟩
  · rintro ⟨k, θ, a, ha⟩
    obtain ⟨i, hi⟩ := enumerateOriginalDefinitions_surjective L ⟨k, θ⟩
    refine ⟨i, ?_⟩
    rw [hi]
    exact ⟨a, fun x ↦ (ha x).symm⟩

end ZFVP.Schmerl
