import ZFVP.Syntax.MembershipRenaming
import ZFVP.Syntax.NegationSemantics
import ZFVP.ModelTheory.DirectedElementaryUnion

/-! Finite formula templates with a hole for an arbitrary internal membership code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

inductive MembershipTemplate (a : ℕ) : ℕ → Type
  | fixed {n} : SetTheorySemisentence n → MembershipTemplate a n
  | hole {n} : (Fin a → Fin n) → MembershipTemplate a n
  | conj {n} : MembershipTemplate a n → MembershipTemplate a n → MembershipTemplate a n
  | disj {n} : MembershipTemplate a n → MembershipTemplate a n → MembershipTemplate a n
  | neg {n} : MembershipTemplate a n → MembershipTemplate a n
  | all {n} : MembershipTemplate a (n + 1) → MembershipTemplate a n
  | exs {n} : MembershipTemplate a (n + 1) → MembershipTemplate a n

namespace MembershipTemplate

def imp {a n : ℕ} (s t : MembershipTemplate a n) : MembershipTemplate a n := .disj (.neg s) t

def Eval {a : ℕ} {W : Type*} [SetStructure W] (P : (Fin a → W) → Prop) :
    {n : ℕ} → MembershipTemplate a n → (Fin n → W) → Prop
  | _, .fixed ψ, b => ψ.Evalb b
  | _, .hole r, b => P (b ∘ r)
  | _, .conj s t, b => s.Eval P b ∧ t.Eval P b
  | _, .disj s t, b => s.Eval P b ∨ t.Eval P b
  | _, .neg s, b => ¬s.Eval P b
  | _, .all s, b => ∀ x, s.Eval P (x :> b)
  | _, .exs s, b => ∃ x, s.Eval P (x :> b)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def compile {a : ℕ} (φ : V) : {n : ℕ} → MembershipTemplate a n → V
  | _, .fixed ψ => encodeMembershipFormula ψ
  | n, .hole r => renameMembershipFormula (a : V) (n : V) (standardTuple (fun i ↦ ((r i).val : V))) φ
  | _, .conj s t => andCode (s.compile φ) (t.compile φ)
  | _, .disj s t => orCode (s.compile φ) (t.compile φ)
  | n, .neg s => negateFormula membershipLanguageCode ∅ (n : V) (s.compile φ)
  | _, .all s => allCode (s.compile φ)
  | _, .exs s => existsCode (s.compile φ)

theorem compile_valid {a n : ℕ} {φ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (a : V)) (t : MembershipTemplate a n) :
    t.compile φ ∈ formulaSet membershipLanguageCode ∅ (n : V) := by
  induction t with
  | fixed ψ => exact encodeMembershipFormula_mem ψ
  | hole r =>
    exact renameMembershipFormula_mem (by simp) (by simp)
      (standardTuple_mem_function _ (fun i ↦ natCast_mem_of_lt (r i).isLt)) hφ
  | conj s t ihs iht => exact (formulaSet_binary membershipLanguageCode_valid (by simp) ihs iht).1
  | disj s t ihs iht => exact (formulaSet_binary membershipLanguageCode_valid (by simp) ihs iht).2
  | neg s ih => exact negateFormula_mem membershipLanguageCode_valid ih
  | all s ih => exact (formulaSet_quantifiers membershipLanguageCode_valid (by simp)
      (by simpa only [num_succ_def] using ih)).1
  | exs s ih => exact (formulaSet_quantifiers membershipLanguageCode_valid (by simp)
      (by simpa only [num_succ_def] using ih)).2

theorem compile_satisfies {a n : ℕ} {φ U : V} (hU : IsNonempty U)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (a : V))
    (t : MembershipTemplate a n) (b : Fin n → SetDomain U) :
    MembershipSatisfies U (n : V) (t.compile φ) (standardTuple (fun i ↦ (b i).val)) ↔
      t.Eval (fun v ↦ MembershipSatisfies U (a : V) φ (standardTuple (fun i ↦ (v i).val))) b := by
  have hv {j : ℕ} (v : Fin j → SetDomain U) : standardTuple (fun i ↦ (v i).val) ∈ U ^ (j : V) :=
    standardTuple_mem_function _ (fun i ↦ (v i).property)
  induction t with
  | fixed ψ => exact membershipSatisfies_encode hU ψ b
  | hole r =>
    have he := membershipSatisfies_rename hU (by simp) (by simp)
      (standardTuple_mem_function _ (fun i ↦ natCast_mem_of_lt (r i).isLt)) hφ (hv b)
    rw [compose_standardTuple _ _ (fun i ↦ by simp only [domain_standardTuple]; exact natCast_mem_of_lt (r i).isLt)] at he
    simpa only [compile, Eval, value_standardTuple, Function.comp_def] using he
  | conj s t ihs iht =>
    have he := satisfies_and (M := membershipStructureCode U) (e := ∅) membershipLanguageCode_valid
      (by simp) (s.compile_valid hφ) (t.compile_valid hφ) (by simpa using hv b)
    exact he.trans (and_congr (ihs b) (iht b))
  | disj s t ihs iht =>
    have he := satisfies_or (M := membershipStructureCode U) (e := ∅) membershipLanguageCode_valid
      (by simp) (s.compile_valid hφ) (t.compile_valid hφ) (by simpa using hv b)
    exact he.trans (or_congr (ihs b) (iht b))
  | neg s ih =>
    have he := satisfies_negateFormula (M := membershipStructureCode U) (e := ∅) membershipLanguageCode_valid
      (s.compile_valid hφ) (by simpa using hv b)
    exact he.trans (not_congr (ih b))
  | @all n s ih =>
    rw [compile, membershipSatisfies_all (by simp)
      (by simpa only [num_succ_def] using s.compile_valid hφ) (hv b)]
    change (∀ x : V, x ∈ U → _) ↔ ∀ x : SetDomain U, s.Eval _ (x :> b)
    constructor
    · intro hh x
      apply (ih (x :> b)).mp
      simpa only [num_succ_def, standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using hh x.val x.property
    · intro hh x hx
      let x' : SetDomain U := ⟨x, hx⟩
      have he := (ih (x' :> b)).mpr (hh x')
      have he' : MembershipSatisfies U (succ (n : V)) (s.compile φ)
          (assignmentPrepend (n : V) (standardTuple (fun i ↦ (b i).val)) x'.val) := by
        simpa only [num_succ_def, standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using he
      exact he'
  | @exs n s ih =>
    rw [compile, membershipSatisfies_exists (by simp)
      (by simpa only [num_succ_def] using s.compile_valid hφ) (hv b)]
    change (∃ x : V, x ∈ U ∧ _) ↔ ∃ x : SetDomain U, s.Eval _ (x :> b)
    constructor
    · rintro ⟨x, hx, hh⟩
      let x' : SetDomain U := ⟨x, hx⟩
      refine ⟨x', (ih (x' :> b)).mp ?_⟩
      have hh' : MembershipSatisfies U (succ (n : V)) (s.compile φ)
          (assignmentPrepend (n : V) (standardTuple (fun i ↦ (b i).val)) x'.val) := hh
      simpa only [num_succ_def, standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using hh'
    · rintro ⟨x, hx⟩
      refine ⟨x.val, x.property, ?_⟩
      have he := (ih (x :> b)).mpr hx
      simpa only [num_succ_def, standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using he

end MembershipTemplate

end ZFVP
