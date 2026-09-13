import ZFVP.Syntax.MembershipTemplates
import ZFVP.Syntax.PrefixTuples

/-! Formula templates preserve an arbitrary internal list of parameters. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace MembershipTemplate

noncomputable def compileTail {a : ℕ} (n φ : V) : {m : ℕ} → MembershipTemplate a m → V
  | m, .fixed ψ => renameMembershipFormula (m : V) (prefixSize m n)
      (standardTuple (fun i : Fin m ↦ (i.val : V))) (encodeMembershipFormula ψ)
  | m, .hole r => renameMembershipFormula (prefixSize a n) (prefixSize m n) (prefixRenaming r n) φ
  | _, .conj s t => andCode (s.compileTail n φ) (t.compileTail n φ)
  | _, .disj s t => orCode (s.compileTail n φ) (t.compileTail n φ)
  | m, .neg s => negateFormula membershipLanguageCode ∅ (prefixSize m n) (s.compileTail n φ)
  | _, .all s => allCode (s.compileTail n φ)
  | _, .exs s => existsCode (s.compileTail n φ)

theorem compileTail_valid {a m : ℕ} {n φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (prefixSize a n)) (t : MembershipTemplate a m) :
    t.compileTail n φ ∈ formulaSet membershipLanguageCode ∅ (prefixSize m n) := by
  induction t with
  | fixed ψ =>
    exact renameMembershipFormula_mem (by simp) (prefixSize_natural _ hn)
      (standardTuple_mem_function _ (natCast_mem_prefixSize hn)) (encodeMembershipFormula_mem ψ)
  | hole r =>
    exact renameMembershipFormula_mem (prefixSize_natural _ hn) (prefixSize_natural _ hn)
      (prefixRenaming_function r hn) hφ
  | conj s t ihs iht => exact (formulaSet_binary membershipLanguageCode_valid (prefixSize_natural _ hn) ihs iht).1
  | disj s t ihs iht => exact (formulaSet_binary membershipLanguageCode_valid (prefixSize_natural _ hn) ihs iht).2
  | neg s ih => exact negateFormula_mem membershipLanguageCode_valid ih
  | all s ih => exact (formulaSet_quantifiers membershipLanguageCode_valid (prefixSize_natural _ hn) ih).1
  | exs s ih => exact (formulaSet_quantifiers membershipLanguageCode_valid (prefixSize_natural _ hn) ih).2

theorem compileTail_satisfies {a m : ℕ} {n φ U b : V} (hU : IsNonempty U) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (prefixSize a n)) (hb : b ∈ U ^ n)
    (t : MembershipTemplate a m) (v : Fin m → SetDomain U) :
    MembershipSatisfies U (prefixSize m n) (t.compileTail n φ) (prependTuple n b (fun i ↦ (v i).val)) ↔
      t.Eval (fun w ↦ MembershipSatisfies U (prefixSize a n) φ (prependTuple n b (fun i ↦ (w i).val))) v := by
  have hv {j : ℕ} (w : Fin j → SetDomain U) : prependTuple n b (fun i ↦ (w i).val) ∈ U ^ prefixSize j n :=
    prependTuple_function hn hb _ (fun i ↦ (w i).property)
  induction t with
  | fixed ψ =>
    have he := membershipSatisfies_rename hU (by simp) (prefixSize_natural _ hn)
      (standardTuple_mem_function _ (natCast_mem_prefixSize hn)) (encodeMembershipFormula_mem ψ) (hv v)
    rw [standardIndices_compose_prependTuple hn hb _ (fun i ↦ (v i).property)] at he
    exact he.trans (membershipSatisfies_encode hU ψ v)
  | hole r =>
    have he := membershipSatisfies_rename hU (prefixSize_natural _ hn) (prefixSize_natural _ hn)
      (prefixRenaming_function r hn) hφ (hv v)
    rw [prefixRenaming_compose r hn hb _ (fun i ↦ (v i).property)] at he
    exact he
  | conj s t ihs iht =>
    have he := satisfies_and (M := membershipStructureCode U) (e := ∅) membershipLanguageCode_valid
      (prefixSize_natural _ hn) (s.compileTail_valid hn hφ) (t.compileTail_valid hn hφ) (by simpa using hv v)
    exact he.trans (and_congr (ihs v) (iht v))
  | disj s t ihs iht =>
    have he := satisfies_or (M := membershipStructureCode U) (e := ∅) membershipLanguageCode_valid
      (prefixSize_natural _ hn) (s.compileTail_valid hn hφ) (t.compileTail_valid hn hφ) (by simpa using hv v)
    exact he.trans (or_congr (ihs v) (iht v))
  | neg s ih =>
    have he := satisfies_negateFormula (M := membershipStructureCode U) (e := ∅) membershipLanguageCode_valid
      (s.compileTail_valid hn hφ) (by simpa using hv v)
    exact he.trans (not_congr (ih v))
  | @all m s ih =>
    rw [compileTail, membershipSatisfies_all (prefixSize_natural _ hn) (s.compileTail_valid hn hφ) (hv v)]
    change (∀ x : V, x ∈ U → _) ↔ ∀ x : SetDomain U, s.Eval _ (x :> v)
    constructor
    · intro hh x
      apply (ih (x :> v)).mp
      simpa only [prefixSize, prependTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using hh x.val x.property
    · intro hh x hx
      let x' : SetDomain U := ⟨x, hx⟩
      have he := (ih (x' :> v)).mpr (hh x')
      have he' : MembershipSatisfies U (succ (prefixSize m n)) (s.compileTail n φ)
          (assignmentPrepend (prefixSize m n) (prependTuple n b (fun i ↦ (v i).val)) x'.val) := by
        simpa only [prefixSize, prependTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using he
      exact he'
  | @exs m s ih =>
    rw [compileTail, membershipSatisfies_exists (prefixSize_natural _ hn) (s.compileTail_valid hn hφ) (hv v)]
    change (∃ x : V, x ∈ U ∧ _) ↔ ∃ x : SetDomain U, s.Eval _ (x :> v)
    constructor
    · rintro ⟨x, hx, hh⟩
      let x' : SetDomain U := ⟨x, hx⟩
      refine ⟨x', (ih (x' :> v)).mp ?_⟩
      have hh' : MembershipSatisfies U (succ (prefixSize m n)) (s.compileTail n φ)
          (assignmentPrepend (prefixSize m n) (prependTuple n b (fun i ↦ (v i).val)) x'.val) := hh
      simpa only [prefixSize, prependTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using hh'
    · rintro ⟨x, hx⟩
      refine ⟨x.val, x.property, ?_⟩
      have he := (ih (x :> v)).mpr hx
      simpa only [prefixSize, prependTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using he

end MembershipTemplate

end ZFVP
