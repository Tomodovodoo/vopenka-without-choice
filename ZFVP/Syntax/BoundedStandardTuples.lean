import ZFVP.SetTheory.BoundedSequenceSupport
import ZFVP.Syntax.StandardTuples

/-! Bounded checks for standard finite parameter tuples inside a support set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def finiteConjunction {n : ℕ} : {k : ℕ} → (Fin k → SetTheorySemisentence n) → SetTheorySemisentence n
  | 0, _ => .verum
  | k + 1, φ => (φ 0).and (finiteConjunction (fun i : Fin k ↦ φ i.succ))

theorem finiteConjunction_bounded {n k : ℕ} (φ : Fin k → SetTheorySemisentence n)
    (hφ : ∀ i, IsBoundedSetFormula (φ i)) : IsBoundedSetFormula (finiteConjunction φ) := by
  induction k with
  | zero => exact .verum
  | succ k ih => exact .and (hφ 0) (ih _ (fun i ↦ hφ i.succ))

theorem eval_finiteConjunction {V : Type*} [SetStructure V] {n k : ℕ}
    (φ : Fin k → SetTheorySemisentence n) (v : Fin n → V) :
    (finiteConjunction φ).Evalb v ↔ ∀ i, (φ i).Evalb v := by
  induction k with
  | zero => exact ⟨fun _ i ↦ Fin.elim0 i, fun _ ↦ trivial⟩
  | succ k ih =>
    change ((φ 0).Evalb v ∧ (finiteConjunction (fun i : Fin k ↦ φ i.succ)).Evalb v) ↔ _
    rw [ih]
    exact ⟨fun h i ↦ Fin.cases h.1 h.2 i, fun h ↦ ⟨h 0, fun i ↦ h i.succ⟩⟩

def standardTupleEntryFormula {n : ℕ} (i : Fin n) : SetTheorySemisentence (n + 3) :=
  boundedSetExs (.bvar 0) (((boundedNumeralFormula i.val).subst ![.bvar 0]).and
    (boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar i.succ.succ.succ.succ]))

def boundedStandardTupleFormula (n : ℕ) : SetTheorySemisentence (n + 2) :=
  boundedSetExs (.bvar 0) (((boundedNumeralFormula n).subst ![.bvar 0]).and
    ((boundedFunctionFormula.subst ![.bvar 2, .bvar 0, .bvar 1]).and
      (finiteConjunction (fun i : Fin n ↦ standardTupleEntryFormula i))))

theorem standardTupleEntryFormula_bounded {n : ℕ} (i : Fin n) :
    IsBoundedSetFormula (standardTupleEntryFormula i) :=
  .exs (.bvar 0) (.and ((boundedNumeralFormula_bounded i.val).subst _)
    (boundedPairMemberFormula_bounded.subst _))

theorem boundedStandardTupleFormula_bounded (n : ℕ) :
    IsBoundedSetFormula (boundedStandardTupleFormula n) :=
  .exs (.bvar 0) (.and ((boundedNumeralFormula_bounded n).subst _)
    (.and (boundedFunctionFormula_bounded.subst _)
      (finiteConjunction_bounded _ standardTupleEntryFormula_bounded)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

theorem eval_standardTupleEntryFormula {n : ℕ} (i : Fin n) (U t : V) (v : Fin n → V) :
    (standardTupleEntryFormula i).Evalb ((n : V) :> U :> t :> v) ↔
      ⟨(i.val : V), v i⟩ₖ ∈ t := by
  simp [standardTupleEntryFormula, eval_boundedSetExs, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    natCast_mem_of_lt i.isLt, eval_and]

theorem eval_boundedStandardTupleFormula {n : ℕ} (U t : V) [IsCodingSupport U]
    (v : Fin n → V) :
    (boundedStandardTupleFormula n).Evalb (U :> t :> v) ↔
      t = standardTuple v ∧ ∀ i, v i ∈ U := by
  have he : (boundedStandardTupleFormula n).Evalb (U :> t :> v) ↔
      t ∈ U ^ (n : V) ∧ ∀ i : Fin n, ⟨(i.val : V), v i⟩ₖ ∈ t := by
    simp [boundedStandardTupleFormula, eval_boundedSetExs, Semiformula.eval_substs,
      Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
      eval_finiteConjunction, eval_standardTupleEntryFormula, IsCodingSupport.numeral_mem, eval_and]
  rw [he]
  constructor
  · rintro ⟨ht, hv⟩
    let := IsFunction.of_mem ht
    have hparam : ∀ i, v i ∈ U := by
      intro i
      have hp := subset_prod_of_mem_function ht _ (hv i)
      obtain ⟨x, _, y, hy, he⟩ := mem_prod_iff.mp hp
      have hey : v i = y := (kpair_inj he).2
      exact hey.symm ▸ hy
    refine ⟨?_, hparam⟩
    apply mem_ext
    intro p
    rw [mem_standardTuple_iff]
    constructor
    · intro hp
      obtain ⟨x, hx, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function ht _ hp)
      rw [mem_natCast_iff] at hx
      obtain ⟨i, rfl⟩ := hx
      exact ⟨i, congrArg (fun z ↦ ⟨(i.val : V), z⟩ₖ)
        ((value_eq_of_kpair_mem hp).symm.trans (value_eq_of_kpair_mem (hv i)))⟩
    · rintro ⟨i, rfl⟩
      exact hv i
  · rintro ⟨rfl, hv⟩
    exact ⟨standardTuple_mem_function v hv, fun i ↦ (mem_standardTuple_iff v _).mpr ⟨i, rfl⟩⟩

theorem standardTuple_mem_support {n : ℕ} {U : V} [IsSequenceSupport U]
    (v : Fin n → V) (hv : ∀ i, v i ∈ U) : standardTuple v ∈ U :=
  function_mem_sequenceSupport (fun _ h ↦ h) (by simp) (standardTuple_mem_function v hv)

end ZFVP
