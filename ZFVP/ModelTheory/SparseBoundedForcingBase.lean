import ZFVP.Syntax.BoundedStandardTuples
import ZFVP.Syntax.UniformStandardCodes
import ZFVP.ModelTheory.UniformWoodinSparseClassForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- A fixed formula for the graph of each external finite tuple constructor. -/
def standardTupleValueFormula (n : ℕ) : SetTheorySemisentence (n + 1) :=
  .exs ((sequenceSupportFormula.subst ![.bvar 0]).and
    ((boundedStandardTupleFormula n).subst (.bvar 0 :> .bvar 1 :> forcingParameterTerms 2 rfl)))

def sparseBoundedForcingBase {n : ℕ} (φ : BoundedFormulaTree n) : SetTheorySemisentence (n + 1) :=
  .exs (.exs (.exs
    (((numeralFormula n).subst ![.bvar 0]).and
      (((encodeMembershipFormulaFormula φ.formula).subst ![.bvar 1]).and
        (((standardTupleValueFormula n).subst (.bvar 2 :> forcingParameterTerms 4 rfl)).and
          (woodinSparseLocalForcingFormula.subst ![.bvar 0, .bvar 1, .bvar 2, .bvar 3]))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl
private theorem eval_exs {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    φ.exs.Evalb v ↔ ∃ x : V, φ.Evalb (x :> v) := Iff.rfl

theorem eval_standardTupleValueFormula {n : ℕ} (t : V) (v : Fin n → V) :
    (standardTupleValueFormula n).Evalb (t :> v) ↔ t = standardTuple v := by
  have he : (standardTupleValueFormula n).Evalb (t :> v) ↔
      ∃ U : V, IsSequenceSupport U ∧ (boundedStandardTupleFormula n).Evalb (U :> t :> v) := by
    simp [standardTupleValueFormula, eval_exs, eval_and, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, forcingParameterTerms, Function.comp_def]
  rw [he]
  constructor
  · rintro ⟨U, hU, he⟩
    let := hU
    exact ((eval_boundedStandardTupleFormula U t v).mp he).1
  · intro ht
    obtain ⟨U, hU, hr⟩ := sequenceSupport_containing (range (standardTuple v))
    let := hU
    refine ⟨U, hU, (eval_boundedStandardTupleFormula U t v).mpr ⟨ht, ?_⟩⟩
    intro i
    apply hU.toIsTransitive.mem_trans ?_ hr
    apply mem_range_iff.mpr
    exact ⟨(i.val : V), (mem_standardTuple_iff v _).mpr ⟨i, rfl⟩⟩

theorem eval_sparseBoundedForcingBase {n : ℕ} (φ : BoundedFormulaTree n)
    (p : V) (v : Fin n → V) :
    (sparseBoundedForcingBase φ).Evalb (p :> v) ↔
      WoodinSparseLocalPrefixForces (n : V) (encodeMembershipFormula φ.formula) (standardTuple v) p := by
  simp [sparseBoundedForcingBase, eval_exs, eval_and, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, forcingParameterTerms, Function.comp_def,
    eval_standardTupleValueFormula, eval_woodinSparseLocalForcingFormula
      (show IsMembershipFormulaCode (n : V) (encodeMembershipFormula φ.formula) from
        (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem φ.formula))]

end ZFVP

