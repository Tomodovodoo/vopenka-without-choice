import ZFVP.Syntax.BoundedExpressionLookup
import ZFVP.Syntax.InternalForcingTruthTables

namespace ZFVP.CodeExpression
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Look up a constructed context-formula code at an assignment and condition. -/
def forcingLookupFormula {n : ℕ} (t : CodeExpression n) : SetTheorySemisentence (n + 4) :=
  boundedSetExs (.bvar 0)
    ((boundedKpairFormula.subst ![.bvar 0, .bvar 3, .bvar 4]).and
      (t.lookupFormula.subst (.bvar 1 :> .bvar 2 :> .bvar 0 :>
        fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ)))

theorem forcingLookupFormula_bounded {n : ℕ} (t : CodeExpression n) :
    IsBoundedSetFormula t.forcingLookupFormula :=
  .exs (.bvar 0) (.and (boundedKpairFormula_bounded.subst _) (t.lookupFormula_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_forcingLookupFormula {n : ℕ} (t : CodeExpression n) {U b p : V}
    [hU : IsCodingSupport U] (T : V) (hb : b ∈ U) (hp : p ∈ U)
    (v : Fin n → V) (hv : ∀ i, v i ∈ U) :
    t.forcingLookupFormula.Evalb (U :> T :> b :> p :> v) ↔
      ⟨t.eval v, ⟨b, p⟩ₖ⟩ₖ ∈ T := by
  have hand {k : ℕ} (φ ψ : SetTheorySemisentence k) (w : Fin k → V) :
      (φ.and ψ).Evalb w ↔ φ.Evalb w ∧ ψ.Evalb w := Iff.rfl
  simp [forcingLookupFormula, eval_boundedSetExs, hand, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  simp only [t.eval_lookupFormula T _ v hv]
  simp [hU.kpair_closed b hb p hp]

@[simp] theorem eval_forcingLookupFormula_one (t : CodeExpression 1) {U b p x : V}
    [IsCodingSupport U] (T : V) (hb : b ∈ U) (hp : p ∈ U) (hx : x ∈ U) :
    t.forcingLookupFormula.Evalb ![U, T, b, p, x] ↔ ⟨t.eval ![x], ⟨b, p⟩ₖ⟩ₖ ∈ T :=
  t.eval_forcingLookupFormula T hb hp ![x] (by simpa using hx)

@[simp] theorem eval_forcingLookupFormula_two (t : CodeExpression 2) {U b p x y : V}
    [IsCodingSupport U] (T : V) (hb : b ∈ U) (hp : p ∈ U) (hx : x ∈ U) (hy : y ∈ U) :
    t.forcingLookupFormula.Evalb ![U, T, b, p, x, y] ↔ ⟨t.eval ![x, y], ⟨b, p⟩ₖ⟩ₖ ∈ T :=
  t.eval_forcingLookupFormula T hb hp ![x, y] (by simpa using And.intro hx hy)

@[simp] theorem eval_forcingLookupFormula_three (t : CodeExpression 3) {U b p x y z : V}
    [IsCodingSupport U] (T : V) (hb : b ∈ U) (hp : p ∈ U)
    (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U) :
    t.forcingLookupFormula.Evalb ![U, T, b, p, x, y, z] ↔ ⟨t.eval ![x, y, z], ⟨b, p⟩ₖ⟩ₖ ∈ T :=
  t.eval_forcingLookupFormula T hb hp ![x, y, z] (by
    simp only [Fin.forall_fin_iff_zero_and_forall_succ]
    simpa using And.intro hx (And.intro hy hz))

end ZFVP.CodeExpression
