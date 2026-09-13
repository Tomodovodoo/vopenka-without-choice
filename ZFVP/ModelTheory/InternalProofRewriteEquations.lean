import ZFVP.ModelTheory.InternalFormulaTransformEquations
import ZFVP.Syntax.PrimitiveProgramProofRewriteEquations

/-! The common formula-transformer results specialized to the explicit proof-rule rewrite. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem evalSet_proofRewriteCode_rel {s d k r v : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hk : k ∈ (ω : V)) (hr : r ∈ (ω : V)) (hv : v ∈ (ω : V)) :
    proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 0 (naturalSquarePair k (naturalSquarePair r v)))))) =
      SetTheory.succ (naturalSquarePair 0 (naturalSquarePair 2 (naturalSquarePair r (proofRewriteArguments.evalSet (naturalSquarePair s (naturalSquarePair d v)))))) := by
  exact evalSet_formulaTransformCode_rel proofRewriteArguments hs hd hk hr hv

@[simp] theorem evalSet_proofRewriteCode_nrel {s d k r v : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hk : k ∈ (ω : V)) (hr : r ∈ (ω : V)) (hv : v ∈ (ω : V)) :
    proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 1 (naturalSquarePair k (naturalSquarePair r v)))))) =
      SetTheory.succ (naturalSquarePair 1 (naturalSquarePair 2 (naturalSquarePair r (proofRewriteArguments.evalSet (naturalSquarePair s (naturalSquarePair d v)))))) := by
  exact evalSet_formulaTransformCode_nrel proofRewriteArguments hs hd hk hr hv

@[simp] theorem evalSet_proofRewriteCode_verum {s d c : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 2 c)))) =
      SetTheory.succ (naturalSquarePair 2 0) := by
  exact evalSet_formulaTransformCode_verum proofRewriteArguments hs hd hc

@[simp] theorem evalSet_proofRewriteCode_falsum {s d c : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 3 c)))) =
      SetTheory.succ (naturalSquarePair 3 0) := by
  exact evalSet_formulaTransformCode_falsum proofRewriteArguments hs hd hc

@[simp] theorem evalSet_proofRewriteCode_and {s d a b : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 4 (naturalSquarePair a b))))) =
      SetTheory.succ (naturalSquarePair 4 (naturalSquarePair (proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d a))) (proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d b))))) := by
  exact evalSet_formulaTransformCode_and proofRewriteArguments hs hd ha hb

@[simp] theorem evalSet_proofRewriteCode_or {s d a b : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 5 (naturalSquarePair a b))))) =
      SetTheory.succ (naturalSquarePair 5 (naturalSquarePair (proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d a))) (proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d b))))) := by
  exact evalSet_formulaTransformCode_or proofRewriteArguments hs hd ha hb

@[simp] theorem evalSet_proofRewriteCode_all {s d a : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (ha : a ∈ (ω : V)) :
    proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 6 a)))) =
      SetTheory.succ (naturalSquarePair 6 (proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair (SetTheory.succ d) a)))) := by
  exact evalSet_formulaTransformCode_all proofRewriteArguments hs hd ha

@[simp] theorem evalSet_proofRewriteCode_exs {s d a : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (ha : a ∈ (ω : V)) :
    proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 7 a)))) =
      SetTheory.succ (naturalSquarePair 7 (proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair (SetTheory.succ d) a)))) := by
  exact evalSet_formulaTransformCode_exs proofRewriteArguments hs hd ha

end ZFVP
