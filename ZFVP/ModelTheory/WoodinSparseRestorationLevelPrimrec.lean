import ZFVP.ModelTheory.WoodinSparseUniformRestoration
import ZFVP.SetTheory.CnSyntacticBoundPrimrec
import Mathlib.Computability.Primrec.Basic

/-! Primitive recursion of the arithmetic which assembles the finite
restoration bound from the syntax bounds of correctness and extendibility.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

section Components

variable
  (hcn : Primrec (fun n ↦ levySyntacticBound (cnFormula n)))
  (hE : Primrec (fun n ↦ levySyntacticBound (cnExtendibleFormula n)))
  (hUE : Primrec (fun n ↦ levySyntacticBound (unboundedExtendibilitySentence n)))

include hcn

theorem woodinSparseReflectionLevel_primrec_of (code : SetTheorySemisentence 2) :
    Primrec (fun r ↦ woodinSparseReflectionLevel r code) := by
  refine (Primrec.nat_add.comp (Primrec.const 2)
    (Primrec.nat_max.comp hcn
      (Primrec.const (max (levySyntacticBound woodinSupercompactFormula)
        (max (levySyntacticBound code) 0))))).of_eq ?_
  intro r
  simp only [woodinSparseReflectionLevel, woodinSparseReflectionDictionary, listBound,
    levySyntacticBound_rew]

theorem woodinSparseWitnessLevel_primrec_of (code : SetTheorySemisentence 2) :
    Primrec (fun r ↦ woodinSparseWitnessLevel r code) :=
  Primrec.nat_add.comp
    (Primrec.nat_max.comp
      (Primrec.nat_max.comp Primrec.id (Primrec.const woodinSupercompactComplexity.val))
      (woodinSparseReflectionLevel_primrec_of hcn code)) (Primrec.const 2)

theorem woodinSparseCnUnboundedSentence_syntacticBound_primrec_of :
    Primrec (fun c ↦ levySyntacticBound (woodinSparseCnUnboundedSentence c)) := by
  refine (Primrec.nat_add.comp
    (Primrec.nat_max.comp (Primrec.const (levySyntacticBound IsOrdinal.dfn))
      (Primrec.nat_add.comp (Primrec.nat_max.comp (Primrec.const 0) hcn)
        (Primrec.const 2))) (Primrec.const 2)).of_eq ?_
  intro c
  simp only [woodinSparseCnUnboundedSentence, levySyntacticBound,
    Semiformula.imp_eq, levySyntacticBound_neg, levySyntacticBound_rew]
  rfl

include hE hUE in
theorem woodinSparseRestorationLevel_primrec_of (code : SetTheorySemisentence 2) :
    Primrec (fun r ↦ woodinSparseRestorationLevel r code) := by
  have hs := woodinSparseWitnessLevel_primrec_of hcn code
  have hc := woodinSparseReflectionLevel_primrec_of hcn code
  exact Primrec.nat_add.comp
    (Primrec.nat_max.comp hs
      (Primrec.nat_max.comp (hE.comp hs)
        (Primrec.nat_max.comp (hUE.comp hs)
          (Primrec.nat_max.comp (hcn.comp hc)
            ((woodinSparseCnUnboundedSentence_syntacticBound_primrec_of hcn).comp hc)))))
    (Primrec.const 4)

end Components

/-- The complete finite-restoration arithmetic has a primitive recursion
certificate, for every fixed complete-code graph formula. -/
theorem woodinSparseRestorationLevel_primrec (code : SetTheorySemisentence 2) :
    Primrec (fun r ↦ woodinSparseRestorationLevel r code) :=
  woodinSparseRestorationLevel_primrec_of cnFormula_syntacticBound_primrec
    cnExtendibleFormula_syntacticBound_primrec
    unboundedExtendibilitySentence_syntacticBound_primrec code

theorem woodinSparseFiniteRestorationLevel_primrec : Primrec woodinSparseFiniteRestorationLevel :=
  woodinSparseRestorationLevel_primrec woodinSparseCompleteStageCodeFormula

end ZFVP
