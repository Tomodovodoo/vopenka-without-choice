import ZFVP.ModelTheory.TransitiveZFIterationTables

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem twoStepStronger_val (a p : SetDomain U) :
    (twoStepStronger a p).val = twoStepStronger a.val p.val := by
  simp only [twoStepStronger, kpair_val U, kpair_second_val U]

theorem successorForcingLiftValue_val (L a b : SetDomain U) :
    (successorForcingLiftValue L a b).val = successorForcingLiftValue L.val a.val b.val := by
  simp only [successorForcingLiftValue, twoStepStronger_val U, value_val_total U,
    kpair_val U, kpair_first_val U]

theorem successorForcingLift_val (C A L : SetDomain U) :
    (successorForcingLift C A L).val = successorForcingLift C.val A.val L.val := by
  unfold successorForcingLift
  rw [← prod_val U]
  apply definableGraph_val U
  intro z _
  rw [successorForcingLiftValue_val U, kpair_first_val U, kpair_second_val U]

theorem successorStageProjection_val (C π k i : SetDomain U) :
    (successorStageProjection C π k i).val = successorStageProjection C.val π.val k.val i.val := by
  unfold successorStageProjection
  apply definableGraph_val U
  intro a _
  simp only [value_val_total U, kpair_val U, kpair_first_val U]

theorem successorStageSection_val (P E k t i : SetDomain U) :
    (successorStageSection P E k t i).val = successorStageSection P.val E.val k.val t.val i.val := by
  unfold successorStageSection
  rw [← value_val_total U P i]
  apply definableGraph_val U
  intro p _
  simp only [kpair_val U, value_val_total U]

theorem successorProjectionColumn_val (θ C π k : SetDomain U) :
    (successorProjectionColumn θ C π k).val = successorProjectionColumn θ.val C.val π.val k.val := by
  unfold successorProjectionColumn
  apply definableGraph_val U
  intro i _
  exact successorStageProjection_val U C π k i

theorem successorSectionColumn_val (θ P E k t : SetDomain U) :
    (successorSectionColumn θ P E k t).val = successorSectionColumn θ.val P.val E.val k.val t.val := by
  unfold successorSectionColumn
  apply definableGraph_val U
  intro i _
  exact successorStageSection_val U P E k t i

theorem successorLiftColumn_val (θ C P L k : SetDomain U) :
    (successorLiftColumn θ C P L k).val = successorLiftColumn θ.val C.val P.val L.val k.val := by
  unfold successorLiftColumn
  apply definableGraph_val U
  intro i _
  simp only [successorForcingLift_val U, value_val_total U, kpair_val U]

end TransitiveZF

theorem woodinIterationSuccessor_eq_code (k s K : V) :
    woodinIterationSuccessor k s K =
      let x := woodinSuccessorStep (woodinIterationStage s K k)
      forcingIterationCodeNext (succ k) s (woodinStagePoset x) (woodinStageOrder x)
        (successorProjectionColumn (succ k) (woodinStagePoset x) (forcingCodeπ s) k)
        (successorSectionColumn (succ k) (forcingCodeP s) (forcingCodeE s) k ∅)
        (successorLiftColumn (succ k) (woodinStagePoset x) (forcingCodeP s) (forcingCodeL s) k)
        (woodinStageTop x) := by
  simp only [woodinIterationSuccessor, forcingSuccessorCode, woodinIterationStage,
    woodinSuccessorStep, woodinSuccessorAt, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code]

theorem TransitiveZF.woodinIterationSuccessor_val (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (k s K : SetDomain U)
    (hstep : (woodinSuccessorStep (woodinIterationStage s K k)).val =
      woodinSuccessorStep (woodinIterationStage s.val K.val k.val)) :
    (woodinIterationSuccessor k s K).val = woodinIterationSuccessor k.val s.val K.val := by
  simp only [woodinIterationSuccessor_eq_code, forcingIterationCodeNext_val U,
    successorProjectionColumn_val U, successorSectionColumn_val U, successorLiftColumn_val U,
    succ_val U, woodinStagePoset_val U, woodinStageOrder_val U, woodinStageTop_val U,
    forcingCodeP_val U, forcingCodeπ_val U, forcingCodeE_val U, forcingCodeL_val U, empty_val U, hstep]

theorem TransitiveZF.woodinIterationCardinalNext_val (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (k s K : SetDomain U)
    (hstep : (woodinSuccessorStep (woodinIterationStage s K k)).val =
      woodinSuccessorStep (woodinIterationStage s.val K.val k.val)) :
    (woodinIterationCardinalNext k s K).val = woodinIterationCardinalNext k.val s.val K.val := by
  simp only [woodinIterationCardinalNext, forcingFamilyNext_val U, succ_val U,
    woodinStageCardinal_val U, hstep]

end ZFVP
