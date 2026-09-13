import ZFVP.ModelTheory.WoodinInitialStage
import ZFVP.ModelTheory.WoodinIterationDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingInitialCode (P R one : V) : V :=
  forcingIterationCode (forcingFamilyNext ∅ ∅ P) (forcingFamilyNext ∅ ∅ R)
    (forcingMatrixNext ∅ ∅ ∅ (identity P)) (forcingMatrixNext ∅ ∅ ∅ (identity P))
    (forcingMatrixNext ∅ ∅ ∅ (forcingIdentityLift P)) (forcingFamilyNext ∅ ∅ one)

theorem forcingInitialCode_valid {P R one : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) :
    IsForcingIterationCode (succ ∅) (forcingInitialCode P R one) := by
  unfold forcingInitialCode
  constructor <;> simp only [forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code,
    forcingCodeE_code, forcingCodeL_code, forcingCodet_code]
  · exact forcingInitialSystem hR ht
  · exact forcingFamilyNext_table _ _ _
  · exact forcingFamilyNext_table _ _ _
  · exact forcingMatrixNext_table _ _ _ _
  · exact forcingMatrixNext_table _ _ _ _
  · exact forcingMatrixNext_table _ _ _ _
  · exact forcingFamilyNext_table _ _ _

noncomputable def woodinInitialCode : V :=
  forcingInitialCode (woodinStagePoset (woodinInitialStage : V))
    (woodinStageOrder (woodinInitialStage : V)) (woodinStageTop (woodinInitialStage : V))

noncomputable def woodinInitialCardinals : V :=
  forcingFamilyNext ∅ ∅ (woodinStageCardinal (woodinInitialStage : V))

theorem woodinInitialCode_stage :
    woodinIterationStage (woodinInitialCode : V) woodinInitialCardinals ∅ = woodinInitialStage := by
  simp [woodinIterationStage, woodinInitialCode, woodinInitialCardinals, forcingInitialCode,
    forcingFamilyNext_new, woodinInitialStage, woodinSuccessorStep, woodinSuccessorAt]

theorem woodinInitialCode_iteration {δ : V} (hδ : IsWoodinSupercompact δ) :
    IsWoodinIteration δ (succ ∅) (woodinInitialCode : V) woodinInitialCardinals := by
  obtain ⟨hstage, hsmall, hinac, _, hbound⟩ := woodinInitialStage_properties hδ
  refine ⟨forcingInitialCode_valid hstage.1 hstage.2.1, forcingFamilyNext_table _ _ _,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have he : i = ∅ := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hi
    subst i
    rw [woodinInitialCode_stage]
    exact hstage
  · intro i hi
    have he : i = ∅ := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hi
    subst i
    rw [woodinInitialCode_stage]
    exact hsmall
  · intro i hi
    have he : i = ∅ := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hi
    subst i
    simpa [woodinInitialCardinals, forcingFamilyNext_new] using hinac
  · intro i hi
    have he : i = ∅ := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hi
    subst i
    simpa [woodinInitialCardinals, forcingFamilyNext_new] using hbound
  · intro i hi j hj hij
    have he : i = ∅ := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hi
    have he' : j = ∅ := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hj
    subst i j
    simp at hij

end ZFVP
