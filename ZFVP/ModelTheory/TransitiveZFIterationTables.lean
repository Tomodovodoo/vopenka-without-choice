import ZFVP.ModelTheory.TransitiveZFWoodinStage
import ZFVP.ModelTheory.LimitRankRestriction
import ZFVP.ModelTheory.WoodinIterationInitial

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem definableGraph_val (A : SetDomain U) (F : SetDomain U → SetDomain U)
    (hF : ℒₛₑₜ-function₁ F) (G : V → V) (hG : ℒₛₑₜ-function₁ G)
    (hval : ∀ x ∈ A, (F x).val = G x.val) :
    (definableGraph A F hF).val = definableGraph A.val G hG := by
  unfold definableGraph
  apply repl_val U
  intro x hx
  rw [kpair_val U, hval x hx]

theorem forcingFamilyNextValue_val (θ P Q i : SetDomain U) :
    (forcingFamilyNextValue θ P Q i).val = forcingFamilyNextValue θ.val P.val Q.val i.val := by
  classical
  by_cases he : i = θ
  · subst i
    simp [forcingFamilyNextValue]
  · have hv : i.val ≠ θ.val := fun h ↦ he (Subtype.ext h)
    simp only [forcingFamilyNextValue, he, hv, ↓reduceIte, value_val_total U]

theorem forcingFamilyNext_val (θ P Q : SetDomain U) :
    (forcingFamilyNext θ P Q).val = forcingFamilyNext θ.val P.val Q.val := by
  unfold forcingFamilyNext
  rw [← succ_val U θ]
  apply definableGraph_val U
  intro i _
  exact forcingFamilyNextValue_val U θ P Q i

theorem forcingMatrixNextValue_val (θ M C d z : SetDomain U) :
    (forcingMatrixNextValue θ M C d z).val =
      forcingMatrixNextValue θ.val M.val C.val d.val z.val := by
  classical
  have he : kpair.π₂ z = θ ↔ kpair.π₂ z.val = θ.val := by
    rw [← kpair_second_val U z]
    exact ⟨congrArg Subtype.val, Subtype.ext⟩
  unfold forcingMatrixNextValue
  split_ifs with hi hj hj
  · rw [forcingFamilyNextValue_val U, kpair_first_val U]
  · exact False.elim (hj (he.mp hi))
  · exact False.elim (hi (he.mpr hj))
  · exact value_val_total U M z

theorem forcingMatrixNext_val (θ M C d : SetDomain U) :
    (forcingMatrixNext θ M C d).val = forcingMatrixNext θ.val M.val C.val d.val := by
  unfold forcingMatrixNext
  rw [← succ_val U θ, ← prod_val U]
  apply definableGraph_val U
  intro z _
  exact forcingMatrixNextValue_val U θ M C d z

theorem forcingIdentityLift_val (P : SetDomain U) :
    (forcingIdentityLift P).val = forcingIdentityLift P.val := by
  unfold forcingIdentityLift
  rw [← prod_val U]
  apply definableGraph_val U
  intro z _
  exact kpair_second_val U z

theorem forcingIterationCode_val (P R π E L t : SetDomain U) :
    (forcingIterationCode P R π E L t).val =
      forcingIterationCode P.val R.val π.val E.val L.val t.val := by
  simp only [forcingIterationCode, kpair_val U]

theorem forcingInitialCode_val (P R t : SetDomain U) :
    (forcingInitialCode P R t).val = forcingInitialCode P.val R.val t.val := by
  simp only [forcingInitialCode, forcingIterationCode_val U, forcingFamilyNext_val U,
    forcingMatrixNext_val U, identity_val U, forcingIdentityLift_val U, empty_val U]

theorem forcingCodeP_val (s : SetDomain U) : (forcingCodeP s).val = forcingCodeP s.val := by
  simp only [forcingCodeP, kpair_first_val U]

theorem forcingCodeR_val (s : SetDomain U) : (forcingCodeR s).val = forcingCodeR s.val := by
  simp only [forcingCodeR, kpair_first_val U, kpair_second_val U]

theorem forcingCodeπ_val (s : SetDomain U) : (forcingCodeπ s).val = forcingCodeπ s.val := by
  simp only [forcingCodeπ, kpair_first_val U, kpair_second_val U]

theorem forcingCodeE_val (s : SetDomain U) : (forcingCodeE s).val = forcingCodeE s.val := by
  simp only [forcingCodeE, kpair_first_val U, kpair_second_val U]

theorem forcingCodeL_val (s : SetDomain U) : (forcingCodeL s).val = forcingCodeL s.val := by
  simp only [forcingCodeL, kpair_first_val U, kpair_second_val U]

theorem forcingCodet_val (s : SetDomain U) : (forcingCodet s).val = forcingCodet s.val := by
  simp only [forcingCodet, kpair_second_val U]

theorem forcingIterationCodeNext_val (θ s Q T ρ F M u : SetDomain U) :
    (forcingIterationCodeNext θ s Q T ρ F M u).val =
      forcingIterationCodeNext θ.val s.val Q.val T.val ρ.val F.val M.val u.val := by
  simp only [forcingIterationCodeNext, forcingIterationCode_val U, forcingFamilyNext_val U,
    forcingMatrixNext_val U, identity_val U, forcingIdentityLift_val U, forcingCodeP_val U,
    forcingCodeR_val U, forcingCodeπ_val U, forcingCodeE_val U, forcingCodeL_val U, forcingCodet_val U]

theorem woodinIterationStage_val (s K i : SetDomain U) :
    (woodinIterationStage s K i).val = woodinIterationStage s.val K.val i.val := by
  simp only [woodinIterationStage, woodinStageCode_val U, value_val_total U,
    forcingCodeP_val U, forcingCodeR_val U, forcingCodet_val U]

end TransitiveZF
end ZFVP
