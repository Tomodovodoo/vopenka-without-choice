import ZFVP.ModelTheory.TransitiveZFSuccessorColumns
import ZFVP.ModelTheory.TransitiveZFTwoStepForcing
import ZFVP.ModelTheory.TwoStepColumnCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem compose_val (R S : SetDomain U) : (compose R S).val = compose R.val S.val := by
  apply SetTheory.mem_ext_iff.mpr
  intro p
  constructor
  · intro hp
    let p' : SetDomain U := ⟨p, (inferInstance : IsTransitive U).mem_trans hp (compose R S).property⟩
    obtain ⟨x, y, z, hR, hS, he⟩ := mem_compose_iff.mp (show p' ∈ compose R S from hp)
    apply mem_compose_iff.mpr
    refine ⟨x.val, y.val, z.val, ?_, ?_, ?_⟩
    · change (⟨x, y⟩ₖ : SetDomain U).val ∈ R.val at hR
      simpa only [kpair_val U] using hR
    · change (⟨y, z⟩ₖ : SetDomain U).val ∈ S.val at hS
      simpa only [kpair_val U] using hS
    · exact (congrArg Subtype.val he).trans (kpair_val U x z)
  · intro hp
    obtain ⟨x, y, z, hR, hS, rfl⟩ := mem_compose_iff.mp hp
    have hxy := kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hR R.property)
    have hyz := kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hS S.property)
    let x' : SetDomain U := ⟨x, hxy.1⟩
    let y' : SetDomain U := ⟨y, hxy.2⟩
    let z' : SetDomain U := ⟨z, hyz.2⟩
    have hR' : (⟨x', y'⟩ₖ : SetDomain U) ∈ R := by
      change (⟨x', y'⟩ₖ : SetDomain U).val ∈ R.val
      simpa only [kpair_val U] using hR
    have hS' : (⟨y', z'⟩ₖ : SetDomain U) ∈ S := by
      change (⟨y', z'⟩ₖ : SetDomain U).val ∈ S.val
      simpa only [kpair_val U] using hS
    have hh := kpair_mem_compose_iff.mpr ⟨y', hR', hS'⟩
    change (⟨x', z'⟩ₖ : SetDomain U).val ∈ (compose R S).val at hh
    simpa only [kpair_val U] using hh

theorem forcingComposeProjectionColumn_val (θ ρ v : SetDomain U) :
    (forcingComposeProjectionColumn θ ρ v).val = forcingComposeProjectionColumn θ.val ρ.val v.val := by
  unfold forcingComposeProjectionColumn
  apply definableGraph_val U
  intro j _
  rw [compose_val U, value_val_total U]

theorem forcingComposeSectionColumn_val (θ F e : SetDomain U) :
    (forcingComposeSectionColumn θ F e).val = forcingComposeSectionColumn θ.val F.val e.val := by
  unfold forcingComposeSectionColumn
  apply definableGraph_val U
  intro j _
  rw [compose_val U, value_val_total U]

theorem forcingTwoStepLiftColumn_val (θ D P M : SetDomain U) :
    (forcingTwoStepLiftColumn θ D P M).val = forcingTwoStepLiftColumn θ.val D.val P.val M.val := by
  unfold forcingTwoStepLiftColumn
  apply definableGraph_val U
  intro i _
  rw [successorForcingLift_val U, value_val_total U, value_val_total U]

theorem twoStepProjection_val (P R Q t : SetDomain U) :
    (twoStepProjection P R Q t).val = twoStepProjection P.val R.val Q.val t.val := by
  unfold twoStepProjection
  rw [← twoStepConditions_val U]
  apply definableGraph_val U
  intro a _
  exact kpair_first_val U a

theorem twoStepSection_val (P t : SetDomain U) :
    (twoStepSection P t).val = twoStepSection P.val t.val := by
  unfold twoStepSection
  apply definableGraph_val U
  intro p _
  exact kpair_val U p t

theorem forcingTwoStepColumnCode_val (θ s C T ρ F M one Q S u : SetDomain U)
    (hT : IsForcingPreorder C T) (hQ : IsForcingName C Q)
    (hS : IsForcingName C S) (hu : IsForcingName C u) :
    (forcingTwoStepColumnCode θ s C T ρ F M one Q S u).val =
      forcingTwoStepColumnCode θ.val s.val C.val T.val ρ.val F.val M.val one.val Q.val S.val u.val := by
  simp only [forcingTwoStepColumnCode, forcingIterationCodeNext_val U,
    twoStepConditions_val U, twoStepOrder_val_of_names U C T Q S u hT hQ hS hu,
    forcingComposeProjectionColumn_val U, forcingComposeSectionColumn_val U,
    forcingTwoStepLiftColumn_val U, twoStepProjection_val U, twoStepSection_val U,
    forcingCodeP_val U, kpair_val U]

end TransitiveZF
end ZFVP
