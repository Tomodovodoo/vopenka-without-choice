import ZFVP.ModelTheory.ProjectionQuotientDensity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def projectionQuotientDensePreimage (P R Q S π one D : V) : V :=
  {r ∈ Q ; ∃ d ∈ Q, ⟨r, d⟩ₖ ∈ S ∧ π ‘ r ∈ atomicMembership P R (checkName one d) D}

theorem projectionQuotientDensePreimage_denseBelow {P R Q S π E one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hS : IsForcingPreorder Q S) (hπ : IsForcingSplitProjection P R Q S π E)
    (D : ForcingName P) (hp : p ∈ P)
    (hD : p ∈ forcingFormula P R forcingDenseFormula
      (standardTuple ![projectionQuotientName Q π one, projectionQuotientOrderName S π one, D.val])) :
    ForcingDenseBelow Q S (projectionQuotientDensePreimage P R Q S π one D.val) (E ‘ p) := by
  refine ⟨fun r hr ↦ (mem_sep_iff.mp hr).1, ?_⟩
  intro q hq hqp
  obtain ⟨r, hr, d, hd, hrq, hrd, hD'⟩ := projectionQuotient_dense_lift hR htop hS hπ.projection
    D hD hq ((hπ.below q hq p hp).mp hqp)
  exact ⟨r, mem_sep_iff.mpr ⟨hr, d, hd, hrd, hD'⟩, hrq⟩

theorem ForcingContext.projectionQuotient_generic (A : ForcingContext V) {Q S π E : V} {G : Set V}
    (hπ : IsForcingSplitProjection A.P A.R Q S π E) (hS : IsForcingPreorder Q S)
    (hG : IsExternalForcingGeneric Q S G)
    (he : forcingProjectionGeneric A.P A.R π G = A.G) :
    IsExternalForcingGeneric (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)
      (A.projectionQuotientFilter G) := by
  refine ⟨A.projectionQuotient_filter hπ.projection hG.1 he, ?_⟩
  intro D hD
  obtain ⟨δ, rfl⟩ := A.ofName_surjective D
  let QN : ForcingName A.P := ⟨projectionQuotientName Q π A.one,
    projectionQuotientName_isName A.top.1 hπ.projection.maps⟩
  let SN : ForcingName A.P := ⟨projectionQuotientOrderName S π A.one,
    projectionQuotientOrderName_isName A.top.1 hπ.projection.maps hS⟩
  have hd : ForcingDense (A.ofName QN) (A.ofName SN) (A.ofName δ) := by
    rw [A.ofName_projectionQuotient hπ.projection.maps, A.ofName_projectionQuotientOrder hπ.projection hS]
    exact hD
  have hf : forcingDenseFormula.Evalb (fun i ↦ A.ofName (![QN, SN, δ] i)) := (Defined.eval_iff _).mpr hd
  obtain ⟨p, hpG, hp⟩ := (A.formula_truth forcingDenseFormula ![QN, SN, δ]).mp hf
  have hpProj : p ∈ forcingProjectionGeneric A.P A.R π G := he.symm ▸ hpG
  have hpE : E ‘ p ∈ G := (hπ.generic_iff_section A.order hG.1 (A.generic.1.1 p hpG)).mp hpProj
  have hdense := projectionQuotientDensePreimage_denseBelow A.order A.top hS hπ δ
    (A.generic.1.1 p hpG) hp
  obtain ⟨r, hrG, hrD⟩ := externalForcingGeneric_meets_denseBelow hS hG hpE hdense
  obtain ⟨d, hdQ, hrd, hforce⟩ := (mem_sep_iff.mp hrD).2
  have hdG := hG.1.2.2.1 r hrG d hdQ hrd
  have hπrG : π ‘ r ∈ A.G := he ▸ hπ.projection.image_mem A.order hG.1 hrG
  refine ⟨A.check d, ⟨d, hdG, rfl⟩, ?_⟩
  have ht := (A.formula_truth nameMemberFormula
    ![⟨checkName A.one d, checkName_isName A.top.1 d⟩, δ]).mpr
      ⟨π ‘ r, hπrG, by
        change π ‘ r ∈ forcingFormula A.P A.R nameMemberFormula (standardTuple ![checkName A.one d, δ.val])
        rwa [forcingFormula_nameMember]⟩
  exact ht

end ZFVP
