import ZFVP.ModelTheory.WoodinCollapseNamedDisplacementForcing
import ZFVP.ModelTheory.SaturatedPrefixSpecification
import ZFVP.ModelTheory.SaturatedHartogsSpecification
import ZFVP.ModelTheory.ForcingCheckedBounded
import ZFVP.ModelTheory.ForcedOrderLaws

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem collapseDisplacement_forces_preInput {P R top r : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hr : r ∈ P)
    (Q S κ δ p q : ForcingName P)
    (hκ : r ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : r ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![δ.val]))
    (hQ : r ∈ forcingFormula P R totalWoodinCollapseFormula (standardTuple ![Q.val, κ.val, δ.val]))
    (hS : r ∈ forcingFormula P R piOneReverseInclusionOrderFormula (standardTuple ![S.val, Q.val]))
    (hp : r ∈ atomicMembership P R p.val Q.val) (hq : r ∈ atomicMembership P R q.val Q.val) :
    r ∈ forcingFormula P R collapseDisplacementPreInputFormula
      (standardTuple ![Q.val, S.val, κ.val, δ.val, p.val, q.val]) := by
  let φ : SetTheorySemisentence 6 :=
    (regularCardinalFormula.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 6) i))).and
      ((IsOrdinal.dfn.subst (fun i ↦ .bvar ((![3] : Fin 1 → Fin 6) i))).and
        ((totalWoodinCollapseFormula.subst (fun i ↦ .bvar ((![0, 2, 3] : Fin 3 → Fin 6) i))).and
          ((piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 6) i))).and
            ((nameMemberFormula.subst (fun i ↦ .bvar ((![4, 0] : Fin 2 → Fin 6) i))).and
              (nameMemberFormula.subst (fun i ↦ .bvar ((![5, 0] : Fin 2 → Fin 6) i)))))))
  have hφ : r ∈ forcingFormula P R φ (standardTuple ![Q.val, S.val, κ.val, δ.val, p.val, q.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_and, mem_inter_iff,
      forcingFormula_rename, forcingFormula_rename, forcingFormula_rename,
      forcingFormula_rename, forcingFormula_rename, forcingFormula_rename]
    refine ⟨hκ, hδ, hQ, hS, ?_, ?_⟩
    · change r ∈ forcingFormula P R nameMemberFormula (standardTuple ![p.val, Q.val])
      rwa [forcingFormula_nameMember]
    · change r ∈ forcingFormula P R nameMemberFormula (standardTuple ![q.val, Q.val])
      rwa [forcingFormula_nameMember]
  apply forcingFormula_entailment φ collapseDisplacementPreInputFormula _ hR ht hr ![Q, S, κ, δ, p, q] hφ
  intro W _ _ _ v hv
  apply (eval_collapseDisplacementPreInputFormula v).mpr
  change (regularCardinalFormula.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 6) i))).Evalb v ∧
    (IsOrdinal.dfn.subst (fun i ↦ .bvar ((![3] : Fin 1 → Fin 6) i))).Evalb v ∧
    (totalWoodinCollapseFormula.subst (fun i ↦ .bvar ((![0, 2, 3] : Fin 3 → Fin 6) i))).Evalb v ∧
    (piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 6) i))).Evalb v ∧
    (nameMemberFormula.subst (fun i ↦ .bvar ((![4, 0] : Fin 2 → Fin 6) i))).Evalb v ∧
    (nameMemberFormula.subst (fun i ↦ .bvar ((![5, 0] : Fin 2 → Fin 6) i))).Evalb v at hv
  simpa [Semiformula.eval_substs, nameMemberFormula] using hv

theorem saturatedPrefix_displacementName_forces_output {P R top κ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : top ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName top κ]))
    (p q : ForcingName P)
    (hp : top ∈ atomicMembership P R p.val (saturatedWoodinPrefixPosetName P R top κ δ))
    (hq : top ∈ atomicMembership P R q.val (saturatedWoodinPrefixPosetName P R top κ δ)) :
    let Q := saturatedWoodinPrefixPosetName P R top κ δ
    let S := saturatedWoodinPrefixOrderName P R top κ δ
    let f := woodinCollapseDisplacementName P R (checkName top κ) (checkName top δ) p.val q.val
    let g := ZFVP.collapseConverseName P R f
    top ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple ![Q, S, checkName top κ, checkName top δ, p.val, q.val, f, g]) := by
  let Q : ForcingName P := ⟨saturatedWoodinPrefixPosetName P R top κ δ,
    saturatedWoodinPrefixPosetName_isName _ _ _ _ _⟩
  let S : ForcingName P := ⟨saturatedWoodinPrefixOrderName P R top κ δ,
    saturatedWoodinPrefixOrderName_isName _ _ _ _ _⟩
  let a : ForcingName P := ⟨checkName top κ, checkName_isName ht.1 κ⟩
  let b : ForcingName P := ⟨checkName top δ, checkName_isName ht.1 δ⟩
  exact woodinCollapseDisplacementName_forces_output hR ht ht.1 Q S a b p q
    (collapseDisplacement_forces_preInput hR ht ht.1 Q S a b p q hκ
      (forces_checked_ordinal hR ht hδ.1 ht.1)
      (saturatedWoodinPrefixPosetName_forces hR ht hδ hP hκδ ht.1)
      (reverseInclusionOrderName_forces hR ht ht.1 Q) hp hq)

theorem saturatedHartogs_displacementName_forces_output {P R top γ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγδ : γ ∈ δ)
    (hγ : top ∈ forcingFormula P R regularCardinalFormula (standardTuple ![hartogsNumberName P R (checkName top γ)]))
    (p q : ForcingName P)
    (hp : top ∈ atomicMembership P R p.val (saturatedHartogsPosetName P R top γ δ))
    (hq : top ∈ atomicMembership P R q.val (saturatedHartogsPosetName P R top γ δ)) :
    let Q := saturatedHartogsPosetName P R top γ δ
    let S := saturatedHartogsOrderName P R top γ δ
    let f := woodinCollapseDisplacementName P R (hartogsNumberName P R (checkName top γ)) (checkName top δ) p.val q.val
    let g := ZFVP.collapseConverseName P R f
    top ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple ![Q, S, hartogsNumberName P R (checkName top γ), checkName top δ, p.val, q.val, f, g]) := by
  let Q : ForcingName P := ⟨saturatedHartogsPosetName P R top γ δ,
    saturatedHartogsPosetName_isName _ _ _ _ _⟩
  let S : ForcingName P := ⟨saturatedHartogsOrderName P R top γ δ,
    reverseInclusionOrderName_isName _ _ _⟩
  let a : ForcingName P := ⟨hartogsNumberName P R (checkName top γ), hartogsNumberName_isName _ _ _⟩
  let b : ForcingName P := ⟨checkName top δ, checkName_isName ht.1 δ⟩
  exact woodinCollapseDisplacementName_forces_output hR ht ht.1 Q S a b p q
    (collapseDisplacement_forces_preInput hR ht ht.1 Q S a b p q hγ
      (forces_checked_ordinal hR ht hδ.1 ht.1)
      (saturatedHartogsPosetName_forces hR ht hδ hP hγδ ht.1)
      (reverseInclusionOrderName_forces hR ht ht.1 Q) hp hq)

end ZFVP



