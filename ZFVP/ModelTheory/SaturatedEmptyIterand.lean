import ZFVP.ModelTheory.WoodinCollapseEmptyIterand
import ZFVP.ModelTheory.ForcingSaturatedName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem reverseInclusionOrderName_empty_top {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    (Q : ForcingName P) (hm : p ∈ atomicMembership P R ∅ Q.val) :
    p ∈ forcingFormula P R forcingTopFormula
      (standardTuple ![Q.val, reverseInclusionOrderName P R Q.val, ∅]) := by
  let S : ForcingName P := ⟨reverseInclusionOrderName P R Q.val, reverseInclusionOrderName_isName _ _ _⟩
  let t : ForcingName P := ⟨∅, empty_forcingName P⟩
  let φ : SetTheorySemisentence 3 :=
    (piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 3) i))).and
      ((isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 3) i))).and
        (nameMemberFormula.subst (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 3) i))))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![Q.val, S.val, t.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_rename, forcingFormula_rename, forcingFormula_rename]
    exact ⟨reverseInclusionOrderName_forces hR htop hp Q, emptyName_forces hR htop hp, (forcingFormula_nameMember P R ∅ Q.val).symm ▸ hm⟩
  exact forcingFormula_entailment φ forcingTopFormula (by
    intro W _ _ _ v hv
    change (piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 3) i))).Evalb v ∧
      (isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 3) i))).Evalb v ∧
      (nameMemberFormula.subst (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 3) i))).Evalb v at hv
    have hh : v 1 = reverseInclusionOrder (v 0) ∧ v 2 = ∅ ∧ v 2 ∈ v 0 := by
      simpa [φ, Semiformula.eval_substs, nameMemberFormula] using hv
    apply (Defined.eval_iff v).mpr
    rw [hh.1, hh.2.1]
    refine ⟨hh.2.1 ▸ hh.2.2, ?_⟩
    intro q hq
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hh.2.1 ▸ hh.2.2, by simp⟩)
    hR htop hp ![Q, S, t] hφ

theorem saturatedName_empty_iterand {P R one U : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (Q : ForcingName P) (hU : (∅ : V) ∈ U)
    (hm : ∀ p ∈ P, p ∈ atomicMembership P R ∅ Q.val) :
    IsForcingIterand P R (forcingSaturatedName P R U Q.val)
      (reverseInclusionOrderName P R (forcingSaturatedName P R U Q.val)) ∅ where
  posetName := forcingSaturatedName_isName _ _ _ _
  orderName := reverseInclusionOrderName_isName _ _ _
  topName := empty_forcingName P
  preorder := fun _ hp ↦ reverseInclusionOrderName_preorder hR htop hp
    ⟨forcingSaturatedName P R U Q.val, forcingSaturatedName_isName _ _ _ _⟩
  top := fun p hp ↦ reverseInclusionOrderName_empty_top hR htop hp
    ⟨forcingSaturatedName P R U Q.val, forcingSaturatedName_isName _ _ _ _⟩
    (forcingSaturatedName_forces_member hR hU hp (empty_forcingName P) (hm p hp))

theorem woodinCollapseName_forces_empty_member {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    (κ δ : ForcingName P)
    (hκ : p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![δ.val])) :
    p ∈ atomicMembership P R ∅ (woodinCollapseName P R κ.val δ.val) := by
  let Q : ForcingName P := ⟨woodinCollapseName P R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩
  let S : ForcingName P := ⟨reverseInclusionOrderName P R Q.val, reverseInclusionOrderName_isName _ _ _⟩
  let t : ForcingName P := ⟨∅, empty_forcingName P⟩
  have hh := woodinCollapse_empty_top_forced_of_ordinal hR htop hp κ δ hκ hδ
  let ψ : SetTheorySemisentence 3 := nameMemberFormula.subst
    (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 3) i))
  have hm := forcingFormula_entailment forcingTopFormula ψ (by
    intro W _ _ _ v hv
    have ht : IsForcingTop (v 0) (v 1) (v 2) := (Defined.eval_iff v).mp hv
    simpa [ψ, nameMemberFormula, Semiformula.eval_substs] using ht.1)
    hR htop hp ![Q, S, t] hh
  dsimp only [ψ] at hm
  rw [forcingFormula_rename] at hm
  change p ∈ forcingFormula P R nameMemberFormula (standardTuple ![∅, Q.val]) at hm
  rwa [forcingFormula_nameMember] at hm

theorem saturatedWoodinCollapse_empty_iterand {P R one U : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (κ δ : ForcingName P) (hU : (∅ : V) ∈ U)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : ∀ p ∈ P, p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![δ.val])) :
    IsForcingIterand P R (forcingSaturatedName P R U (woodinCollapseName P R κ.val δ.val))
      (reverseInclusionOrderName P R (forcingSaturatedName P R U (woodinCollapseName P R κ.val δ.val))) ∅ :=
  saturatedName_empty_iterand hR htop
    ⟨woodinCollapseName P R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩ hU
    (fun p hp ↦ woodinCollapseName_forces_empty_member hR htop hp κ δ (hκ p hp) (hδ p hp))

end ZFVP



