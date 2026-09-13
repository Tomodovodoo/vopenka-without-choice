import ZFVP.ModelTheory.WoodinCollapseName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCollapse_top_forced_of_ordinal {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (κ δ : ForcingName P)
    (hκ : p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![δ.val])) :
    p ∈ forcingFormula P R forcingTopFormula
      (standardTuple ![woodinCollapseName P R κ.val δ.val,
        reverseInclusionOrderName P R (woodinCollapseName P R κ.val δ.val), forcedEmptyName P R]) := by
  let Q : ForcingName P := ⟨woodinCollapseName P R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩
  let S : ForcingName P := ⟨reverseInclusionOrderName P R Q.val, reverseInclusionOrderName_isName _ _ _⟩
  let t : ForcingName P := ⟨forcedEmptyName P R, forcedEmptyName_isName _ _⟩
  let φ : SetTheorySemisentence 5 :=
    (totalWoodinCollapseFormula.subst (fun i ↦ .bvar ((![0, 3, 4] : Fin 3 → Fin 5) i))).and
      ((piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 5) i))).and
        ((isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 5) i))).and
          ((regularCardinalFormula.subst (fun i ↦ .bvar ((![3] : Fin 1 → Fin 5) i))).and
            (IsOrdinal.dfn.subst (fun i ↦ .bvar ((![4] : Fin 1 → Fin 5) i))))))
  let ψ : SetTheorySemisentence 5 := forcingTopFormula.subst
    (fun i ↦ .bvar ((![0, 1, 2] : Fin 3 → Fin 5) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![Q.val, S.val, t.val, κ.val, δ.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_rename, forcingFormula_rename, forcingFormula_rename, forcingFormula_rename,
      forcingFormula_rename]
    exact ⟨woodinCollapseName_forces hR htop hp κ δ,
      reverseInclusionOrderName_forces hR htop hp Q, forcedEmptyName_forces hR htop hp, hκ, hδ⟩
  have hψ := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change (totalWoodinCollapseFormula.subst (fun i ↦ .bvar ((![0, 3, 4] : Fin 3 → Fin 5) i))).Evalb v ∧
      (piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 5) i))).Evalb v ∧
      (isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 5) i))).Evalb v ∧
      (regularCardinalFormula.subst (fun i ↦ .bvar ((![3] : Fin 1 → Fin 5) i))).Evalb v ∧
      (IsOrdinal.dfn.subst (fun i ↦ .bvar ((![4] : Fin 1 → Fin 5) i))).Evalb v at hv
    have hh : v 0 = totalWoodinCollapse (v 3) (v 4) ∧ v 1 = reverseInclusionOrder (v 0) ∧
        v 2 = ∅ ∧ IsRegularCardinal (v 3) ∧ IsOrdinal (v 4) := by
      simpa [Semiformula.eval_substs] using hv
    let := hh.2.2.2.2
    have hz : (∅ : W) ∈ v 3 := hh.2.2.2.1.2.1 ∅ (by simp)
    have ht : IsForcingTop (v 0) (v 1) (v 2) := by
      rw [hh.2.1, hh.1, hh.2.2.1, totalWoodinCollapse_eq]
      exact woodinCollapse_top hz (v 4)
    simpa [ψ, Semiformula.eval_substs] using ht)
    hR htop hp ![Q, S, t, κ, δ] hφ
  change p ∈ forcingFormula P R (forcingTopFormula.subst
    (fun i ↦ .bvar ((![0, 1, 2] : Fin 3 → Fin 5) i)))
    (standardTuple ![Q.val, S.val, t.val, κ.val, δ.val]) at hψ
  rw [forcingFormula_rename] at hψ
  exact hψ

theorem woodinCollapse_iterand_of_ordinal {P R one : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (κ δ : ForcingName P)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : ∀ p ∈ P, p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![δ.val])) :
    IsForcingIterand P R (woodinCollapseName P R κ.val δ.val)
      (reverseInclusionOrderName P R (woodinCollapseName P R κ.val δ.val)) (forcedEmptyName P R) where
  posetName := woodinCollapseName_isName _ _ _ _
  orderName := reverseInclusionOrderName_isName _ _ _
  topName := forcedEmptyName_isName _ _
  preorder := fun _p hp ↦ reverseInclusionOrderName_preorder hR htop hp
    ⟨woodinCollapseName P R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩
  top := fun p hp ↦ woodinCollapse_top_forced_of_ordinal hR htop hp κ δ (hκ p hp) (hδ p hp)

theorem woodinCollapse_top_forced {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (κ δ : ForcingName P)
    (hκ : p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : p ∈ forcingFormula P R woodinLocalRestorationFormula (standardTuple ![κ.val, δ.val])) :
    p ∈ forcingFormula P R forcingTopFormula
      (standardTuple ![woodinCollapseName P R κ.val δ.val,
        reverseInclusionOrderName P R (woodinCollapseName P R κ.val δ.val), forcedEmptyName P R]) := by
  let ψ : SetTheorySemisentence 2 := IsOrdinal.dfn.subst
    (fun i ↦ .bvar ((![1] : Fin 1 → Fin 2) i))
  have ho := forcingFormula_entailment woodinLocalRestorationFormula ψ (by
    intro W _ _ _ v hv
    have hh : IsWoodinLocalRestoration (v 0) (v 1) := (Defined.eval_iff v).mp hv
    simpa [ψ, Semiformula.eval_substs] using hh.1) hR htop hp ![κ, δ] hδ
  dsimp only [ψ] at ho
  rw [forcingFormula_rename] at ho
  exact woodinCollapse_top_forced_of_ordinal hR htop hp κ δ hκ ho

theorem woodinCollapse_iterand {P R one : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (κ δ : ForcingName P)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : ∀ p ∈ P, p ∈ forcingFormula P R woodinLocalRestorationFormula (standardTuple ![κ.val, δ.val])) :
    IsForcingIterand P R (woodinCollapseName P R κ.val δ.val)
      (reverseInclusionOrderName P R (woodinCollapseName P R κ.val δ.val)) (forcedEmptyName P R) where
  posetName := woodinCollapseName_isName _ _ _ _
  orderName := reverseInclusionOrderName_isName _ _ _
  topName := forcedEmptyName_isName _ _
  preorder := fun _p hp ↦ reverseInclusionOrderName_preorder hR htop hp
    ⟨woodinCollapseName P R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩
  top := fun p hp ↦ woodinCollapse_top_forced hR htop hp κ δ (hκ p hp) (hδ p hp)

end ZFVP
