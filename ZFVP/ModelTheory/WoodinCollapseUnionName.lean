import ZFVP.ModelTheory.WoodinCollapseName
import ZFVP.SetTheory.ForcingUnionClosure
import ZFVP.ModelTheory.ForcingCheckedBounded
import ZFVP.SetTheory.AtomicCheckNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCollapseName_forces_unionClosedAt {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    (κ δ α : ForcingName P)
    (hκ : p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![δ.val]))
    (hDC : p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![α.val]))
    (hακ : p ∈ forcingFormula P R nameMemberFormula (standardTuple ![α.val, κ.val])) :
    p ∈ forcingFormula P R forcingUnionClosedAtFormula
      (standardTuple ![woodinCollapseName P R κ.val δ.val, α.val]) := by
  let Q : ForcingName P := ⟨woodinCollapseName P R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩
  let φ : SetTheorySemisentence 4 :=
    (totalWoodinCollapseFormula.subst (fun i ↦ .bvar ((![0, 1, 2] : Fin 3 → Fin 4) i))).and
      ((regularCardinalFormula.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 4) i))).and
        ((IsOrdinal.dfn.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 4) i))).and
          ((dependentChoiceAtFormula.subst (fun i ↦ .bvar ((![3] : Fin 1 → Fin 4) i))).and
            (nameMemberFormula.subst (fun i ↦ .bvar ((![3, 1] : Fin 2 → Fin 4) i))))))
  let ψ : SetTheorySemisentence 4 := forcingUnionClosedAtFormula.subst
    (fun i ↦ .bvar ((![0, 3] : Fin 2 → Fin 4) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![Q.val, κ.val, δ.val, α.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_rename, forcingFormula_rename, forcingFormula_rename,
      forcingFormula_rename, forcingFormula_rename]
    exact ⟨woodinCollapseName_forces hR htop hp κ δ, hκ, hδ, hDC, hακ⟩
  have hψ := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change (totalWoodinCollapseFormula.subst (fun i ↦ .bvar ((![0, 1, 2] : Fin 3 → Fin 4) i))).Evalb v ∧
      (regularCardinalFormula.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 4) i))).Evalb v ∧
      (IsOrdinal.dfn.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 4) i))).Evalb v ∧
      (dependentChoiceAtFormula.subst (fun i ↦ .bvar ((![3] : Fin 1 → Fin 4) i))).Evalb v ∧
      (nameMemberFormula.subst (fun i ↦ .bvar ((![3, 1] : Fin 2 → Fin 4) i))).Evalb v at hv
    have hh : v 0 = totalWoodinCollapse (v 1) (v 2) ∧ IsRegularCardinal (v 1) ∧
        IsOrdinal (v 2) ∧ InternalDependentChoiceAt (v 3) ∧ v 3 ∈ v 1 := by
      simpa [φ, Semiformula.eval_substs, nameMemberFormula] using hv
    let := hh.2.2.1
    have hc : IsForcingUnionClosedAt (v 0) (v 3) := by
      rw [hh.1, totalWoodinCollapse_eq]
      exact woodinCollapse_unionClosedAt hh.2.1 hh.2.2.2.2 hh.2.2.2.1
    simpa [ψ, Semiformula.eval_substs] using hc) hR htop hp ![Q, κ, δ, α] hφ
  change p ∈ forcingFormula P R (forcingUnionClosedAtFormula.subst
    (fun i ↦ .bvar ((![0, 3] : Fin 2 → Fin 4) i))) (standardTuple ![Q.val, κ.val, δ.val, α.val]) at hψ
  rw [forcingFormula_rename] at hψ
  exact hψ

theorem woodinPrefix_forces_unionClosedAt {P R one κ δ α p : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P) (hα : α ∈ κ)
    (hκ : p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hDC : p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![checkName one α])) :
    p ∈ forcingFormula P R forcingUnionClosedAtFormula
      (standardTuple ![woodinCollapseName P R (checkName one κ) (checkName one δ), checkName one α]) := by
  apply woodinCollapseName_forces_unionClosedAt hR htop hp
    ⟨checkName one κ, checkName_isName htop.1 _⟩ ⟨checkName one δ, checkName_isName htop.1 _⟩
    ⟨checkName one α, checkName_isName htop.1 _⟩ hκ (forces_checked_ordinal hR htop inferInstance hp) hDC
  rw [forcingFormula_nameMember]
  exact (mem_atomicMembership_checkName_iff hR htop _ _ _).mpr ⟨hp, hα⟩

end ZFVP
