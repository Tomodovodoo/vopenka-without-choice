import ZFVP.ModelTheory.ForcingConditionalEquivalence
import ZFVP.ModelTheory.WoodinCollapseIterand
import ZFVP.ModelTheory.ForcingCheckedBounded
import ZFVP.ModelTheory.TwoStepCheckedTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCollapse_restoration_forcing_iff {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    (κ δ : ForcingName P)
    (hδ : p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![δ.val])) :
    p ∈ forcingFormula P R woodinLocalRestorationFormula (standardTuple ![κ.val, δ.val]) ↔
      p ∈ forcingFormula P R (allCheckedForcingFormula dependentChoiceBelowFormula)
        (standardTuple ![woodinCollapseName P R κ.val δ.val,
          reverseInclusionOrderName P R (woodinCollapseName P R κ.val δ.val),
          forcedEmptyName P R, δ.val]) := by
  let Q : ForcingName P := ⟨woodinCollapseName P R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩
  let S : ForcingName P := ⟨reverseInclusionOrderName P R Q.val, reverseInclusionOrderName_isName _ _ _⟩
  let t : ForcingName P := ⟨forcedEmptyName P R, forcedEmptyName_isName _ _⟩
  let φ : SetTheorySemisentence 5 :=
    (totalWoodinCollapseFormula.subst (fun i ↦ .bvar ((![0, 3, 4] : Fin 3 → Fin 5) i))).and
      ((piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 5) i))).and
        ((isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 5) i))).and
          (IsOrdinal.dfn.subst (fun i ↦ .bvar ((![4] : Fin 1 → Fin 5) i)))))
  let ψ : SetTheorySemisentence 5 := woodinLocalRestorationFormula.subst
    (fun i ↦ .bvar ((![3, 4] : Fin 2 → Fin 5) i))
  let χ : SetTheorySemisentence 5 := (allCheckedForcingFormula dependentChoiceBelowFormula).subst
    (fun i ↦ .bvar ((![0, 1, 2, 4] : Fin 4 → Fin 5) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![Q.val, S.val, t.val, κ.val, δ.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_and, mem_inter_iff, forcingFormula_rename, forcingFormula_rename,
      forcingFormula_rename, forcingFormula_rename]
    exact ⟨woodinCollapseName_forces hR htop hp κ δ,
      reverseInclusionOrderName_forces hR htop hp Q, forcedEmptyName_forces hR htop hp, hδ⟩
  have he := forcingFormula_iff_under φ ψ χ (by
    intro W _ _ _ v hv
    change (totalWoodinCollapseFormula.subst (fun i ↦ .bvar ((![0, 3, 4] : Fin 3 → Fin 5) i))).Evalb v ∧
      (piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 5) i))).Evalb v ∧
      (isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 5) i))).Evalb v ∧
      (IsOrdinal.dfn.subst (fun i ↦ .bvar ((![4] : Fin 1 → Fin 5) i))).Evalb v at hv
    have hh : v 0 = totalWoodinCollapse (v 3) (v 4) ∧ v 1 = reverseInclusionOrder (v 0) ∧
        v 2 = ∅ ∧ IsOrdinal (v 4) := by
      simpa [Semiformula.eval_substs] using hv
    let := hh.2.2.2
    have hQ : v 0 = woodinCollapse (v 3) (v 4) := hh.1.trans (totalWoodinCollapse_eq _ _)
    have hs : ψ.Evalb v ↔ IsWoodinLocalRestoration (v 3) (v 4) := by
      simp [ψ, Semiformula.eval_substs]
    have hc : χ.Evalb v ↔ ∀ p ∈ v 0,
        p ∈ forcingFormula (v 0) (v 1) dependentChoiceBelowFormula
          (standardTuple ![checkName (v 2) (v 4)]) := by
      simp [χ, Semiformula.eval_substs, eval_allCheckedForcingFormula]
    rw [hs, hc]
    rw [hh.2.1, hQ, hh.2.2.1]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨inferInstance, h⟩⟩)
    hR htop hp ![Q, S, t, κ, δ] hφ
  dsimp only [ψ, χ] at he
  rw [forcingFormula_rename, forcingFormula_rename] at he
  exact he

end ZFVP
