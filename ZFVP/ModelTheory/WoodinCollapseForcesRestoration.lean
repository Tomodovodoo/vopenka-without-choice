import ZFVP.ModelTheory.WoodinCollapseRestorationBelow

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def dependentChoiceBelowFormula : SetTheorySemisentence 1 :=
  “κ. ∀ α ∈ κ, !dependentChoiceAtFormula α”

def woodinCollapseSetFormula : SetTheorySemisentence 3 :=
  f“P κ δ. !IsOrdinal.dfn δ ∧ ∀ p, p ∈ P ↔
    !sigmaOneWoodinConditionFormula p κ δ (!hierarchyFormula δ)”

def woodinCollapseRestorationFormula : SetTheorySemisentence 5 :=
  f“κ δ P R p. !regularCardinalFormula κ ∧ !regularCardinalFormula δ ∧
    !highCriticalWoodinFormula δ ∧ κ ∈ δ ∧ !dependentChoiceBelowFormula κ ∧
    !woodinCollapseSetFormula P κ δ ∧ !piOneReverseInclusionOrderFormula R P ∧ p ∈ P →
      !(checkedUnaryForcingFormula dependentChoiceBelowFormula) P R (!isEmpty) p δ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance dependentChoiceBelowFormula_defined :
    Defined (fun v : Fin 1 → V ↦ ∀ α ∈ v 0, InternalDependentChoiceAt α) dependentChoiceBelowFormula :=
  ⟨fun v ↦ by simp [dependentChoiceBelowFormula]⟩

theorem eval_woodinCollapseSetFormula (P κ δ : V) :
    woodinCollapseSetFormula.Evalb ![P, κ, δ] ↔ IsOrdinal δ ∧ P = woodinCollapse κ δ := by
  simp [woodinCollapseSetFormula]
  intro hδ
  let := hδ
  simp only [eval_sigmaOneWoodinConditionFormula]
  exact mem_ext_iff.symm

instance woodinCollapseSetFormula_defined :
    Defined (fun v : Fin 3 → V ↦ IsOrdinal (v 2) ∧ v 0 = woodinCollapse (v 1) (v 2)) woodinCollapseSetFormula := by
  refine ⟨fun v ↦ ?_⟩
  have hv : ![v 0, v 1, v 2] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
  rw [← hv]
  exact eval_woodinCollapseSetFormula _ _ _

theorem eval_woodinCollapseRestorationFormula (v : Fin 5 → V) :
    woodinCollapseRestorationFormula.Evalb v ↔
      (IsRegularCardinal (v 0) → IsRegularCardinal (v 1) → HasHighCriticalWoodinWitnesses (v 1) →
        v 0 ∈ v 1 → (∀ α ∈ v 0, InternalDependentChoiceAt α) →
        IsOrdinal (v 1) → v 2 = woodinCollapse (v 0) (v 1) → v 3 = reverseInclusionOrder (v 2) →
        v 4 ∈ v 2 → v 4 ∈ forcingFormula (v 2) (v 3) dependentChoiceBelowFormula
          (standardTuple ![checkName ∅ (v 1)])) := by
  simp [woodinCollapseRestorationFormula, eval_piOneReverseInclusionOrderFormula]

set_option maxHeartbeats 1000000 in
theorem woodinCollapse_forces_restoration_countable [Countable V] {κ δ p : V}
    (hκ : IsRegularCardinal κ) (hδreg : IsRegularCardinal δ)
    (hδ : HasHighCriticalWoodinWitnesses δ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) (hp : p ∈ woodinCollapse κ δ) :
    p ∈ forcingFormula (woodinCollapse κ δ) (woodinCollapseOrder κ δ) dependentChoiceBelowFormula
      (standardTuple ![checkName ∅ δ]) := by
  let c : ForcingName (woodinCollapse κ δ) :=
    ⟨checkName ∅ δ, checkName_isName (empty_mem_woodinCollapse (hκ.2.1 ∅ (by simp)) δ) δ⟩
  apply forcingFormula_of_all_generics (woodinCollapse_poset κ δ).1
    (woodinCollapse_top (hκ.2.1 ∅ (by simp)) δ) hp dependentChoiceBelowFormula ![c]
  intro G hG _
  exact (Defined.eval_iff _).mpr (WoodinCollapseModel.dependentChoice_below_restored hκ hδreg hδ hκδ hDC hG)

set_option maxHeartbeats 1000000 in
theorem woodinCollapse_forces_restoration {κ δ p : V}
    (hκ : IsRegularCardinal κ) (hδreg : IsRegularCardinal δ)
    (hδ : HasHighCriticalWoodinWitnesses δ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) (hp : p ∈ woodinCollapse κ δ) :
    p ∈ forcingFormula (woodinCollapse κ δ) (woodinCollapseOrder κ δ) dependentChoiceBelowFormula
      (standardTuple ![checkName ∅ δ]) := by
  have hh := eval_of_countable_zf woodinCollapseRestorationFormula (by
    intro W _ _ _ _ v
    apply (eval_woodinCollapseRestorationFormula v).mpr
    intro hκ hδreg hδ hκδ hDC _ hP hR hp
    rw [hR, hP] at *
    exact woodinCollapse_forces_restoration_countable hκ hδreg hδ hκδ hDC hp)
    ![κ, δ, woodinCollapse κ δ, woodinCollapseOrder κ δ, p]
  exact (eval_woodinCollapseRestorationFormula _).mp hh hκ hδreg hδ hκδ hDC hδreg.1.1 rfl rfl hp

end ZFVP
