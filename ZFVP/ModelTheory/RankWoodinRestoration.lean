import ZFVP.ModelTheory.TransitiveZFWoodinCollapse
import ZFVP.ModelTheory.TransitiveZFFormulaForcing
import ZFVP.SetTheory.WoodinPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_woodinLocalRestoration_iff (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (κ δ : SetDomain (hierarchy ξ)) (hδ : IsOrdinal δ) :
    IsWoodinLocalRestoration κ δ ↔
      ∀ p ∈ woodinCollapse κ.val δ.val,
        p ∈ classForcingFormula (woodinCollapse κ.val δ.val) (woodinCollapseOrder κ.val δ.val)
          (fun x ↦ x ∈ hierarchy ξ ∧ IsForcingName (woodinCollapse κ.val δ.val) x)
          (by definability) dependentChoiceBelowFormula (standardTuple ![checkName ∅ δ.val]) := by
  let := hierarchy_transitive ξ
  have he := TransitiveZF.forcingFormula_standardTuple_val (hierarchy ξ)
    (woodinCollapse κ δ) (woodinCollapseOrder κ δ) dependentChoiceBelowFormula ![checkName ∅ δ]
  have hv : (fun i : Fin 1 ↦ ((![checkName ∅ δ] : Fin 1 → SetDomain (hierarchy ξ)) i).val) =
      ![checkName ∅ δ.val] := by
    funext i
    refine Fin.cases ?_ (fun j ↦ Fin.elim0 j) i
    simp [TransitiveZF.checkName_val, TransitiveZF.empty_val]
  rw [hv] at he
  have he' : (forcingFormula (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      dependentChoiceBelowFormula (standardTuple ![checkName ∅ δ])).val =
      classForcingFormula (woodinCollapse κ.val δ.val) (woodinCollapseOrder κ.val δ.val)
        (fun x ↦ x ∈ hierarchy ξ ∧ IsForcingName (woodinCollapse κ.val δ.val) x)
        (by definability) dependentChoiceBelowFormula (standardTuple ![checkName ∅ δ.val]) := by
    simpa only [rank_woodinCollapse_val hs κ δ hδ, rank_woodinCollapseOrder_val hs κ δ hδ,
      Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
      TransitiveZF.checkName_val, TransitiveZF.empty_val] using he
  unfold IsWoodinLocalRestoration
  rw [and_iff_right hδ]
  have hall := TransitiveZF.forall_mem_val_iff (hierarchy ξ) (woodinCollapse κ δ)
    (fun p ↦ p ∈ forcingFormula (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      dependentChoiceBelowFormula (standardTuple ![checkName ∅ δ]))
    (fun p ↦ p ∈ (forcingFormula (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      dependentChoiceBelowFormula (standardTuple ![checkName ∅ δ])).val) (fun _ ↦ Iff.rfl)
  rw [rank_woodinCollapse_val hs κ δ hδ, he'] at hall
  exact hall

end ZFVP
