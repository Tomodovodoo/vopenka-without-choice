import ZFVP.ModelTheory.TransitiveZFFormulaForcing
import ZFVP.ModelTheory.TransitiveZFInaccessible
import ZFVP.ModelTheory.ForcingRankTruth
import ZFVP.SetTheory.WoodinPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_woodinPrefixCutoff_iff (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (P R one κ γ : SetDomain (hierarchy ξ)) :
    IsWoodinPrefixCutoff P R one κ γ ↔ κ.val ∈ γ.val ∧ IsChoicelessInaccessible γ.val ∧
      ∀ p ∈ P.val, p ∈ classForcingFormula P.val R.val
        (IsLowRankForcingName P.val ξ) (by definability) woodinLocalRestorationFormula
        (standardTuple ![checkName one.val κ.val, checkName one.val γ.val]) := by
  let := hierarchy_transitive ξ
  have he := TransitiveZF.forcingFormula_standardTuple_val (hierarchy ξ) P R
    woodinLocalRestorationFormula ![checkName one κ, checkName one γ]
  have hv : (fun i : Fin 2 ↦ ((![checkName one κ, checkName one γ] :
      Fin 2 → SetDomain (hierarchy ξ)) i).val) = ![checkName one.val κ.val, checkName one.val γ.val] := by
    funext i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun z ↦ Fin.elim0 z) j) i <;>
      simp [TransitiveZF.checkName_val]
  rw [hv] at he
  have hall := TransitiveZF.forall_mem_val_iff (hierarchy ξ) P
    (fun p ↦ p ∈ forcingFormula P R woodinLocalRestorationFormula
      (standardTuple ![checkName one κ, checkName one γ]))
    (fun p ↦ p ∈ (forcingFormula P R woodinLocalRestorationFormula
      (standardTuple ![checkName one κ, checkName one γ])).val) (fun _ ↦ Iff.rfl)
  rw [he] at hall
  unfold IsWoodinPrefixCutoff
  exact and_congr Iff.rfl (and_congr (rank_choicelessInaccessible_iff hs γ) hall)

theorem rank_woodinPrefixCutoff_iff_of_forcing_eq (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (P R one κ γ : SetDomain (hierarchy ξ))
    (he : classForcingFormula P.val R.val (IsLowRankForcingName P.val ξ) (by definability)
      woodinLocalRestorationFormula (standardTuple ![checkName one.val κ.val, checkName one.val γ.val]) =
      forcingFormula P.val R.val woodinLocalRestorationFormula
        (standardTuple ![checkName one.val κ.val, checkName one.val γ.val])) :
    IsWoodinPrefixCutoff P R one κ γ ↔ IsWoodinPrefixCutoff P.val R.val one.val κ.val γ.val := by
  rw [rank_woodinPrefixCutoff_iff hs P R one κ γ, he]
  rfl

end ZFVP
