import ZFVP.ModelTheory.ForcingRankDCThreshold
import ZFVP.ModelTheory.RankDCBelowAgreement
import ZFVP.ModelTheory.ForcingInaccessibleRankTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.rankDCBelow_classForcing_iff (A : ForcingContext V)
    {ξ γ : V} (hξ : IsChoicelessInaccessible ξ) (hP : A.P ∈ hierarchy ξ)
    (hn : checkName A.one γ ∈ hierarchy ξ) {η : A.Model}
    (ht : IsRankDCThreshold (A.check γ) η) (hη : η ∈ A.check ξ) :
    GenericMeets A.G (classForcingFormula A.P A.R (IsLowRankForcingName A.P ξ)
      (by definability) dependentChoiceBelowFormula (standardTuple ![checkName A.one γ])) ↔
    GenericMeets A.G (forcingFormula A.P A.R dependentChoiceBelowFormula
      (standardTuple ![checkName A.one γ])) := by
  let := hξ.1
  let v : Fin 1 → ForcingName A.P := ![⟨checkName A.one γ, checkName_isName A.top.1 γ⟩]
  have hv : ∀ i, (v i).val ∈ hierarchy ξ := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hn
  have he := A.rankName_formula_truth_of_inaccessible hξ hP dependentChoiceBelowFormula v hv
  have hi := A.check_inaccessible_of_small hξ hP
  let := rankDomain_nonempty hi.2.1
  let := hi.rankCriterion.models_zf
  have hγ : A.check γ ∈ hierarchy (A.check ξ) := A.ofName_mem_checked_hierarchy (v 0) hn
  have hd := ht.dependentChoiceBelow_iff hη hi hγ
  have hnames : (fun i ↦ (v i).val) = ![checkName A.one γ] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  have hvalues : (fun i ↦ A.ofName (v i)) = ![A.check γ] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  have hrank : (show Fin 1 → SetDomain (hierarchy (A.check ξ)) from fun i ↦
      ⟨A.ofName (v i), (A.mem_checked_hierarchy_iff_low_name_of_inaccessible hξ hP _).mpr
        ⟨v i, hv i, rfl⟩⟩) =
      (show Fin 1 → SetDomain (hierarchy (A.check ξ)) from ![⟨A.check γ, hγ⟩]) := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [hnames, hrank] at he
  have hf := A.formula_truth dependentChoiceBelowFormula v
  rw [hnames, hvalues] at hf
  exact he.symm.trans (hd.trans hf)

end ZFVP
