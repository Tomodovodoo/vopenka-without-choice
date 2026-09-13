import ZFVP.ModelTheory.ForcingRankInternalNames
import ZFVP.ModelTheory.TransitiveZFWoodinCollapse
import ZFVP.ModelTheory.WoodinPrefixNameFormulas
import ZFVP.ModelTheory.ForcingSmallInaccessible

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V) {ξ : V} [IsOrdinal ξ]
  [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankInternalValue_check_val (hξ : IsChoicelessInaccessible ξ)
    (P one x : SetDomain (hierarchy ξ)) (hP : P.val = A.P) (ho : one.val = A.one)
    (ht : one ∈ P) :
    (A.rankInternalValue hξ P hP ⟨checkName one x, checkName_isName ht x⟩).val = A.check x.val := by
  let := hierarchy_transitive ξ
  change A.ofName ⟨(checkName one x).val, _⟩ =
    A.ofName ⟨checkName A.one x.val, checkName_isName A.top.1 x.val⟩
  apply congrArg A.ofName
  apply Subtype.ext
  rw [TransitiveZF.checkName_val, ho]

theorem rankInternalCollapseName_value (hξ : IsChoicelessInaccessible ξ)
    (P R one : SetDomain (hierarchy ξ)) (hP : P.val = A.P) (hR : R.val = A.R)
    (ho : one.val = A.one) (κ γ : ForcingName P) :
    A.ofName (A.rankInternalName P hP
      ⟨woodinCollapseName P R κ.val γ.val, woodinCollapseName_isName _ _ _ _⟩) =
      totalWoodinCollapse (A.ofName (A.rankInternalName P hP κ))
        (A.ofName (A.rankInternalName P hP γ)) := by
  let := hierarchy_transitive ξ
  have hord : IsForcingPreorder P R := (TransitiveZF.forcingPreorder_iff (hierarchy ξ) P R).mpr
    (by simpa only [hP, hR] using A.order)
  have htop : IsForcingTop P R one := (TransitiveZF.forcingTop_iff (hierarchy ξ) P R one).mpr
    (by simpa only [hP, hR, ho] using A.top)
  let Q : ForcingName P :=
    ⟨woodinCollapseName P R κ.val γ.val, woodinCollapseName_isName _ _ _ _⟩
  let v : Fin 3 → ForcingName P := ![Q, κ, γ]
  have hf : ∀ p ∈ P, p ∈ forcingFormula P R totalWoodinCollapseFormula
      (standardTuple (fun i ↦ (v i).val)) := by
    intro p hp
    have hn : (fun i ↦ (v i).val) = ![Q.val, κ.val, γ.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
    rw [hn]
    exact woodinCollapseName_forces hord htop hp κ γ
  have hi := A.check_inaccessible_of_small hξ (hP ▸ P.property)
  let := hi.1
  let := rankDomain_nonempty hi.2.1
  let := hi.rankCriterion.models_zf
  let := hierarchy_transitive (A.check ξ)
  let w : Fin 3 → SetDomain (hierarchy (A.check ξ)) := fun i ↦ A.rankInternalValue hξ P hP (v i)
  have he : w 0 = totalWoodinCollapse (w 1) (w 2) :=
    (Defined.eval_iff (φ := totalWoodinCollapseFormula) w).mp
      (A.rankInternalValue_eval_of_forces hξ P R hP hR totalWoodinCollapseFormula v hf)
  have hv := congrArg Subtype.val he
  change (w 0).val = totalWoodinCollapse (w 1).val (w 2).val
  classical
  by_cases hd : IsOrdinal (w 2)
  · let := hd
    have hdv := (TransitiveZF.ordinal_iff (hierarchy (A.check ξ)) (w 2)).mp hd
    let := hdv
    rw [totalWoodinCollapse_eq,
      rank_woodinCollapse_val (fun _ hb ↦ regularCardinal_succ_closed hi.regular hb) _ _ hd] at hv
    simpa only [totalWoodinCollapse_eq] using hv
  · have hdv : ¬ IsOrdinal (w 2).val := fun h ↦ hd
      ((TransitiveZF.ordinal_iff (hierarchy (A.check ξ)) (w 2)).mpr h)
    simp only [totalWoodinCollapse, hd, ↓reduceIte, TransitiveZF.empty_val] at hv
    change (w 0).val = totalWoodinCollapse (w 1).val (w 2).val
    simpa only [totalWoodinCollapse, hdv, ↓reduceIte] using hv

theorem rankInternalCollapse_value (hξ : IsChoicelessInaccessible ξ)
    (P R one κ γ : SetDomain (hierarchy ξ)) (hP : P.val = A.P) (hR : R.val = A.R)
    (ho : one.val = A.one) (hγ : IsOrdinal γ) :
    A.ofName (A.rankInternalName P hP
      ⟨woodinPrefixPosetName P R one κ γ, woodinCollapseName_isName _ _ _ _⟩) =
      woodinCollapse (A.check κ.val) (A.check γ.val) := by
  let := hierarchy_transitive ξ
  have hord : IsForcingPreorder P R := (TransitiveZF.forcingPreorder_iff (hierarchy ξ) P R).mpr
    (by simpa only [hP, hR] using A.order)
  have htop : IsForcingTop P R one := (TransitiveZF.forcingTop_iff (hierarchy ξ) P R one).mpr
    (by simpa only [hP, hR, ho] using A.top)
  let cκ : ForcingName P := ⟨checkName one κ, checkName_isName htop.1 κ⟩
  let cγ : ForcingName P := ⟨checkName one γ, checkName_isName htop.1 γ⟩
  let Q : ForcingName P := ⟨woodinPrefixPosetName P R one κ γ, woodinCollapseName_isName _ _ _ _⟩
  let v : Fin 3 → ForcingName P := ![Q, cκ, cγ]
  have hf : ∀ p ∈ P, p ∈ forcingFormula P R totalWoodinCollapseFormula
      (standardTuple (fun i ↦ (v i).val)) := by
    intro p hp
    have hn : (fun i ↦ (v i).val) = ![Q.val, cκ.val, cγ.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
    rw [hn]
    exact woodinCollapseName_forces hord htop hp cκ cγ
  have hi := A.check_inaccessible_of_small hξ (hP ▸ P.property)
  let := hi.1
  let := rankDomain_nonempty hi.2.1
  let := hi.rankCriterion.models_zf
  let := hierarchy_transitive (A.check ξ)
  let w : Fin 3 → SetDomain (hierarchy (A.check ξ)) := fun i ↦ A.rankInternalValue hξ P hP (v i)
  have he : w 0 = totalWoodinCollapse (w 1) (w 2) :=
    (Defined.eval_iff (φ := totalWoodinCollapseFormula) w).mp
      (A.rankInternalValue_eval_of_forces hξ P R hP hR totalWoodinCollapseFormula v hf)
  have hk : (w 1).val = A.check κ.val := A.rankInternalValue_check_val hξ P one κ hP ho htop.1
  have hg : (w 2).val = A.check γ.val := A.rankInternalValue_check_val hξ P one γ hP ho htop.1
  let := (TransitiveZF.ordinal_iff (hierarchy ξ) γ).mp hγ
  have hd : IsOrdinal (w 2) := (TransitiveZF.ordinal_iff (hierarchy (A.check ξ)) (w 2)).mpr
    (hg ▸ inferInstance)
  let := hd
  rw [totalWoodinCollapse_eq] at he
  have hv := congrArg Subtype.val he
  rw [rank_woodinCollapse_val (fun _ hb ↦ regularCardinal_succ_closed hi.regular hb) _ _ hd, hk, hg] at hv
  exact hv

end ForcingContext
end ZFVP
