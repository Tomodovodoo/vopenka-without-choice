import ZFVP.ModelTheory.RankHartogs
import ZFVP.ModelTheory.RankInternalCollapseName
import ZFVP.ModelTheory.ForcingHartogsName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V) {ξ : V} [IsOrdinal ξ]
  [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankInternalHartogsName_value (hξ : IsChoicelessInaccessible ξ)
    (P R one : SetDomain (hierarchy ξ)) (hP : P.val = A.P) (hR : R.val = A.R)
    (ho : one.val = A.one) (τ : ForcingName P) :
    A.ofName (A.rankInternalName P hP
      ⟨hartogsNumberName P R τ.val, hartogsNumberName_isName _ _ _⟩) =
      hartogsNumber (A.ofName (A.rankInternalName P hP τ)) := by
  let := hierarchy_transitive ξ
  have hord : IsForcingPreorder P R := (TransitiveZF.forcingPreorder_iff (hierarchy ξ) P R).mpr
    (by simpa only [hP, hR] using A.order)
  have htop : IsForcingTop P R one := (TransitiveZF.forcingTop_iff (hierarchy ξ) P R one).mpr
    (by simpa only [hP, hR, ho] using A.top)
  let H : ForcingName P := ⟨hartogsNumberName P R τ.val, hartogsNumberName_isName _ _ _⟩
  let v : Fin 2 → ForcingName P := ![H, τ]
  have hf : ∀ p ∈ P, p ∈ forcingFormula P R hartogsNumberFormula
      (standardTuple (fun i ↦ (v i).val)) := by
    intro p hp
    have hn : (fun i ↦ (v i).val) = ![H.val, τ.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    rw [hn]
    exact hartogsNumberName_forces hord htop hp τ
  have hi := A.check_inaccessible_of_small hξ (hP ▸ P.property)
  let := hi.1
  let := rankDomain_nonempty hi.2.1
  let := hi.rankCriterion.models_zf
  let := hierarchy_transitive (A.check ξ)
  let w : Fin 2 → SetDomain (hierarchy (A.check ξ)) := fun i ↦ A.rankInternalValue hξ P hP (v i)
  have he : w 0 = hartogsNumber (w 1) :=
    (Defined.eval_iff (φ := hartogsNumberFormula) w).mp
      (A.rankInternalValue_eval_of_forces hξ P R hP hR hartogsNumberFormula v hf)
  have hv := congrArg Subtype.val he
  rw [rank_hartogsNumber_val (fun _ hb ↦ regularCardinal_succ_closed hi.regular hb)] at hv
  exact hv

theorem rankInternalCheckedHartogs_value (hξ : IsChoicelessInaccessible ξ)
    (P R one γ : SetDomain (hierarchy ξ)) (hP : P.val = A.P) (hR : R.val = A.R)
    (ho : one.val = A.one) (ht : one ∈ P) :
    A.ofName (A.rankInternalName P hP
      ⟨hartogsNumberName P R (checkName one γ), hartogsNumberName_isName _ _ _⟩) =
      hartogsNumber (A.check γ.val) := by
  rw [A.rankInternalHartogsName_value hξ P R one hP hR ho
    ⟨checkName one γ, checkName_isName ht γ⟩]
  exact congrArg hartogsNumber (A.rankInternalValue_check_val hξ P one γ hP ho ht)

theorem rankInternalHartogsCollapse_value (hξ : IsChoicelessInaccessible ξ)
    (P R one γ δ : SetDomain (hierarchy ξ)) (hP : P.val = A.P) (hR : R.val = A.R)
    (ho : one.val = A.one) (ht : one ∈ P) (hδ : IsOrdinal δ) :
    A.ofName (A.rankInternalName P hP
      ⟨woodinCollapseName P R (hartogsNumberName P R (checkName one γ)) (checkName one δ),
        woodinCollapseName_isName _ _ _ _⟩) =
      woodinCollapse (hartogsNumber (A.check γ.val)) (A.check δ.val) := by
  rw [A.rankInternalCollapseName_value hξ P R one hP hR ho
    ⟨hartogsNumberName P R (checkName one γ), hartogsNumberName_isName _ _ _⟩
    ⟨checkName one δ, checkName_isName ht δ⟩]
  rw [A.rankInternalCheckedHartogs_value hξ P R one γ hP hR ho ht]
  have hc := A.rankInternalValue_check_val hξ P one δ hP ho ht
  change A.ofName (A.rankInternalName P hP ⟨checkName one δ, checkName_isName ht δ⟩) =
    A.check δ.val at hc
  rw [hc]
  let := hierarchy_transitive ξ
  let := (TransitiveZF.ordinal_iff (hierarchy ξ) δ).mp hδ
  exact totalWoodinCollapse_eq _ _

end ForcingContext
end ZFVP
