import ZFVP.ModelTheory.ForcingInternalInaccessibleRankTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V) {ξ : V} [IsOrdinal ξ]
  [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rankInternalName (P : SetDomain (hierarchy ξ)) (hP : P.val = A.P)
    (τ : ForcingName P) : ForcingName A.P := by
  let := hierarchy_transitive ξ
  exact ⟨τ.val.val, hP ▸ (TransitiveZF.forcingName_iff (hierarchy ξ) P τ.val).mp τ.property⟩

noncomputable def rankInternalValue (hξ : IsChoicelessInaccessible ξ)
    (P : SetDomain (hierarchy ξ)) (hP : P.val = A.P) (τ : ForcingName P) :
    SetDomain (hierarchy (A.check ξ)) :=
  ⟨A.ofName (A.rankInternalName P hP τ),
    (A.mem_checked_hierarchy_iff_low_name_of_inaccessible hξ (hP ▸ P.property) _).mpr
      ⟨A.rankInternalName P hP τ, τ.val.property, rfl⟩⟩

theorem rankInternalValue_eval_of_forces (hξ : IsChoicelessInaccessible ξ)
    (P R : SetDomain (hierarchy ξ)) (hP : P.val = A.P) (hR : R.val = A.R)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName P)
    (hf : ∀ p ∈ P, p ∈ forcingFormula P R φ (standardTuple (fun i ↦ (v i).val))) :
    φ.Evalb (fun i ↦ A.rankInternalValue hξ P hP (v i)) := by
  have he := A.internalRank_formula_truth_of_inaccessible hξ P R hP hR φ
    (fun i ↦ A.rankInternalName P hP (v i)) (fun i ↦ (v i).val.property)
  apply he.mpr
  change GenericMeets A.G (forcingFormula P R φ (standardTuple (fun i ↦ (v i).val))).val
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have hpP : p ∈ P.val := hP ▸ A.generic.1.1 p hp
  let p' : SetDomain (hierarchy ξ) := ⟨p, (hierarchy_transitive ξ).mem_trans hpP P.property⟩
  exact ⟨p, hp, hf p' hpP⟩

end ForcingContext
end ZFVP
