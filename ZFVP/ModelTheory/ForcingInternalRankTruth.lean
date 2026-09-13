import ZFVP.ModelTheory.TransitiveZFFormulaForcing
import ZFVP.ModelTheory.ForcingRankTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V) {δ : V}
variable [Nonempty (SetDomain (hierarchy δ))] [(SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalRank_formula_truth (hδ : Cn 1 δ)
    (P R : SetDomain (hierarchy δ)) (hP : P.val = A.P) (hR : R.val = A.R)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName A.P)
    (hv : ∀ i, (v i).val ∈ hierarchy δ) :
    φ.Evalb (show Fin n → SetDomain (hierarchy (A.check δ)) from fun i ↦
      (⟨A.ofName (v i), (A.mem_checked_hierarchy_iff_low_name hδ (hP ▸ P.property) _).mpr
        ⟨v i, hv i, rfl⟩⟩ : SetDomain (hierarchy (A.check δ)))) ↔
      GenericMeets A.G (forcingFormula P R φ
        (standardTuple (fun i ↦ (⟨(v i).val, hv i⟩ : SetDomain (hierarchy δ))))).val := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  let w : Fin n → SetDomain (hierarchy δ) := fun i ↦ ⟨(v i).val, hv i⟩
  have he := TransitiveZF.forcingFormula_standardTuple_val (hierarchy δ) P R φ w
  have he' : (forcingFormula P R φ (standardTuple w)).val =
      classForcingFormula A.P A.R (IsLowRankForcingName A.P δ) (by definability) φ
        (standardTuple (fun i ↦ (v i).val)) := by
    rw [hP, hR] at he
    convert he using 1
    rfl
  exact (A.rankName_formula_truth hδ (hP ▸ P.property) φ v hv).trans
    (congrArg (GenericMeets A.G) he').symm.to_iff

end ForcingContext
end ZFVP
