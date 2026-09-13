import ZFVP.ModelTheory.RankNameFormulaTruthCoverage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω : V} [IsOrdinal Ω]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG

/-- Actual endpoint truth for every standard formula, including all higher
quantifiers. Coverage comes from the constructed sparse iteration. -/
theorem woodinSparse_endpoint_standardFormula_truth {n : ℕ}
    (φ : SetTheorySemisentence n) (v : Fin n → ForcingName (E).P)
    (hv : ∀ i, (v i).val ∈ hierarchy Ω) :
    φ.Evalb (show Fin n → SetDomain (hierarchy ((E).check Ω)) from fun i ↦
      ⟨(E).ofName (v i), (E).ofName_mem_checked_hierarchy _ (hv i)⟩) ↔
      GenericMeets (E).G (classForcingFormula (E).P (E).R (IsLowRankForcingName (E).P Ω)
        (by definability) φ (standardTuple (fun i ↦ (v i).val))) :=
  (E).rankName_formula_truth_of_coverage
    (woodinSparseGenericContext_endpoint_low_name_coverage hΩ hAC hG) φ v hv

variable {γ : V} [IsOrdinal γ] (hγ : γ ∈ Ω)
local notation "B" => woodinSparseFixedPointContext hΩ hAC hG hγ

theorem woodinSparse_fixedPoint_standardFormula_truth
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) {n : ℕ}
    (φ : SetTheorySemisentence n) (v : Fin n → ForcingName (B).P)
    (hv : ∀ i, (v i).val ∈ hierarchy γ) :
    φ.Evalb (show Fin n → SetDomain (hierarchy ((B).check γ)) from fun i ↦
      ⟨(B).ofName (v i), (B).ofName_mem_checked_hierarchy _ (hv i)⟩) ↔
      GenericMeets (B).G (classForcingFormula (B).P (B).R (IsLowRankForcingName (B).P γ)
        (by definability) φ (standardTuple (fun i ↦ (v i).val))) :=
  (B).rankName_formula_truth_of_coverage
    (woodinSparseFixedPointContext_low_name_coverage hΩ hAC hG hγ hfix) φ v hv

end ZFVP
