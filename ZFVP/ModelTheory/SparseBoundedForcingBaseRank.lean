import ZFVP.ModelTheory.SparseBoundedForcingBase
import ZFVP.ModelTheory.TransitiveZFStandardEncoding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω : V} (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
include hΩ hAC

theorem sparseBoundedForcingBase_rank :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ {n : ℕ} (φ : BoundedFormulaTree n) (v : Fin n → SetDomain (hierarchy Ω)),
      (∀ i, IsForcingName ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) (v i).val) →
      ∀ p : SetDomain (hierarchy Ω),
        (sparseBoundedForcingBase φ).Evalb (p :> v) ↔
          p.val ∈ internalForcingSet
            ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
            ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω)
            (lowRankNameSet ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) Ω)
            (n : V) (encodeMembershipFormula φ.formula) (standardTuple (fun i ↦ (v i).val)) := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro n φ v hv p
  let P := (forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω
  let R := (forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω
  have hcode : IsMembershipFormulaCode (n : SetDomain (hierarchy Ω))
      (encodeMembershipFormula φ.formula) :=
    (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem φ.formula)
  have he := woodinSparse_localPrefixForces_rank_iff hΩ hAC
    (n : SetDomain (hierarchy Ω)) (encodeMembershipFormula φ.formula) (standardTuple v) p hcode
  rw [TransitiveZF.numeral_val, TransitiveZF.encodeMembershipFormula_val,
    TransitiveZF.standardTuple_val] at he
  rw [eval_sparseBoundedForcingBase, he]
  have hb : standardTuple (fun i ↦ (v i).val) ∈ lowRankNameSet P Ω ^ (n : V) :=
    standardTuple_mem_function _ (fun i ↦ (mem_lowRankNameSet P Ω (v i).val).mpr ⟨(v i).property, hv i⟩)
  by_cases hp : p.val ∈ P
  · exact woodinSparse_boundedPrefixForces_iff hΩ hAC φ.formula_bounded.encode hb hp
  · have hf : ¬WoodinSparseBoundedPrefixForces Ω (n : V) (encodeMembershipFormula φ.formula)
        (standardTuple (fun i ↦ (v i).val)) p.val := by
      rintro ⟨i, hi, η, hη, h0, hb, hpi, hforce⟩
      exact hp (woodinSparse_prefix_carrier_subset hΩ hAC hi p.val hpi)
    have hg : p.val ∉ internalForcingSet P R (lowRankNameSet P Ω) (n : V)
        (encodeMembershipFormula φ.formula) (standardTuple (fun i ↦ (v i).val)) :=
      fun h ↦ hp (internalForcingSet_subset _ _ _ _ _ _ _ h)
    exact iff_of_false hf hg

end ZFVP
