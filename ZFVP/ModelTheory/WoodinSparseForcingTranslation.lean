import ZFVP.ModelTheory.SparseBoundedForcingBaseRank
import ZFVP.ModelTheory.ClassForcingTranslationMeaning
import ZFVP.ModelTheory.WoodinSparseStandardFormulaTruth
import ZFVP.Syntax.InternalForcingStandardEncoding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinSparseForcingDictionary : ClassForcingDictionary where
  carrier := woodinSparseClassCarrierFormula
  order := woodinSparseClassOrderFormula
  names := woodinSparseClassNameFormula
  base := sparseBoundedForcingBase

def woodinSparseForcingTranslation {n : ℕ} (φ : SetTheorySemisentence n) : SetTheorySemisentence (n + 1) :=
  woodinSparseForcingDictionary.translation φ

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω : V} (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
include hΩ hAC

/-- A concrete parameter-free forcing translation with all higher-quantifier
clauses interpreted at the actual sparse endpoint rank. -/
theorem woodinSparseForcingTranslation_rank :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → SetDomain (hierarchy Ω)),
      (∀ i, IsForcingName ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) (v i).val) →
      ∀ p : SetDomain (hierarchy Ω),
        (woodinSparseForcingTranslation φ).Evalb (p :> v) ↔
          p.val ∈ classForcingFormula
            ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
            ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω)
            (fun x ↦ x ∈ hierarchy Ω ∧ IsForcingName ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) x)
            (by definability) φ (standardTuple (fun i ↦ (v i).val)) := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let P := (forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω
  let R := (forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω
  have hR := (woodinSparseStageCode_valid hΩ hAC (subset_refl Ω)).system.order.preorder Ω (mem_succ_self Ω)
  have hP := woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC Ω (mem_succ_self Ω)
  apply ClassForcingDictionary.translation_meaning woodinSparseForcingDictionary (hierarchy Ω) P R hR hP
    (woodinSparseClassCarrierFormula_rank hΩ hAC)
    (woodinSparseClassOrderFormula_rank hΩ hAC)
    (woodinSparseClassNameFormula_rank hΩ hAC)
  intro n φ v hv p
  have he := sparseBoundedForcingBase_rank hΩ hAC φ v hv p
  rw [internalForcingSet_standardEncoding P R (lowRankNameSet P Ω) φ.formula _
    (fun i ↦ (mem_lowRankNameSet P Ω (v i).val).mpr ⟨(v i).property, hv i⟩)] at he
  have hn : (fun x : V ↦ x ∈ lowRankNameSet P Ω) =
      (fun x : V ↦ x ∈ hierarchy Ω ∧ IsForcingName P x) := by
    funext x
    exact propext (mem_lowRankNameSet P Ω x)
  simp only [hn] at he
  exact he

end ZFVP

