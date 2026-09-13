import ZFVP.ModelTheory.UniformWoodinSparseRecursion
import ZFVP.ModelTheory.LocalSparsePrefixForcingFormula
import ZFVP.ModelTheory.WoodinSparseClassReadout
import ZFVP.ModelTheory.ClassCarrierNameFormula

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinSparseClassCarrierFormula : SetTheorySemisentence 1 :=
  f“p. ∃ i, !IsOrdinal.dfn i ∧
    p ∈ !value.dfn (!forcingCodePFormula (!woodinSparseStageCodeFormula i)) i”

def woodinSparseClassOrderFormula : SetTheorySemisentence 2 :=
  f“p q. ∃ i, !IsOrdinal.dfn i ∧
    !kpair.dfn p q ∈ !value.dfn (!forcingCodeRFormula (!woodinSparseStageCodeFormula i)) i”

def woodinSparseClassNameFormula : SetTheorySemisentence 1 :=
  classCarrierNameFormula woodinSparseClassCarrierFormula

def woodinSparseLocalForcingFormula : SetTheorySemisentence 4 :=
  localSparsePrefixForcingFormula woodinSparseStageCodeFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_woodinSparseClassCarrierFormula (p : V) :
    woodinSparseClassCarrierFormula.Evalb ![p] ↔
      ∃ i : V, IsOrdinal i ∧ p ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i := by
  simp [woodinSparseClassCarrierFormula]

theorem eval_woodinSparseClassOrderFormula (p q : V) :
    woodinSparseClassOrderFormula.Evalb ![p, q] ↔
      ∃ i : V, IsOrdinal i ∧ ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode i)) ‘ i := by
  simp [woodinSparseClassOrderFormula]

theorem eval_woodinSparseLocalForcingFormula {n φ b p : V} (hφ : IsMembershipFormulaCode n φ) :
    woodinSparseLocalForcingFormula.Evalb ![n, φ, b, p] ↔ WoodinSparseLocalPrefixForces n φ b p :=
  eval_localSparsePrefixForcingFormula _ hφ

variable {Ω : V} (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
include hΩ hAC

theorem woodinSparseClassCarrierFormula_rank :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ p : SetDomain (hierarchy Ω), woodinSparseClassCarrierFormula.Evalb ![p] ↔
      p.val ∈ (forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro p
  rw [eval_woodinSparseClassCarrierFormula, woodinSparse_endpoint_carrier_union hΩ hAC]
  have row (i : SetDomain (hierarchy Ω)) (hi : IsOrdinal i) :
      ((forcingCodeP (woodinSparseStageCode i)) ‘ i).val =
        (forcingCodeP (woodinSparseStageCode i.val)) ‘ i.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodeP_val,
      (hΩ.rank_woodinSparseCode_val hAC i hi).2]
  constructor
  · rintro ⟨i, hi, hp⟩
    let := (TransitiveZF.ordinal_iff (hierarchy Ω) i).mp hi
    refine ⟨i.val, ordinal_mem_hierarchy_iff.mp i.property, ?_⟩
    change p.val ∈ ((forcingCodeP (woodinSparseStageCode i)) ‘ i).val at hp
    rwa [row i hi] at hp
  · rintro ⟨i, hi, hp⟩
    let := IsOrdinal.of_mem hi
    let i' : SetDomain (hierarchy Ω) := ⟨i, ordinal_mem_hierarchy_iff.mpr hi⟩
    have hi' : IsOrdinal i' := (TransitiveZF.ordinal_iff (hierarchy Ω) i').mpr inferInstance
    refine ⟨i', hi', ?_⟩
    change p.val ∈ ((forcingCodeP (woodinSparseStageCode i')) ‘ i').val
    rwa [row i' hi']

theorem woodinSparseClassOrderFormula_rank :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ p q : SetDomain (hierarchy Ω), woodinSparseClassOrderFormula.Evalb ![p, q] ↔
      ⟨p.val, q.val⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro p q
  rw [eval_woodinSparseClassOrderFormula, woodinSparse_endpoint_order_union hΩ hAC]
  have row (i : SetDomain (hierarchy Ω)) (hi : IsOrdinal i) :
      ((forcingCodeR (woodinSparseStageCode i)) ‘ i).val =
        (forcingCodeR (woodinSparseStageCode i.val)) ‘ i.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodeR_val,
      (hΩ.rank_woodinSparseCode_val hAC i hi).2]
  constructor
  · rintro ⟨i, hi, hp⟩
    let := (TransitiveZF.ordinal_iff (hierarchy Ω) i).mp hi
    refine ⟨i.val, ordinal_mem_hierarchy_iff.mp i.property, ?_⟩
    change (⟨p, q⟩ₖ : SetDomain (hierarchy Ω)).val ∈ ((forcingCodeR (woodinSparseStageCode i)) ‘ i).val at hp
    rwa [TransitiveZF.kpair_val, row i hi] at hp
  · rintro ⟨i, hi, hp⟩
    let := IsOrdinal.of_mem hi
    let i' : SetDomain (hierarchy Ω) := ⟨i, ordinal_mem_hierarchy_iff.mpr hi⟩
    have hi' : IsOrdinal i' := (TransitiveZF.ordinal_iff (hierarchy Ω) i').mpr inferInstance
    refine ⟨i', hi', ?_⟩
    change (⟨p, q⟩ₖ : SetDomain (hierarchy Ω)).val ∈ ((forcingCodeR (woodinSparseStageCode i')) ‘ i').val
    rwa [TransitiveZF.kpair_val, row i' hi']

theorem woodinSparseClassNameFormula_rank :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ τ : SetDomain (hierarchy Ω), woodinSparseClassNameFormula.Evalb ![τ] ↔
      IsForcingName ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) τ.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  exact eval_classCarrierNameFormula_transitive (hierarchy Ω) _ _
    (woodinSparseClassCarrierFormula_rank hΩ hAC)

theorem woodinSparseLocalForcingFormula_rank :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ n φ b p : SetDomain (hierarchy Ω), IsMembershipFormulaCode n φ →
      (woodinSparseLocalForcingFormula.Evalb ![n, φ, b, p] ↔
        WoodinSparseBoundedPrefixForces Ω n.val φ.val b.val p.val) := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  intro n φ b p hφ
  exact (eval_woodinSparseLocalForcingFormula hφ).trans
    (woodinSparse_localPrefixForces_rank_iff hΩ hAC n φ b p hφ)

end ZFVP

