import ZFVP.ModelTheory.WoodinSparseCodeRankAgreement
import ZFVP.ModelTheory.TransitiveZFLowRankInternalForcing
import ZFVP.ModelTheory.WoodinSparseBoundedEndpointComparison

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The local class-forcing base ranges over all ordinal prefixes in its own
universe. It has no ambient endpoint parameter. -/
def WoodinSparseLocalPrefixForces (n φ b p : V) : Prop :=
  ∃ i η : V, IsOrdinal i ∧ IsOrdinal η ∧ (∅ : V) ∈ η ∧
    let P := (forcingCodeP (woodinSparseStageCode i)) ‘ i;
    let R := (forcingCodeR (woodinSparseStageCode i)) ‘ i;
    b ∈ lowRankNameSet P η ^ n ∧ p ∈ P ∧
      InternalForces P R (lowRankNameSet P η) n φ b p

variable {Ω : V} (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)

include hAC
/-- The actual local prefix computation in the endpoint rank is precisely the
bounded-prefix relation in the ambient universe. -/
theorem woodinSparse_localPrefixForces_rank_iff :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ n φ b p : SetDomain (hierarchy Ω), IsMembershipFormulaCode n φ →
      (WoodinSparseLocalPrefixForces n φ b p ↔
        WoodinSparseBoundedPrefixForces Ω n.val φ.val b.val p.val) := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro n φ b p hφ
  let j := setDomainEndExtension (hierarchy Ω)
  have hφ' : IsMembershipFormulaCode n.val φ.val := (j.membershipFormulaCode_iff n φ).mpr hφ
  have rows (i : SetDomain (hierarchy Ω)) (hi : IsOrdinal i) :
      ((forcingCodeP (woodinSparseStageCode i)) ‘ i).val =
          (forcingCodeP (woodinSparseStageCode i.val)) ‘ i.val ∧
      ((forcingCodeR (woodinSparseStageCode i)) ‘ i).val =
          (forcingCodeR (woodinSparseStageCode i.val)) ‘ i.val := by
    have hs := (hΩ.rank_woodinSparseCode_val hAC i hi).2
    simp only [TransitiveZF.value_val_total, TransitiveZF.forcingCodeP_val,
      TransitiveZF.forcingCodeR_val, hs]
    exact ⟨trivial, trivial⟩
  have hlocal (i η : SetDomain (hierarchy Ω)) (hi : IsOrdinal i) (hη : IsOrdinal η) :
      let P := (forcingCodeP (woodinSparseStageCode i)) ‘ i;
      let R := (forcingCodeR (woodinSparseStageCode i)) ‘ i;
      (b ∈ lowRankNameSet P η ^ n ∧ p ∈ P ∧ InternalForces P R (lowRankNameSet P η) n φ b p) ↔
      let P' := (forcingCodeP (woodinSparseStageCode i.val)) ‘ i.val;
      let R' := (forcingCodeR (woodinSparseStageCode i.val)) ‘ i.val;
      b.val ∈ lowRankNameSet P' η.val ^ n.val ∧ p.val ∈ P' ∧
        p.val ∈ internalForcingSet P' R' (lowRankNameSet P' η.val) n.val φ.val b.val := by
    dsimp only
    let P := (forcingCodeP (woodinSparseStageCode i)) ‘ i
    let R := (forcingCodeR (woodinSparseStageCode i)) ‘ i
    have hD := TransitiveZF.lowRankNameSet_val P η hη
    have hf := (j.function_iff b n (lowRankNameSet P η)).symm
    change (b ∈ lowRankNameSet P η ^ n ↔ b.val ∈ (lowRankNameSet P η).val ^ n.val) at hf
    rw [hD, (rows i hi).1] at hf
    rw [hf]
    have hp : p ∈ P ↔ p.val ∈ (forcingCodeP (woodinSparseStageCode i.val)) ‘ i.val := by
      change p.val ∈ P.val ↔ _
      rw [(rows i hi).1]
    rw [hp]
    apply and_congr_right
    intro hb
    apply and_congr_right
    intro hpp
    have hb' := hf.mpr hb
    have hp' := hp.mpr hpp
    have he := TransitiveZF.internalForces_lowRankNameSet_iff P R η n φ b p hη hφ hb' hp'
    rw [(rows i hi).1, (rows i hi).2] at he
    exact he.trans (mem_internalForcingSet hφ').symm
  constructor
  · rintro ⟨i, η, hi, hη, h0, hh⟩
    have hi' := (TransitiveZF.ordinal_iff (hierarchy Ω) i).mp hi
    have hη' := (TransitiveZF.ordinal_iff (hierarchy Ω) η).mp hη
    let := hi'
    let := hη'
    refine ⟨i.val, ordinal_mem_hierarchy_iff.mp i.property, η.val,
      ordinal_mem_hierarchy_iff.mp η.property, ?_, (hlocal i η hi hη).mp hh⟩
    change (∅ : V) ∈ η.val
    change (∅ : SetDomain (hierarchy Ω)).val ∈ η.val at h0
    rwa [TransitiveZF.empty_val] at h0
  · rintro ⟨i, hi, η, hη, h0, hh⟩
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hη
    let i' : SetDomain (hierarchy Ω) := ⟨i, ordinal_mem_hierarchy_iff.mpr hi⟩
    let η' : SetDomain (hierarchy Ω) := ⟨η, ordinal_mem_hierarchy_iff.mpr hη⟩
    have hi' : IsOrdinal i' := (TransitiveZF.ordinal_iff (hierarchy Ω) i').mpr inferInstance
    have hη' : IsOrdinal η' := (TransitiveZF.ordinal_iff (hierarchy Ω) η').mpr inferInstance
    refine ⟨i', η', hi', hη', ?_, (hlocal i' η' hi' hη').mpr hh⟩
    change (∅ : SetDomain (hierarchy Ω)).val ∈ η
    rwa [TransitiveZF.empty_val]

end ZFVP


