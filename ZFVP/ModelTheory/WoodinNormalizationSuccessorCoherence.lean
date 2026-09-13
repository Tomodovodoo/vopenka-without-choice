import ZFVP.ModelTheory.WoodinNormalizationSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinIterationSuccessor_projection_value {k s K i z : V}
    (hi : i ∈ succ k) (hz : z ∈ (forcingCodeP (woodinIterationSuccessor k s K)) ‘ (succ k)) :
    ((forcingCodeπ (woodinIterationSuccessor k s K)) ‘ ⟨i, succ k⟩ₖ) ‘ z =
      ((forcingCodeπ s) ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ z) := by
  simp only [woodinIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeπ_code, forcingMatrixNext_column hi]
  apply successorProjectionColumn_value hi
  simpa only [woodinIterationSuccessor, forcingSuccessorCode_poset] using hz

theorem woodinIterationSuccessor_section_value {k s K i p : V}
    (hi : i ∈ succ k) (hp : p ∈ (forcingCodeP s) ‘ i) :
    ((forcingCodeE (woodinIterationSuccessor k s K)) ‘ ⟨i, succ k⟩ₖ) ‘ p =
      ⟨((forcingCodeE s) ‘ ⟨i, k⟩ₖ) ‘ p, ∅⟩ₖ := by
  simp only [woodinIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeE_code, forcingMatrixNext_column hi]
  exact successorSectionColumn_value hi hp

variable {k s K m N T : V}
local notation "P" => (forcingCodeP s) ‘ k
local notation "R" => (forcingCodeR s) ‘ k
local notation "o" => (forcingCodet s) ‘ k
local notation "κ" => K ‘ k
local notation "c" => woodinPrefixCutoff P R o κ
local notation "s'" => woodinIterationSuccessor k s K
local notation "m'" => woodinNormalizationSuccessor k s K m

theorem woodinNormalizationSuccessor_projection_coherent {i z : V}
    (hr : IsForcingRetraction N T P R (m ‘ k)) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R o) (hone : o ∈ N) (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c)
    (hκc : κ ⊆ c) (he : ∀ p ∈ P, ⟨(m ‘ k) ‘ p, p⟩ₖ ∈ R ∧ ⟨p, (m ‘ k) ‘ p⟩ₖ ∈ R)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName o κ]))
    (hi : i ∈ succ k)
    (hcoh : ∀ p ∈ P, ((forcingCodeπ s) ‘ ⟨i, k⟩ₖ) ‘ ((m ‘ k) ‘ p) =
      (m ‘ i) ‘ (((forcingCodeπ s) ‘ ⟨i, k⟩ₖ) ‘ p))
    (hz : z ∈ (forcingCodeP s') ‘ (succ k)) :
    ((forcingCodeπ s') ‘ ⟨i, succ k⟩ₖ) ‘ ((m' ‘ (succ k)) ‘ z) =
      (m' ‘ i) ‘ (((forcingCodeπ s') ‘ ⟨i, succ k⟩ₖ) ‘ z) := by
  have hn := woodinNormalizationSuccessorMap_retraction hr hR hT ht hone hc hP hκc he hκ
  have hz' := hn.inclusion _ (function_value_mem hn.maps hz)
  have hfirst : kpair.π₁ z ∈ P := by
    have hzC := hz
    simp only [woodinIterationSuccessor, forcingSuccessorCode_poset] at hzC
    obtain ⟨p, hp, τ, _, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hzC
    simpa using hp
  rw [woodinNormalizationSuccessor_new, woodinNormalizationSuccessor_old hi,
    woodinIterationSuccessor_projection_value hi hz', woodinIterationSuccessor_projection_value hi hz,
    woodinNormalizationSuccessorMap_prefix hr hR hT ht hone hc hP hκc he hκ hz]
  exact hcoh _ hfirst

theorem woodinNormalizationSuccessor_section_coherent [IsOrdinal k] {i p : V}
    (hs : IsForcingIterationCode (succ k) s)
    (hr : IsForcingRetraction N T P R (m ‘ k)) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R o) (hone : o ∈ N) (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c)
    (hκc : κ ⊆ c) (he : ∀ q ∈ P, ⟨(m ‘ k) ‘ q, q⟩ₖ ∈ R ∧ ⟨q, (m ‘ k) ‘ q⟩ₖ ∈ R)
    (hκ : ∀ q ∈ P, q ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName o κ]))
    (hi : i ∈ succ k) (hp : p ∈ (forcingCodeP s) ‘ i)
    (hmp : (m ‘ i) ‘ p ∈ (forcingCodeP s) ‘ i)
    (hcoh : (m ‘ k) ‘ (((forcingCodeE s) ‘ ⟨i, k⟩ₖ) ‘ p) =
      ((forcingCodeE s) ‘ ⟨i, k⟩ₖ) ‘ ((m ‘ i) ‘ p)) :
    (m' ‘ (succ k)) ‘ (((forcingCodeE s') ‘ ⟨i, succ k⟩ₖ) ‘ p) =
      ((forcingCodeE s') ‘ ⟨i, succ k⟩ₖ) ‘ ((m' ‘ i) ‘ p) := by
  have hik : i ⊆ k := by
    rcases mem_succ_iff.mp hi with rfl | hik
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hik
  have hsec : ((forcingCodeE s) ‘ ⟨i, k⟩ₖ) ‘ p ∈ P :=
    hs.system.split.secMaps i hi k (mem_succ_self k) hik p hp
  rw [woodinNormalizationSuccessor_new, woodinNormalizationSuccessor_old hi,
    woodinIterationSuccessor_section_value hi hp, woodinIterationSuccessor_section_value hi hmp,
    woodinNormalizationSuccessorMap_empty_tail hr hR hT ht hone hc hP hκc he hκ hsec, hcoh]

theorem IsWoodinIteration.normalizationSuccessor_top {Ω : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (h : IsWoodinIteration Ω (succ k) s K)
    (hr : IsForcingRetraction N T P R (m ‘ k)) (hT : IsForcingPreorder N T) (hone : o ∈ N)
    (he : ∀ p ∈ P, ⟨(m ‘ k) ‘ p, p⟩ₖ ∈ R ∧ ⟨p, (m ‘ k) ‘ p⟩ₖ ∈ R) :
    (m' ‘ (succ k)) ‘ ((forcingCodet s') ‘ (succ k)) = (forcingCodet s') ‘ (succ k) := by
  obtain ⟨hR, ht, hc, hP, hκc, hκ⟩ := h.normalizationSuccessor_inputs hΩ
  have ht' : (forcingCodet s') ‘ (succ k) = ⟨o, ∅⟩ₖ := by
    simp only [woodinIterationSuccessor, forcingSuccessorCode_top]
  rw [ht', woodinNormalizationSuccessor_new,
    woodinNormalizationSuccessorMap_empty_tail hr hR hT ht hone hc hP hκc he hκ ht.1, hr.fixes o hone]

theorem IsWoodinIteration.normalizationSuccessor_equivalent {Ω z : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (h : IsWoodinIteration Ω (succ k) s K)
    (hr : IsForcingRetraction N T P R (m ‘ k)) (hT : IsForcingPreorder N T) (hone : o ∈ N)
    (he : ∀ p ∈ P, ⟨(m ‘ k) ‘ p, p⟩ₖ ∈ R ∧ ⟨p, (m ‘ k) ‘ p⟩ₖ ∈ R)
    (hz : z ∈ (forcingCodeP s') ‘ (succ k)) :
    ⟨(m' ‘ (succ k)) ‘ z, z⟩ₖ ∈ (forcingCodeR s') ‘ (succ k) ∧
      ⟨z, (m' ‘ (succ k)) ‘ z⟩ₖ ∈ (forcingCodeR s') ‘ (succ k) := by
  obtain ⟨hR, ht, hc, hP, hκc, hκ⟩ := h.normalizationSuccessor_inputs hΩ
  have hz' : z ∈ boundedNameTwoStep P R c (saturatedWoodinPrefixPosetName P R o κ c) := by
    simpa only [woodinIterationSuccessor, forcingSuccessorCode_poset,
      saturatedWoodinPrefix_twoStep_eq_bounded hR hc hP] using hz
  rw [woodinNormalizationSuccessor_new, woodinNormalizationSuccessorMap_eq hr hT]
  simpa only [woodinIterationSuccessor, forcingSuccessorCode_order,
    saturatedWoodinPrefix_twoStepOrder_eq_bounded hR hc hP] using
      normalizedBaseTwoStepMap_equivalent hr hR hT ht hone hc hP he
        (saturatedWoodinPrefix_iterand hR ht hc hP hκc hκ) hz'

end ZFVP
