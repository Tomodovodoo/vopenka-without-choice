import ZFVP.ModelTheory.GenericSigmaDomain
import ZFVP.SetTheory.CnForcingDomain
import ZFVP.ModelTheory.ForcingCheckedTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem domainSigmaTruth_zero_iff_sigmaOneTruth {n φ b : V}
    (hφ : IsLevyFormulaCode .sigma 1 n φ) :
    DomainSigmaTruth 0 n φ b ↔ SigmaOneTruth n φ b := by
  constructor
  · rintro ⟨T, hT, hb, ht⟩
    exact ⟨T, hT.support.toIsCodingSupport.toIsTransitive, hT.nonempty, hb, ht⟩
  · rintro ⟨T, hT, hne, hb, ht⟩
    obtain ⟨U, hU, hTU⟩ := sequenceSupport_containing T
    let := hU
    let := hT
    have hsub : T ⊆ U := fun x hx ↦ hU.toIsCodingSupport.toIsTransitive.mem_trans hx hTU
    have hneU : IsNonempty U := ⟨ω, IsCodingSupport.omega_mem⟩
    exact ⟨U, hU, mem_function_of_mem_function_of_subset hb hsub,
      membershipSatisfies_sigmaOne_upward hφ hne hneU hsub hb ht⟩

namespace ForcingContext

theorem lowRank_sigmaOneTruth_downward (A : ForcingContext V) {δ n φ b : V}
    (hδ : Cn 1 δ) (hP : A.P ∈ hierarchy δ) (hR : A.R ∈ hierarchy δ)
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ lowRankNameSet A.P δ ^ n)
    (hσ : IsLevyFormulaCode .sigma 1 (A.check n) (A.check φ))
    (ht : SigmaOneTruth (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb))) :
    MembershipSatisfies (hierarchy (A.check δ)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb)) := by
  let := hδ.ordinal
  let := hierarchy_transitive (A.check δ)
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  let := IsFunction.of_mem hb
  have hbu : b ∈ hierarchy δ := function_mem_sequenceSupport
    (fun τ hτ ↦ (mem_lowRankNameSet A.P δ τ).mp hτ |>.1) hφ.context hb
  obtain ⟨p, hp, D, hD, hne, hbD, hf⟩ := A.sigmaOneTruth_forcingDomain
    (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb)
    (domain_eq_of_mem_function hb) hφ hσ ht
  obtain ⟨E, hEu, hE, hneE, hbE, hfE⟩ := hδ.forcingDomain_family hP hR hbu hφ
    (A.generic.1.1 p hp) ⟨D, hD, hne, hbD, hf⟩
  have hc : ∀ τ ∈ E, ∀ u p, ⟨u, p⟩ₖ ∈ τ → u ∈ E :=
    fun τ hτ u _ hu ↦ hE.subname_closed τ hτ u (mem_domain_of_kpair_mem hu)
  let T := range (A.evaluationGraph E hE.names)
  let : IsTransitive T := A.evaluationRange_transitive E hE.names hc
  have hneT : IsNonempty T := A.evaluationRange_nonempty E hE.names hneE
  have hTU : T ⊆ hierarchy (A.check δ) := by
    intro x hx
    obtain ⟨τ, hτ, rfl⟩ := (A.mem_range_evaluationGraph_iff E hE.names x).mp hx
    exact A.ofName_mem_checked_hierarchy _ ((hierarchy_transitive δ).mem_trans hτ hEu)
  have hneU : IsNonempty (hierarchy (A.check δ)) := by
    obtain ⟨x, hx⟩ := hneT.nonempty
    exact ⟨x, hTU x hx⟩
  have htT := (A.groundGenericTruth E hE.names hφ b hbE).mpr
    ⟨p, hp, (mem_internalForcingSet hφ).mpr hfE⟩
  exact membershipSatisfies_sigmaOne_upward hσ hneT hneU hTU
    (A.sequenceValue_mem_evaluationRange hE.names hbE) htT

theorem cn_one_check (A : ForcingContext V) {δ : V}
    (hδ : Cn 1 δ) (hP : A.P ∈ hierarchy δ) :
    Cn 1 (A.check δ) := by
  let := hδ.ordinal
  let := hierarchy_transitive (A.check δ)
  have hR : A.R ∈ hierarchy δ := subset_mem_hierarchy_limit hδ.successor_closed
    (prod_mem_hierarchy_limit hδ.successor_closed hP hP) A.order.1
  refine ⟨inferInstance, ?_⟩
  intro n φ hφ b hb
  rw [domainSigmaTruth_zero_iff_sigmaOneTruth hφ]
  constructor
  · intro ht
    have hc : IsMembershipFormulaCode n φ := (mem_formulaSet_iff _ _ _ _).mp hφ.valid
    obtain ⟨m, ψ, hn, hψ, hvalid⟩ := A.checkEmbedding.membershipFormulaCode_preimages hc
    change n = A.check m at hn
    change φ = A.check ψ at hψ
    subst n φ
    obtain ⟨s, hs, hsD, he⟩ := A.lowRankFiniteAssignment_representative hδ hP hvalid.context hb
    subst b
    exact A.lowRank_sigmaOneTruth_downward hδ hP hR hvalid hsD hφ ht
  · intro ht
    let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
    have h0 : (∅ : V) ∈ hierarchy δ := IsCodingSupport.empty_mem
    have hne : IsNonempty (hierarchy (A.check δ)) :=
      ⟨A.ofName ⟨∅, empty_forcingName A.P⟩, A.ofName_mem_checked_hierarchy _ h0⟩
    exact ⟨hierarchy (A.check δ), inferInstance, hne, hb, ht⟩

end ForcingContext

def smallForcingCnOneFormula : SetTheorySemisentence 5 :=
  f“P R o δ p. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !(cnFormula 1) δ ∧ P ∈ !hierarchyFormula δ ∧ p ∈ P →
      !(checkedUnaryForcingFormula (cnFormula 1)) P R o p δ”

theorem eval_smallForcingCnOneFormula (v : Fin 5 → V) :
    smallForcingCnOneFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        Cn 1 (v 3) → v 0 ∈ hierarchy (v 3) → v 4 ∈ v 0 →
        v 4 ∈ forcingFormula (v 0) (v 1) (cnFormula 1)
          (standardTuple ![checkName (v 2) (v 3)])) := by
  simp [smallForcingCnOneFormula]

theorem smallForcing_forces_cn_one_countable [Countable V] {P R one δ p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : Cn 1 δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P) :
    p ∈ forcingFormula P R (cnFormula 1) (standardTuple ![checkName one δ]) := by
  refine forces_checkedUnary_of_all_generics hR htop hp (cnFormula 1) ?_
  intro G hG _hpG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  exact ((cnFormula_defined 1).iff _).mpr (A.cn_one_check hδ hP)

theorem smallForcing_forces_cn_one {P R one δ p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : Cn 1 δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P) :
    p ∈ forcingFormula P R (cnFormula 1) (standardTuple ![checkName one δ]) := by
  have hh := eval_of_countable_zf smallForcingCnOneFormula (by
    intro W _ _ _ _ v
    exact (eval_smallForcingCnOneFormula v).mpr
      (fun hR htop hδ hP hp ↦ smallForcing_forces_cn_one_countable
        (P := v 0) (R := v 1) (one := v 2) (δ := v 3) (p := v 4) hR htop hδ hP hp))
    ![P, R, one, δ, p]
  exact (eval_smallForcingCnOneFormula ![P, R, one, δ, p]).mp hh hR htop hδ hP hp

end ZFVP
