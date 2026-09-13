import ZFVP.ModelTheory.InternalHenkinNameRenaming

/-! Every accepted existential receives a fresh natural-name witness at its
enumerated Henkin stage. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem henkinWitnessCode_accepts_body (hω : Schmerl.HasStandardOmega V) {T s n φ ψ : V}
    (hs : IsCoherentHenkinSequence T s) (hzero : (0 : V) ∈ n)
    (hφ : IsConsistentCodedFormula T n φ) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ (succ n))
    (ha : HenkinAccepted T s ⟨n, existsCode ψ⟩ₖ)
    (hstep : HenkinAccepted T s (henkinWitnessCode n φ (henkinDecisionLiteral T n φ (existsCode ψ)))) :
    HenkinAccepted T s ⟨succ n, ψ⟩ₖ := by
  classical
  have he := (formulaSet_quantifiers membershipLanguageCode_valid hφ.context hψ).2
  have hc := henkinDecisionLiteral_consistent hω hφ he
  have hl := hstep.of_refines hω (henkinWitnessCode_refines_literal hω hzero hc)
  have hchoice : IsConsistentCodedFormula T n (andCode φ (existsCode ψ)) := by
    by_contra hneg
    rw [henkinDecisionLiteral, ite_eq_right hneg] at hl
    exact ha.not_negate hω hs hl
  rw [henkinDecisionLiteral, ite_eq_left hchoice] at hstep
  have hself : existsCode ψ = existsCode (kpair.π₂ (existsCode ψ)) := by simp [existsCode]
  have hs' : HenkinAccepted T s ⟨succ n, andCode ψ (henkinShiftFormula n φ)⟩ₖ := by
    simpa only [henkinWitnessCode, existsCode, kpair.π₂_kpair, ite_true] using hstep
  exact hs'.consequence hω (CodedFormulaImplies.conj_left T hψ (henkinShiftFormula_valid hφ.context hφ.1))

theorem henkinLiftCode_exists {n ψ k : V} (hn : n ∈ (ω : V))
    (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hk : k ∈ (ω : V)) :
    henkinLiftCode ⟨n, existsCode ψ⟩ₖ k = ⟨ordinalAdd n k,
      existsCode (renameMembershipFormula (succ n) (succ (ordinalAdd n k))
        (liftMembershipIndices n (tailShiftIndices n k)) ψ)⟩ₖ := by
  rw [henkinLiftCode_eq_rename (formulaSet_quantifiers membershipLanguageCode_valid hn hψ).2 hk,
    renameMembershipFormula_exists hn (ordinalAdd_natural hn hk) (tailShiftIndices_function hn hk) hψ]

theorem henkinStages_exists_witness (hω : Schmerl.HasStandardOmega V) {T e n ψ : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    (hrange : range e = formulaFamily (membershipLanguageCode : V) ∅)
    (hn : n ∈ (ω : V)) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ (succ n))
    (ha : HenkinAccepted T (henkinStages T e) ⟨n, existsCode ψ⟩ₖ) :
    ∃ a ∈ (ω : V), HenkinAccepted T (henkinStages T e)
      ⟨succ (ordinalAdd n a), renameMembershipFormula (succ n) (succ (ordinalAdd n a))
        (liftMembershipIndices n (tailShiftIndices n a)) ψ⟩ₖ := by
  have hs := henkinStages_complete hω hT he hrange
  have hex := (formulaSet_quantifiers membershipLanguageCode_valid hn hψ).2
  have hq : ⟨n, existsCode ψ⟩ₖ ∈ range e := hrange ▸ (mem_formulaSet_iff _ _ _ _).mp hex
  obtain ⟨k, hkq⟩ := mem_range_iff.mp hq
  have : IsFunction e := IsFunction.of_mem he
  have hk : k ∈ (ω : V) := by simpa only [domain_eq_of_mem_function he] using mem_domain_of_kpair_mem hkq
  have hv : e ‘ k = ⟨n, existsCode ψ⟩ₖ := value_eq_of_kpair_mem hkq
  obtain ⟨m, φ, hp, hzero, hφ⟩ := henkinConditions_cases (function_value_mem hs.1.1 hk)
  have hm := hφ.context
  let A := henkinLiftCode ⟨m, φ⟩ₖ (succ n)
  let B := henkinLiftCode ⟨n, existsCode ψ⟩ₖ (succ m)
  let χ := renameMembershipFormula (succ n) (succ (ordinalAdd n (succ m)))
    (liftMembershipIndices n (tailShiftIndices n (succ m))) ψ
  have hA := henkinLiftCode_consistent hω hφ hzero (ω_succ_closed hn)
  have hB : B = ⟨ordinalAdd n (succ m), existsCode χ⟩ₖ :=
    henkinLiftCode_exists hn hψ (ω_succ_closed hm)
  have hcontext : kpair.π₁ A = ordinalAdd n (succ m) := by
    dsimp only [A]
    rw [henkinLiftCode_context hm (ω_succ_closed hn)]
    have : IsOrdinal n := IsOrdinal.of_mem hn
    have : IsOrdinal m := IsOrdinal.of_mem hm
    rw [ordinalAdd_succ, ordinalAdd_succ, ordinalAdd_comm_natural hm hn]
  have hχ : χ ∈ formulaSet membershipLanguageCode ∅ (succ (ordinalAdd n (succ m))) :=
    renameMembershipFormula_mem (ω_succ_closed hn) (ω_succ_closed (ordinalAdd_natural hn (ω_succ_closed hm)))
      (liftMembershipIndices_function hn (ordinalAdd_natural hn (ω_succ_closed hm))
        (tailShiftIndices_function hn (ω_succ_closed hm))) hψ
  have hacc := (hs.lift_iff hω hex (ω_succ_closed hm)).mpr ha
  change HenkinAccepted T (henkinStages T e) B at hacc
  rw [hB] at hacc
  have hstep := HenkinAccepted.stage hs.1 (ω_succ_closed hk)
  rw [henkinStages_succ T e hk, hv, hp] at hstep
  simp only [henkinNextCode, kpair.π₁_kpair] at hstep
  change HenkinAccepted T (henkinStages T e)
    (henkinWitnessCode (kpair.π₁ A) (kpair.π₂ A)
      (henkinDecisionLiteral T (kpair.π₁ A) (kpair.π₂ A) (kpair.π₂ B))) at hstep
  rw [hB, kpair.π₂_kpair, hcontext] at hstep
  change (0 : V) ∈ kpair.π₁ A ∧ IsConsistentCodedFormula T (kpair.π₁ A) (kpair.π₂ A) at hA
  rw [hcontext] at hA
  exact ⟨succ m, ω_succ_closed hm, henkinWitnessCode_accepts_body hω hs.1 hA.1 hA.2 hχ hacc hstep⟩

end ZFVP
