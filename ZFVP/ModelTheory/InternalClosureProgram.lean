import ZFVP.ModelTheory.InternalTemplateProgram

/-! Explicit universal closure preserves internal syntax and universal satisfaction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evalSet_universalClosure_zero {c : V} (hc : c ∈ (ω : V)) :
    universalClosure.evalSet (naturalSquarePair 0 c) = c := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hc
  have h := congrArg internalArithmeticVal (evalArithmetic_universalClosure_zero u)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_zero] using h

theorem evalSet_universalClosure_succ {k c : V} (hk : k ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    universalClosure.evalSet (naturalSquarePair (SetTheory.succ k) c) =
      SetTheory.succ (naturalSquarePair 6 (universalClosure.evalSet (naturalSquarePair k c))) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hk
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hc
  have h := congrArg internalArithmeticVal (evalArithmetic_universalClosure_succ u v)
  have hsix : internalArithmeticVal (6 : InternalArithmetic V) = (6 : V) := internalArithmeticVal_natCast 6
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_succ, hsix] using h

theorem ordinalAdd_succ_interchange {n k : V} (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) :
    ordinalAdd (SetTheory.succ n) k = ordinalAdd n (SetTheory.succ k) := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal k := IsOrdinal.of_mem hk
  rw [ordinalAdd_succ_left_natural hn hk, ordinalAdd_succ]

theorem requirementFits_universalClosure (allowFree : Bool) {k n c : V}
    (hk : k ∈ (ω : V)) (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement allowFree).evalSet c) (ordinalAdd n k)) :
    requirementFits ((formulaRequirement allowFree).evalSet (universalClosure.evalSet (naturalSquarePair k c))) n := by
  have H : ∀ k ∈ (ω : V), ∀ n ∈ (ω : V), ∀ c ∈ (ω : V),
      requirementFits ((formulaRequirement allowFree).evalSet c) (ordinalAdd n k) →
      requirementFits ((formulaRequirement allowFree).evalSet (universalClosure.evalSet (naturalSquarePair k c))) n := by
    apply naturalNumber_induction (fun k ↦ ∀ n ∈ (ω : V), ∀ c ∈ (ω : V),
      requirementFits ((formulaRequirement allowFree).evalSet c) (ordinalAdd n k) →
      requirementFits ((formulaRequirement allowFree).evalSet (universalClosure.evalSet (naturalSquarePair k c))) n)
      (by definability)
    · intro n hn c hc hv
      rw [evalSet_universalClosure_zero hc]
      simpa only [zero_def, ordinalAdd_zero] using hv
    · intro k hk ih n hn c hc hv
      rw [evalSet_universalClosure_succ hk hc, requirementFits_formula_all allowFree
        (evalSet_natural _ (naturalSquarePair_natural hk hc)) hn]
      apply ih _ (ω_succ_closed hn) c hc
      rwa [ordinalAdd_succ_interchange hn hk]
  exact H k hk n hn c hc hv

theorem satisfies_universalClosure (allowFree : Bool) (M e : V) {k n c : V}
    (hk : k ∈ (ω : V)) (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement allowFree).evalSet c) (ordinalAdd n k))
    (hs : ∀ b ∈ structureDomain M ^ ordinalAdd n k,
      Satisfies membershipLanguageCode (naturalSyntaxFreeDomain allowFree) M e (ordinalAdd n k) (decodedNaturalFormula c) b) :
    ∀ b ∈ structureDomain M ^ n,
      Satisfies membershipLanguageCode (naturalSyntaxFreeDomain allowFree) M e n
        (decodedNaturalFormula (universalClosure.evalSet (naturalSquarePair k c))) b := by
  have H : ∀ k ∈ (ω : V), ∀ n ∈ (ω : V), ∀ c ∈ (ω : V),
      requirementFits ((formulaRequirement allowFree).evalSet c) (ordinalAdd n k) →
      (∀ b ∈ structureDomain M ^ ordinalAdd n k,
        Satisfies membershipLanguageCode (naturalSyntaxFreeDomain allowFree) M e (ordinalAdd n k) (decodedNaturalFormula c) b) →
      ∀ b ∈ structureDomain M ^ n,
        Satisfies membershipLanguageCode (naturalSyntaxFreeDomain allowFree) M e n
          (decodedNaturalFormula (universalClosure.evalSet (naturalSquarePair k c))) b := by
    apply naturalNumber_induction (fun k ↦ ∀ n ∈ (ω : V), ∀ c ∈ (ω : V),
      requirementFits ((formulaRequirement allowFree).evalSet c) (ordinalAdd n k) →
      (∀ b ∈ structureDomain M ^ ordinalAdd n k,
        Satisfies membershipLanguageCode (naturalSyntaxFreeDomain allowFree) M e (ordinalAdd n k) (decodedNaturalFormula c) b) →
      ∀ b ∈ structureDomain M ^ n,
        Satisfies membershipLanguageCode (naturalSyntaxFreeDomain allowFree) M e n
          (decodedNaturalFormula (universalClosure.evalSet (naturalSquarePair k c))) b) (by definability)
    · intro n hn c hc hv hs
      rw [evalSet_universalClosure_zero hc]
      simpa only [zero_def, ordinalAdd_zero] using hs
    · intro k hk ih n hn c hc hv hs b hb
      have hctx := ordinalAdd_succ_interchange hn hk
      have hv' : requirementFits ((formulaRequirement allowFree).evalSet c) (ordinalAdd (SetTheory.succ n) k) := hctx.symm ▸ hv
      have hs' : ∀ b ∈ structureDomain M ^ ordinalAdd (SetTheory.succ n) k,
          Satisfies membershipLanguageCode (naturalSyntaxFreeDomain allowFree) M e (ordinalAdd (SetTheory.succ n) k) (decodedNaturalFormula c) b := by
        simpa only [hctx] using hs
      have hcode := evalSet_natural universalClosure (naturalSquarePair_natural hk hc)
      have hvalid := decodedNaturalFormula_valid allowFree hcode (ω_succ_closed hn)
        (requirementFits_universalClosure allowFree hk (ω_succ_closed hn) hc hv')
      rw [evalSet_universalClosure_succ hk hc, decodedNaturalFormula_all hcode,
        satisfies_all membershipLanguageCode_valid hn hvalid hb]
      intro x hx
      exact ih _ (ω_succ_closed hn) c hc hv' hs' _ (assignmentPrepend_mem_function hn hb hx)
  exact H k hk n hn c hc hv hs

end ZFVP
