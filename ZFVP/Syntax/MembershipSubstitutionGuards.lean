import ZFVP.Syntax.FormulaSubstitutionValidity
import ZFVP.Syntax.MembershipAtomicSyntax

/-! Capture-avoiding substitution carries a bounded membership guard to a bounded guard. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem substituted_boundPairArguments {n i j B E : V} (hn : n ∈ (ω : V))
    (hi : i ∈ n) (hj : j ∈ n) :
    compose (boundPairArguments i j) (termSubstitution membershipLanguageCode ∅ n B E) =
      standardTuple ![B ‘ i, B ‘ j] := by
  unfold boundPairArguments
  rw [compose_standardTuple]
  · congr 1
    funext a
    refine Fin.cases ?_ (fun b ↦ Fin.cases ?_ (fun c ↦ Fin.elim0 c) b) a
    · exact termSubstitution_boundVar membershipLanguageCode_valid hn ∅ B E hi
    · exact termSubstitution_boundVar membershipLanguageCode_valid hn ∅ B E hj
  · intro a
    simp only [domain_termSubstitution]
    have hc := (termSet_closed (membershipLanguageCode_valid (V := V)) hn ∅).1
    exact Fin.cases (hc i hi) (fun b ↦ Fin.cases (hc j hj) (fun c ↦ Fin.elim0 c) b) a

theorem substituted_guardArguments {n m B E i j : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hB : B ∈ termSet membershipLanguageCode ∅ m ^ n)
    (hi : i ∈ n) (hj : j ∈ m) (hij : B ‘ i = boundVarCode j) :
    compose (boundedGuardArguments i)
      (termSubstitution membershipLanguageCode ∅ (succ n)
        (liftBoundReplacement membershipLanguageCode ∅ m n B) E) = boundedGuardArguments j := by
  change compose (boundPairArguments 0 (succ i)) _ = boundPairArguments 0 (succ j)
  rw [substituted_boundPairArguments (ω_succ_closed hn) (zero_mem_succ_natural hn)
    (succ_mem_succ_of_natural_mem hn hi)]
  rw [liftBoundReplacement_zero hn, liftBoundReplacement_succ membershipLanguageCode_valid hm hn hB hi,
    hij, termBoundShift_boundVar membershipLanguageCode_valid hm ∅ hj]
  rfl

theorem substitutionState_bound_index {s i : V} (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s)
    (hi : i ∈ stateSource s) : ∃ j ∈ stateTarget s, (stateBound s) ‘ i = boundVarCode j :=
  membershipTerm_cases hs.2.1 (function_value_mem hs.2.2.1 hi)

theorem formulaSubstitutionGraph_boundedAll {G n i φ k j : V}
    (hn : n ∈ (ω : V)) (hi : i ∈ n) (hk : k ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n))
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ (G ‘ k))
    (hc : n = stateSource (G ‘ k))
    (hstep : G ‘ (succ k) = liftSubstitutionState membershipLanguageCode ∅ (G ‘ k))
    (hj : j ∈ stateTarget (G ‘ k)) (hij : (stateBound (G ‘ k)) ‘ i = boundVarCode j) :
    (formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨n, boundedAllCode i φ⟩ₖ, k⟩ₖ =
      boundedAllCode j ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ) := by
  have ha := boundedGuardArguments_valid hn hi
  have hg := (formulaSet_atoms membershipLanguageCode_valid (ω_succ_closed hn) ha).2
  rw [boundedAllCode, formulaSubstitutionGraph_all membershipLanguageCode_valid hn hk
    (formulaSet_binary membershipLanguageCode_valid (ω_succ_closed hn) hg hφ).2,
    formulaSubstitutionGraph_or membershipLanguageCode_valid (ω_succ_closed hn) (ω_succ_closed hk) hg hφ,
    formulaSubstitutionGraph_negAtom membershipLanguageCode_valid (ω_succ_closed hn) (ω_succ_closed hk) ha]
  simp only [hstep, liftSubstitutionState, stateBound_code, stateFree_code]
  have he := substituted_guardArguments (E := liftFreeReplacement membershipLanguageCode ∅
    (stateTarget (G ‘ k)) (stateFree (G ‘ k))) hn hs.2.1 (hc.symm ▸ hs.2.2.1) hi hj hij
  simpa only [hc, boundedAllCode] using congrArg (fun args : V ↦ allCode (orCode (negAtomCode (relationToken 1) args)
    ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ))) he

theorem formulaSubstitutionGraph_boundedExists {G n i φ k j : V}
    (hn : n ∈ (ω : V)) (hi : i ∈ n) (hk : k ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n))
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ (G ‘ k))
    (hc : n = stateSource (G ‘ k))
    (hstep : G ‘ (succ k) = liftSubstitutionState membershipLanguageCode ∅ (G ‘ k))
    (hj : j ∈ stateTarget (G ‘ k)) (hij : (stateBound (G ‘ k)) ‘ i = boundVarCode j) :
    (formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨n, boundedExistsCode i φ⟩ₖ, k⟩ₖ =
      boundedExistsCode j ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ) := by
  have ha := boundedGuardArguments_valid hn hi
  have hg := (formulaSet_atoms membershipLanguageCode_valid (ω_succ_closed hn) ha).1
  rw [boundedExistsCode, formulaSubstitutionGraph_exists membershipLanguageCode_valid hn hk
    (formulaSet_binary membershipLanguageCode_valid (ω_succ_closed hn) hg hφ).1,
    formulaSubstitutionGraph_and membershipLanguageCode_valid (ω_succ_closed hn) (ω_succ_closed hk) hg hφ,
    formulaSubstitutionGraph_atom membershipLanguageCode_valid (ω_succ_closed hn) (ω_succ_closed hk) ha]
  simp only [hstep, liftSubstitutionState, stateBound_code, stateFree_code]
  have he := substituted_guardArguments (E := liftFreeReplacement membershipLanguageCode ∅
    (stateTarget (G ‘ k)) (stateFree (G ‘ k))) hn hs.2.1 (hc.symm ▸ hs.2.2.1) hi hj hij
  simpa only [hc, boundedExistsCode] using congrArg (fun args : V ↦ existsCode (andCode (atomCode (relationToken 1) args)
    ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ))) he

end ZFVP
