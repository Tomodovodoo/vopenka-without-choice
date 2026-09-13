import ZFVP.ModelTheory.SchmerlInternalInfinitarySubstitutionSemantics

/-! Substitution from a single internal state. The complete sequence of
lifted states is constructed by internal recursion. Its image fragment is
valid and preserves internal countability, including for nonstandard omega. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def substituteCode (L F s φ : V) : V :=
  (infinitarySubstitutionGraph L F (substitutionStates L ∅ s)) ‘ ⟨⟨stateSource s, φ⟩ₖ, (0 : V)⟩ₖ

noncomputable def substitutionFragment (L F s : V) : V :=
  substitutedFragment L F (substitutionStates L ∅ s)

instance substituteCode_definable : ℒₛₑₜ-function₄[V] substituteCode := by
  unfold substituteCode
  definability

instance substitutionFragment_definable : ℒₛₑₜ-function₃[V] substitutionFragment := by
  unfold substitutionFragment
  definability

theorem substitutionFragment_valid {L F s : V} (hF : IsFragment L F)
    (hs : IsSubstitutionState L ∅ ∅ s) : IsFragment L (substitutionFragment L F s) := by
  apply substitutedFragment_valid hF
    (fun k hk ↦ substitutionStates_valid hF.1 hs hk)
  · intro k hk
    rw [substitutionStates_succ L ∅ s hk]
    simp only [liftSubstitutionState, stateSource_code]
  · intro k hk
    rw [substitutionStates_succ L ∅ s hk]
    simp only [liftSubstitutionState, stateTarget_code]

theorem substitutionFragment_countable {L F s : V} (hF : IsInternallyCountable F) :
    IsInternallyCountable (substitutionFragment L F s) := substitutedFragment_countable hF

theorem substituteCode_mem {L F s φ : V} (hφ : ⟨stateSource s, φ⟩ₖ ∈ F) :
    ⟨stateTarget s, substituteCode L F s φ⟩ₖ ∈ substitutionFragment L F s := by
  have hs0 := substitutionStates_zero L (∅ : V) s
  simpa only [substitutionFragment, substituteCode, hs0] using (substitutedNode_mem (L := L) (G := substitutionStates L ∅ s)
    hφ (k := (0 : V)) (by simp) (by rw [hs0]))

theorem holds_substituteCode {L F s M φ b : V} (hF : IsFragment L F)
    (hM : IsStructureCode L M) (hs : IsSubstitutionState L ∅ ∅ s)
    (hφ : ⟨stateSource s, φ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ stateTarget s) :
    Holds L (substitutionFragment L F s) M (stateTarget s) (substituteCode L F s φ) b ↔
      Holds L F M (stateSource s) φ
        (compose (stateBound s) (termEvaluation L ∅ (stateTarget s) M b ∅)) := by
  have hs0 := substitutionStates_zero L (∅ : V) s
  have h := holds_substitutionGraph hF hM
    (fun k hk ↦ substitutionStates_valid hF.1 hs hk)
    (fun k hk ↦ substitutionStates_succ L ∅ s hk)
    (stateSource s) φ hφ (0 : V) (by simp) (by rw [hs0]) b (by simpa only [hs0] using hb)
  simpa only [substitutionFragment, substituteCode, substitutedAssignment, hs0, substitutionTargetEvaluation,
    evaluateWithFreeAssignment] using h

end ZFVP.Infinitary.Internal
