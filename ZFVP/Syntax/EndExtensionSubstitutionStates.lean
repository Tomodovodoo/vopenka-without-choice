import ZFVP.Syntax.EndExtensionTermEvaluation
import ZFVP.Syntax.EndExtensionAssignments
import ZFVP.Syntax.SubstitutionStates
import ZFVP.Syntax.MembershipSwap

/-! Term replacement and binder lifting commute with membership end
extensions. The iteration argument is internal to the target model, so
it covers every internal natural number without external well-foundedness. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem map_termSubstitutionStep (b e t previous : V) :
    j (termSubstitutionStep b e t previous) = termSubstitutionStep (j b) (j e) (j t) (j previous) := by
  have hz : kpair.π₁ (j t) = (0 : W) ↔ kpair.π₁ t = (0 : V) := by
    rw [← j.map_first, ← (show j (0 : V) = (0 : W) from j.map_numeral 0), j.injective.eq_iff]
  have ho : kpair.π₁ (j t) = (1 : W) ↔ kpair.π₁ t = (1 : V) := by
    rw [← j.map_first, ← (show j (1 : V) = (1 : W) from j.map_numeral 1), j.injective.eq_iff]
  simp only [termSubstitutionStep, hz, ho]
  split_ifs <;> simp only [j.map_value_total, j.map_first, j.map_second, j.map_compose, j.map_functionTermCode]
  all_goals tauto

theorem map_termSubstitution {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (Γ b e : V) :
    j (termSubstitution L Γ n b e) = termSubstitution (j L) (j Γ) (j n) (j b) (j e) := by
  symm
  apply (termSubstitution_eq_iff _ _ _ _ _ _).mpr
  rw [totalRecursionAttempt_iff]
  refine ⟨j.map_function _, ?_, ?_⟩
  · rw [← j.map_domain, domain_termSubstitution, j.map_termSet hL hn Γ]
  · intro u hu
    rw [← j.map_termSet hL hn Γ] at hu
    obtain ⟨t, ht, rfl⟩ := j.endExtension _ u hu
    rw [← j.map_value_total]
    have hrec := ((termSubstitution_eq_iff L Γ n b e _).mp rfl).1.2.2 t (by simpa using ht)
    rw [hrec, j.map_termSubstitutionStep, j.map_restrict, j.map_termPredecessors hL hn ht]

theorem map_boundShiftReplacement (n : V) : j (boundShiftReplacement n) = boundShiftReplacement (j n) := by
  exact j.map_definableGraph n (fun i ↦ boundVarCode (succ i)) (fun i ↦ boundVarCode (succ i))
    (by definability) (by definability) (fun i _ ↦ by rw [j.map_boundVarCode, j.map_succ])

theorem map_freeIdentityReplacement (Γ : V) : j (freeIdentityReplacement Γ) = freeIdentityReplacement (j Γ) := by
  exact j.map_definableGraph Γ freeVarCode freeVarCode (by definability) (by definability)
    (fun i _ ↦ j.map_freeVarCode i)

theorem map_boundVariableAssignment (n : V) : j (boundVariableAssignment n) = boundVariableAssignment (j n) := by
  exact j.map_definableGraph n boundVarCode boundVarCode (by definability) (by definability)
    (fun i _ ↦ j.map_boundVarCode i)

theorem map_shiftTwoIndices (n : V) : j (shiftTwoIndices n) = shiftTwoIndices (j n) := by
  exact j.map_definableGraph n (fun i ↦ succ (succ i)) (fun i ↦ succ (succ i))
    (by definability) (by definability) (fun i _ ↦ by rw [j.map_succ, j.map_succ])

theorem map_swapFirstTwoIndices (n : V) : j (swapFirstTwoIndices n) = swapFirstTwoIndices (j n) := by
  simp only [swapFirstTwoIndices, j.map_assignmentPrepend, j.map_succ, j.map_shiftTwoIndices,
    (show j (0 : V) = (0 : W) from j.map_numeral 0)]

theorem map_termBoundShift {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (Γ : V) :
    j (termBoundShift L Γ n) = termBoundShift (j L) (j Γ) (j n) := by
  rw [termBoundShift, j.map_termSubstitution hL hn, j.map_boundShiftReplacement, j.map_freeIdentityReplacement]
  rfl

theorem map_substitutionState (n m B E : V) :
    j (substitutionState n m B E) = substitutionState (j n) (j m) (j B) (j E) := by
  simp only [substitutionState, j.map_kpair]

theorem map_stateSource (s : V) : j (stateSource s) = stateSource (j s) := by
  simp only [stateSource, j.map_first]
theorem map_stateTarget (s : V) : j (stateTarget s) = stateTarget (j s) := by
  simp only [stateTarget, j.map_first, j.map_second]
theorem map_stateBound (s : V) : j (stateBound s) = stateBound (j s) := by
  simp only [stateBound, j.map_first, j.map_second]
theorem map_stateFree (s : V) : j (stateFree s) = stateFree (j s) := by
  simp only [stateFree, j.map_second]

theorem substitutionState_map {L Γ Δ s : V} (hL : IsLanguageCode L) (hs : IsSubstitutionState L Γ Δ s) :
    IsSubstitutionState (j L) (j Γ) (j Δ) (j s) := by
  unfold IsSubstitutionState
  rw [← j.map_stateSource, ← j.map_stateTarget, ← j.map_stateBound, ← j.map_stateFree,
    ← j.map_termSet hL hs.2.1 Δ]
  exact ⟨(j.natural_iff _).mpr hs.1, (j.natural_iff _).mpr hs.2.1,
    (j.function_iff _ _ _).mpr hs.2.2.1, (j.function_iff _ _ _).mpr hs.2.2.2⟩

theorem map_liftSubstitutionState {L Γ Δ s : V} (hL : IsLanguageCode L) (hs : IsSubstitutionState L Γ Δ s) :
    j (liftSubstitutionState L Δ s) = liftSubstitutionState (j L) (j Δ) (j s) := by
  simp only [liftSubstitutionState, liftBoundReplacement, liftFreeReplacement,
    j.map_substitutionState, j.map_assignmentPrepend, j.map_compose,
    j.map_termBoundShift hL hs.2.1, j.map_boundVarCode,
    (show j (0 : V) = (0 : W) from j.map_numeral 0), j.map_succ,
    j.map_stateSource, j.map_stateTarget, j.map_stateBound, j.map_stateFree]

theorem map_substitutionStates {L Γ Δ s : V} (hL : IsLanguageCode L) (hs : IsSubstitutionState L Γ Δ s) :
    j (substitutionStates L Δ s) = substitutionStates (j L) (j Δ) (j s) := by
  let := j.map_function (substitutionStates L Δ s)
  apply functions_eq_of_domain_values
  · rw [← j.map_domain, domain_substitutionStates, domain_substitutionStates, j.map_omega]
  · have hv : ∀ k ∈ (ω : W), (j (substitutionStates L Δ s)) ‘ k =
        (substitutionStates (j L) (j Δ) (j s)) ‘ k := by
      apply naturalNumber_induction (fun k ↦ (j (substitutionStates L Δ s)) ‘ k =
        (substitutionStates (j L) (j Δ) (j s)) ‘ k) (by definability)
      · rw [← (show j (0 : V) = (0 : W) from j.map_numeral 0), ← j.map_value_total,
          substitutionStates_zero, (show j (0 : V) = (0 : W) from j.map_numeral 0), substitutionStates_zero]
      · intro k hk ih
        obtain ⟨i, hi, rfl⟩ := j.endExtension ω k (by simpa only [j.map_omega] using hk)
        rw [← j.map_succ, ← j.map_value_total, substitutionStates_succ L Δ s hi,
          j.map_liftSubstitutionState hL (substitutionStates_valid hL hs hi), j.map_succ,
          substitutionStates_succ _ _ _ hk]
        rw [← j.map_value_total] at ih
        rw [ih]
    intro k hk
    apply hv k
    simpa only [← j.map_domain, domain_substitutionStates, j.map_omega] using hk

end MembershipEndExtension
end ZFVP
