import ZFVP.Syntax.FormulaSubstitutionComposition
import ZFVP.Syntax.MembershipSubstitutionGuards

/-! Capture-avoiding composition of membership substitutions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def membershipStateTermMap (s : V) : V :=
  termSubstitution membershipLanguageCode ∅ (stateSource s) (stateBound s) (stateFree s)

instance membershipStateTermMap_definable : ℒₛₑₜ-function₁[V] membershipStateTermMap := by
  unfold membershipStateTermMap
  exact Language.DefinableFunction₅.comp (by definability) (by definability) (by definability)
    (by definability) (by definability)

theorem membershipStateTermMap_function {s : V} (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s) :
    membershipStateTermMap s ∈ (termSet membershipLanguageCode ∅ (stateTarget s)) ^
      (termSet membershipLanguageCode ∅ (stateSource s)) :=
  termSubstitution_mem_function membershipLanguageCode_valid hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

theorem membershipStateTermMap_boundVar {s i : V}
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s) (hi : i ∈ stateSource s) :
    (membershipStateTermMap s) ‘ (boundVarCode i) = (stateBound s) ‘ i :=
  termSubstitution_boundVar membershipLanguageCode_valid hs.1 _ _ _ hi

def IsMembershipStateComposition (s t u : V) : Prop :=
  stateSource t = stateTarget s ∧ stateSource u = stateSource s ∧ stateTarget u = stateTarget t ∧
    ∀ i ∈ stateSource s, (membershipStateTermMap t) ‘ ((stateBound s) ‘ i) = (stateBound u) ‘ i

instance membershipStateComposition_definable : ℒₛₑₜ-relation₃[V] IsMembershipStateComposition := by
  unfold IsMembershipStateComposition
  definability

theorem IsMembershipStateComposition.termMaps {s t u : V}
    (h : IsMembershipStateComposition s t u)
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s)
    (ht : IsSubstitutionState membershipLanguageCode ∅ ∅ t)
    (hu : IsSubstitutionState membershipLanguageCode ∅ ∅ u) :
    compose (membershipStateTermMap s) (membershipStateTermMap t) = membershipStateTermMap u := by
  have hsf := membershipStateTermMap_function hs
  have htf := membershipStateTermMap_function ht
  have huf := membershipStateTermMap_function hu
  rw [h.1] at htf
  rw [h.2.1, h.2.2.1] at huf
  apply function_eq_of_values (compose_function hsf htf) huf
  intro x hx
  obtain ⟨i, hi, rfl⟩ := membershipTerm_cases hs.1 hx
  rw [value_compose_of_mem_function hsf htf hx, membershipStateTermMap_boundVar hs hi,
    membershipStateTermMap_boundVar hu (h.2.1.symm ▸ hi)]
  exact h.2.2.2 i hi

theorem IsMembershipStateComposition.lift {s t u : V}
    (h : IsMembershipStateComposition s t u)
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s)
    (ht : IsSubstitutionState membershipLanguageCode ∅ ∅ t)
    (hu : IsSubstitutionState membershipLanguageCode ∅ ∅ u) :
    IsMembershipStateComposition (liftSubstitutionState membershipLanguageCode ∅ s)
      (liftSubstitutionState membershipLanguageCode ∅ t)
      (liftSubstitutionState membershipLanguageCode ∅ u) := by
  have hls := liftSubstitutionState_valid membershipLanguageCode_valid hs
  have hlt := liftSubstitutionState_valid membershipLanguageCode_valid ht
  have hB (v : V) : stateBound (liftSubstitutionState membershipLanguageCode ∅ v) =
      liftBoundReplacement membershipLanguageCode ∅ (stateTarget v) (stateSource v) (stateBound v) := by
    simp only [liftSubstitutionState, stateBound_code]
  refine ⟨by simpa [liftSubstitutionState] using congrArg succ h.1,
    by simpa [liftSubstitutionState] using congrArg succ h.2.1,
    by simpa [liftSubstitutionState] using congrArg succ h.2.2.1, ?_⟩
  intro i hi
  have hiω := IsOrdinal.toIsTransitive.mem_trans hi hls.1
  rcases internalNatural_cases hiω with rfl | ⟨j, hj, rfl⟩
  · rw [hB s, hB u, liftBoundReplacement_zero hs.1, liftBoundReplacement_zero hu.1,
      membershipStateTermMap_boundVar hlt (by
        simpa only [liftSubstitutionState, stateSource_code] using zero_mem_succ_natural ht.1), hB t]
    exact liftBoundReplacement_zero ht.1 _ _ _ _
  · have hj' : j ∈ stateSource s := by
      have he : succ j ≠ (0 : V) := by
        intro hz
        have hh : j ∈ succ j := by simp
        rw [hz] at hh
        exact not_mem_empty hh
      have hp := natural_predecessor_mem hs.1
        (by simpa only [liftSubstitutionState, stateSource_code] using hi) he
      have : IsOrdinal j := IsOrdinal.of_mem hj
      simpa only [sUnion_succ_of_transitive] using hp
    obtain ⟨a, ha, hsa⟩ := substitutionState_bound_index hs hj'
    have hat : a ∈ stateSource t := h.1.symm ▸ ha
    obtain ⟨b, hb, htb⟩ := substitutionState_bound_index ht hat
    have hub : (stateBound u) ‘ j = boundVarCode b := by
      have hh := h.2.2.2 j hj'
      rw [hsa, membershipStateTermMap_boundVar ht hat, htb] at hh
      exact hh.symm
    have hjU : j ∈ stateSource u := h.2.1.symm ▸ hj'
    have hbU : b ∈ stateTarget u := h.2.2.1.symm ▸ hb
    rw [hB s, hB u]
    rw [liftBoundReplacement_succ membershipLanguageCode_valid hs.2.1 hs.1 hs.2.2.1 hj', hsa,
      termBoundShift_boundVar membershipLanguageCode_valid hs.2.1 ∅ ha,
      membershipStateTermMap_boundVar hlt (by
        simpa only [liftSubstitutionState, stateSource_code] using succ_mem_succ_of_natural_mem ht.1 hat), hB t]
    rw [liftBoundReplacement_succ membershipLanguageCode_valid ht.2.1 ht.1 ht.2.2.1 hat, htb,
      termBoundShift_boundVar membershipLanguageCode_valid ht.2.1 ∅ hb,
      liftBoundReplacement_succ membershipLanguageCode_valid hu.2.1 hu.1 hu.2.2.1 hjU, hub,
      termBoundShift_boundVar membershipLanguageCode_valid hu.2.1 ∅ hbU]

theorem IsMembershipStateComposition.iterated {s t u k : V}
    (h : IsMembershipStateComposition s t u)
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s)
    (ht : IsSubstitutionState membershipLanguageCode ∅ ∅ t)
    (hu : IsSubstitutionState membershipLanguageCode ∅ ∅ u) (hk : k ∈ (ω : V)) :
    IsMembershipStateComposition ((substitutionStates membershipLanguageCode ∅ s) ‘ k)
      ((substitutionStates membershipLanguageCode ∅ t) ‘ k)
      ((substitutionStates membershipLanguageCode ∅ u) ‘ k) := by
  apply naturalNumber_induction (fun k ↦
    IsMembershipStateComposition ((substitutionStates membershipLanguageCode ∅ s) ‘ k)
      ((substitutionStates membershipLanguageCode ∅ t) ‘ k)
      ((substitutionStates membershipLanguageCode ∅ u) ‘ k)) (by definability) ?_ ?_ k hk
  · simpa only [substitutionStates_zero] using h
  · intro k hk ih
    rw [substitutionStates_succ _ _ _ hk, substitutionStates_succ _ _ _ hk, substitutionStates_succ _ _ _ hk]
    exact ih.lift (substitutionStates_valid membershipLanguageCode_valid hs hk)
      (substitutionStates_valid membershipLanguageCode_valid ht hk)
      (substitutionStates_valid membershipLanguageCode_valid hu hk)

theorem substituteMembershipFormula_compose {s t u φ : V}
    (h : IsMembershipStateComposition s t u)
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s)
    (ht : IsSubstitutionState membershipLanguageCode ∅ ∅ t)
    (hu : IsSubstitutionState membershipLanguageCode ∅ ∅ u)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (stateSource s)) :
    substituteFormula membershipLanguageCode ∅ ∅ t (substituteFormula membershipLanguageCode ∅ ∅ s φ) =
      substituteFormula membershipLanguageCode ∅ ∅ u φ := by
  let G := substitutionStates membershipLanguageCode ∅ s
  let H := substitutionStates membershipLanguageCode ∅ t
  let J := substitutionStates membershipLanguageCode ∅ u
  have hc := formulaSubstitutionGraph_compose (G := G) (H := H) (J := J) membershipLanguageCode_valid
    (fun k hk ↦ substitutionStates_valid membershipLanguageCode_valid hs hk)
    (fun k hk ↦ by simp only [G, substitutionStates_succ _ _ _ hk, liftSubstitutionState, stateSource_code])
    (fun k hk ↦ by simp only [G, substitutionStates_succ _ _ _ hk, liftSubstitutionState, stateTarget_code])
    (by
      intro k hk
      have hi := h.iterated hs ht hu hk
      have hh := hi.termMaps (substitutionStates_valid membershipLanguageCode_valid hs hk)
        (substitutionStates_valid membershipLanguageCode_valid ht hk)
        (substitutionStates_valid membershipLanguageCode_valid hu hk)
      simpa only [membershipStateTermMap, hi.1, hi.2.1, G, H, J] using hh)
    (stateSource s) φ hφ (0 : V) (by simp) (by simp [G, substitutionStates_zero])
  simpa only [G, H, J, substitutionStates_zero, substituteFormula, h.1, h.2.1] using hc

end ZFVP
