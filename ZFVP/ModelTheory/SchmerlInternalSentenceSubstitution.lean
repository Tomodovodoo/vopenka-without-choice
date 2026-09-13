import ZFVP.ModelTheory.SchmerlInternalSubstitutionComposition
import ZFVP.ModelTheory.SchmerlInternalOrdinaryQuantifierAxioms

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Binder lifting fixes all variables introduced since the initial state. -/
theorem substitutionStates_bound_prefix {L s : V} (hL : IsLanguageCode L)
    (hs : IsSubstitutionState L ∅ ∅ s) :
    ∀ k ∈ (ω : V), k ⊆ stateSource ((substitutionStates L ∅ s) ‘ k) ∧
      k ⊆ stateTarget ((substitutionStates L ∅ s) ‘ k) ∧
      ∀ i ∈ k, (stateBound ((substitutionStates L ∅ s) ‘ k)) ‘ i = boundVarCode i := by
  apply naturalNumber_induction (fun k ↦
    k ⊆ stateSource ((substitutionStates L ∅ s) ‘ k) ∧
      k ⊆ stateTarget ((substitutionStates L ∅ s) ‘ k) ∧
      ∀ i ∈ k, (stateBound ((substitutionStates L ∅ s) ‘ k)) ‘ i = boundVarCode i)
    (by definability) ?_ ?_
  · simp only [zero_def]
    exact ⟨empty_subset _, empty_subset _, fun i hi ↦ False.elim (not_mem_empty hi)⟩
  · intro k hk ih
    have hv := substitutionStates_valid hL hs hk
    rw [substitutionStates_succ _ _ _ hk]
    simp only [liftSubstitutionState, stateSource_code, stateTarget_code, stateBound_code]
    have hsub {a : V} (ha : a ∈ (ω : V)) (hka : k ⊆ a) : succ k ⊆ succ a := by
      have : IsOrdinal k := IsOrdinal.of_mem hk
      have : IsOrdinal a := IsOrdinal.of_mem ha
      intro i hi
      rcases mem_succ_iff.mp hi with rfl | hi
      · exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hka)
      · exact mem_succ_iff.mpr (Or.inr (hka i hi))
    refine ⟨hsub hv.1 ih.1, hsub hv.2.1 ih.2.1, ?_⟩
    intro i hi
    have hiω := IsOrdinal.toIsTransitive.mem_trans hi (ω_succ_closed hk)
    rcases internalNatural_cases hiω with rfl | ⟨j, hj, rfl⟩
    · exact liftBoundReplacement_zero hv.1 _ _ _ _
    · have hjk : j ∈ k := by
        have hne : succ j ≠ (0 : V) := by
          intro hz
          have hh : j ∈ succ j := by simp
          rw [hz] at hh
          exact not_mem_empty hh
        have hh := natural_predecessor_mem hk hi hne
        have : IsOrdinal j := IsOrdinal.of_mem hj
        simpa only [sUnion_succ_of_transitive] using hh
      rw [liftBoundReplacement_succ hL hv.2.1 hv.1 hv.2.2.1 (ih.1 j hjk),
        ih.2.2 j hjk, termBoundShift_boundVar hL hv.2.1 ∅ (ih.2.1 j hjk)]

theorem substitutionStates_source_zero {L s : V} (hz : stateSource s = 0) :
    ∀ k ∈ (ω : V), stateSource ((substitutionStates L ∅ s) ‘ k) = k := by
  apply naturalNumber_induction (fun k ↦ stateSource ((substitutionStates L ∅ s) ‘ k) = k)
    (by definability) ?_ ?_
  · simpa only [substitutionStates_zero] using hz
  · intro k hk ih
    rw [substitutionStates_succ _ _ _ hk]
    simpa only [liftSubstitutionState, stateSource_code] using congrArg succ ih

/-- Replacement tables fixing a prefix fix every term in that context. -/
theorem termSubstitution_fixed_prefix {L n m B E : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hnm : n ⊆ m)
    (hB : ∀ i ∈ n, B ‘ i = boundVarCode i) :
    ∀ t ∈ termSet L ∅ n, t ∈ termSet L ∅ m ∧ (termSubstitution L ∅ m B E) ‘ t = t := by
  apply termSet_induction hL hn ∅ (fun t ↦
    t ∈ termSet L ∅ m ∧ (termSubstitution L ∅ m B E) ‘ t = t) (by definability)
  · intro i hi
    exact ⟨(termSet_closed hL hm ∅).1 i (hnm i hi),
      (termSubstitution_boundVar hL hm ∅ B E (hnm i hi)).trans (hB i hi)⟩
  · intro x hx
    exact False.elim (not_mem_empty hx)
  · intro f hf args ha ih
    have ha' : args ∈ termSet L ∅ m ^ ((functionArities L) ‘ f) :=
      mem_function_of_mem_function_of_subset (mem_function_range_of_mem_function ha) (by
        intro t ht
        exact (ih t ht).1)
    have ht := (termSet_closed hL hm ∅).2.2 f hf args ha'
    refine ⟨ht, ?_⟩
    rw [termSubstitution_function hL hm ∅ B E ht]
    apply congrArg (functionTermCode f)
    have hT : termSubstitution L ∅ m B E ∈ range (termSubstitution L ∅ m B E) ^ termSet L ∅ m := by
      simpa only [domain_termSubstitution] using (IsFunction.mem_function (termSubstitution L ∅ m B E))
    have : IsFunction args := IsFunction.of_mem ha
    have : IsFunction (compose args (termSubstitution L ∅ m B E)) := IsFunction.of_mem (compose_function ha' hT)
    apply functions_eq_of_domain_values (domain_eq_of_mem_function (compose_function ha' hT) |>.trans (domain_eq_of_mem_function ha).symm)
    intro i hi
    rw [domain_eq_of_mem_function (compose_function ha' hT)] at hi
    rw [value_compose_of_mem_function ha' hT hi]
    exact (ih _ (mem_range_of_kpair_mem (kpair_value_mem (by rwa [domain_eq_of_mem_function ha])))).2

theorem termSubstitution_identity_of_bound {L n B E : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hB : ∀ i ∈ n, B ‘ i = boundVarCode i) :
    termSubstitution L ∅ n B E = SetTheory.identity (termSet L ∅ n) := by
  apply functions_eq_of_domain_values (by rw [domain_termSubstitution, domain_eq_of_mem_function (identity_mem_function _)])
  intro t ht
  rw [domain_termSubstitution] at ht
  rw [identity_value ht]
  exact (termSubstitution_fixed_prefix hL hn hn (subset_refl _) hB t ht).2

theorem substitutionStates_context_match {L s t : V} (h : stateTarget s = stateSource t) :
    ∀ k ∈ (ω : V), stateTarget ((substitutionStates L ∅ s) ‘ k) =
      stateSource ((substitutionStates L ∅ t) ‘ k) := by
  apply naturalNumber_induction (fun k ↦ stateTarget ((substitutionStates L ∅ s) ‘ k) =
    stateSource ((substitutionStates L ∅ t) ‘ k)) (by definability) ?_ ?_
  · simpa only [substitutionStates_zero] using h
  · intro k hk ih
    rw [substitutionStates_succ _ _ _ hk, substitutionStates_succ _ _ _ hk]
    simpa only [liftSubstitutionState, stateTarget_code, stateSource_code] using congrArg succ ih

theorem substituteCode_closed_eq {L F s φ : V} (hF : IsFragment L F)
    (hs : IsSubstitutionState L ∅ ∅ s) (hz : stateSource s = 0)
    (hφ : ⟨(0 : V), φ⟩ₖ ∈ F) : substituteCode L F s φ = φ := by
  have ht : ∀ k ∈ (ω : V),
      termSubstitution L ∅ (stateSource ((substitutionStates L ∅ s) ‘ k))
        (stateBound ((substitutionStates L ∅ s) ‘ k)) (stateFree ((substitutionStates L ∅ s) ‘ k)) =
        SetTheory.identity (termSet L ∅ (stateSource ((substitutionStates L ∅ s) ‘ k))) := by
    intro k hk
    rw [substitutionStates_source_zero hz k hk]
    exact termSubstitution_identity_of_bound hF.1 hk (substitutionStates_bound_prefix hF.1 hs k hk).2.2
  have hh := infinitarySubstitutionGraph_identity hF (G := substitutionStates L ∅ s)
    (fun k hk ↦ by rw [substitutionStates_succ _ _ _ hk]; simp only [liftSubstitutionState, stateSource_code])
    ht 0 φ hφ 0 (by simp) (by rw [substitutionStates_zero, hz])
  simpa only [substituteCode, hz] using hh

/-- Composition on a lifted sentence, with arbitrary well-typed second replacement. -/
theorem substituteCode_closed_composition {L F s t φ : V} (hF : IsFragment L F)
    (hs : IsSubstitutionState L ∅ ∅ s) (ht : IsSubstitutionState L ∅ ∅ t)
    (hz : stateSource s = 0) (hc : stateTarget s = stateSource t)
    (hφ : ⟨(0 : V), φ⟩ₖ ∈ F) :
    substituteCode L (substitutionFragment L F s) t (substituteCode L F s φ) = φ := by
  let G := substitutionStates L ∅ s
  let H := substitutionStates L ∅ t
  have hterms : ∀ k ∈ (ω : V),
      compose (termSubstitution L ∅ (stateSource (G ‘ k)) (stateBound (G ‘ k)) (stateFree (G ‘ k)))
        (termSubstitution L ∅ (stateTarget (G ‘ k)) (stateBound (H ‘ k)) (stateFree (H ‘ k))) =
      termSubstitution L ∅ (stateSource (G ‘ k)) (stateBound (G ‘ k)) (stateFree (G ‘ k)) := by
    intro k hk
    have hG := substitutionStates_valid hF.1 hs hk
    have hH := substitutionStates_valid hF.1 ht hk
    have hsource : stateSource (G ‘ k) = k := substitutionStates_source_zero hz k hk
    have hmatch : stateTarget (G ‘ k) = stateSource (H ‘ k) := substitutionStates_context_match hc k hk
    have hprefixG := substitutionStates_bound_prefix hF.1 hs k hk
    have hprefixH := substitutionStates_bound_prefix hF.1 ht k hk
    have hfirst := termSubstitution_mem_function hF.1 hG.1 hG.2.1 hG.2.2.1 hG.2.2.2
    have hsecond := termSubstitution_mem_function hF.1 hH.1 hH.2.1 hH.2.2.1 hH.2.2.2
    change termSubstitution L ∅ (stateSource (G ‘ k)) (stateBound (G ‘ k)) (stateFree (G ‘ k)) ∈
      termSet L ∅ (stateTarget (G ‘ k)) ^ termSet L ∅ (stateSource (G ‘ k)) at hfirst
    change termSubstitution L ∅ (stateSource (H ‘ k)) (stateBound (H ‘ k)) (stateFree (H ‘ k)) ∈
      termSet L ∅ (stateTarget (H ‘ k)) ^ termSet L ∅ (stateSource (H ‘ k)) at hsecond
    rw [← hmatch] at hsecond
    have hcomp := compose_function hfirst hsecond
    have : IsFunction (compose (termSubstitution L ∅ (stateSource (G ‘ k)) (stateBound (G ‘ k)) (stateFree (G ‘ k)))
        (termSubstitution L ∅ (stateTarget (G ‘ k)) (stateBound (H ‘ k)) (stateFree (H ‘ k)))) := IsFunction.of_mem hcomp
    apply functions_eq_of_domain_values ((domain_eq_of_mem_function hcomp).trans (domain_eq_of_mem_function hfirst).symm)
    intro a ha
    rw [domain_eq_of_mem_function hcomp, hsource] at ha
    rw [value_compose_of_mem_function hfirst hsecond (by rwa [hsource]), hsource]
    have he := (termSubstitution_fixed_prefix (E := stateFree (G ‘ k)) hF.1 hk hk (subset_refl _) hprefixG.2.2 a ha).2
    rw [he, hmatch]
    exact (termSubstitution_fixed_prefix hF.1 hk hH.1 hprefixH.1 hprefixH.2.2 a ha).2
  have hh := infinitarySubstitutionGraph_compose hF
    (G := G) (H := H) (J := G) (fun k hk ↦ substitutionStates_valid hF.1 hs hk)
    (fun k hk ↦ by dsimp [G]; rw [substitutionStates_succ _ _ _ hk]; simp only [liftSubstitutionState, stateSource_code])
    (fun k hk ↦ by dsimp [G]; rw [substitutionStates_succ _ _ _ hk]; simp only [liftSubstitutionState, stateTarget_code])
    hterms 0 φ hφ 0 (by simp) (by dsimp [G]; rw [substitutionStates_zero, hz])
  have heq : substituteCode L (substitutionFragment L F s) t (substituteCode L F s φ) = substituteCode L F s φ := by
    simpa only [substituteCode, substitutionFragment, G, H, substitutionStates_zero, hz, hc] using hh
  exact heq.trans (substituteCode_closed_eq hF hs hz hφ)

/-- A closed sentence viewed in an arbitrary internal variable context. -/
noncomputable def sentenceLiftCode (L F n φ : V) : V := renameCode L F 0 n ∅ φ

noncomputable def sentenceLiftFragment (L F n : V) : V := renamedFragment L F 0 n ∅

instance sentenceLiftCode_definable : ℒₛₑₜ-function₄[V] sentenceLiftCode := by
  unfold sentenceLiftCode renameCode
  definability

instance sentenceLiftFragment_definable : ℒₛₑₜ-function₃[V] sentenceLiftFragment := by
  unfold sentenceLiftFragment renamedFragment
  definability

theorem sentenceLiftFragment_valid {L F n : V} (hF : IsFragment L F) (hn : n ∈ (ω : V)) :
    IsFragment L (sentenceLiftFragment L F n) :=
  renamedFragment_valid hF (by simp) hn (mem_function.intro (by simp [zero_def]) (by simp [zero_def]))

theorem sentenceLiftFragment_countable {L F n : V} (hF : IsInternallyCountable F) :
    IsInternallyCountable (sentenceLiftFragment L F n) := renamedFragment_countable hF

theorem sentenceLiftCode_mem {L F n φ : V} (hφ : ⟨(0 : V), φ⟩ₖ ∈ F) :
    ⟨n, sentenceLiftCode L F n φ⟩ₖ ∈ sentenceLiftFragment L F n := renameCode_mem hφ

/-- Closed syntax is literally unchanged by this lift, at every internal context. -/
theorem sentenceLiftCode_eq {L F n φ : V} (hF : IsFragment L F)
    (hn : n ∈ (ω : V)) (hφ : ⟨(0 : V), φ⟩ₖ ∈ F) : sentenceLiftCode L F n φ = φ := by
  apply substituteCode_closed_eq hF
    (renamingState_valid hF.1 (by simp) hn (mem_function.intro (by simp [zero_def]) (by simp [zero_def])))
    (by simp only [renamingState, stateSource_code]) hφ

theorem sentenceLiftCode_zero {L F φ : V} (hF : IsFragment L F)
    (hφ : ⟨(0 : V), φ⟩ₖ ∈ F) : sentenceLiftCode L F 0 φ = φ :=
  sentenceLiftCode_eq hF (by simp) hφ

/-- Exact simultaneous substitution of a lifted sentence, in any valid input fragment. -/
theorem substituteCode_sentenceLift {L F H s φ : V} (hF : IsFragment L F)
    (hH : IsFragment L H) (hs : IsSubstitutionState L ∅ ∅ s)
    (hφ : ⟨(0 : V), φ⟩ₖ ∈ F)
    (hHφ : ⟨stateSource s, sentenceLiftCode L F (stateSource s) φ⟩ₖ ∈ H) :
    substituteCode L H s (sentenceLiftCode L F (stateSource s) φ) =
      sentenceLiftCode L F (stateTarget s) φ := by
  rw [substituteCode_fragment_eq hH (sentenceLiftFragment_valid hF hs.1) hHφ (sentenceLiftCode_mem hφ),
    sentenceLiftCode_eq hF hs.2.1 hφ]
  exact substituteCode_closed_composition hF
    (renamingState_valid hF.1 (by simp) hs.1
      (mem_function.intro (by simp [zero_def]) (by simp [zero_def]))) hs
    (by simp only [renamingState, stateSource_code]) (by simp only [renamingState, stateTarget_code]) hφ

/-- Exact successor weakening of a lifted sentence, in any valid input fragment. -/
theorem weakenCode_sentenceLift {L F H n φ : V} (hF : IsFragment L F)
    (hH : IsFragment L H) (hn : n ∈ (ω : V)) (hφ : ⟨(0 : V), φ⟩ₖ ∈ F)
    (hHφ : ⟨n, sentenceLiftCode L F n φ⟩ₖ ∈ H) :
    weakenCode L H n (sentenceLiftCode L F n φ) = sentenceLiftCode L F (succ n) φ := by
  have hs := renamingState_valid hF.1 hn (ω_succ_closed hn) (successorIndices_function hn)
  have hh := substituteCode_sentenceLift hF hH hs hφ
    (by simpa only [renamingState, stateSource_code] using hHφ)
  simpa only [weakenCode, renameCode, renamingState, stateSource_code, stateTarget_code] using hh

end ZFVP.Infinitary.Internal
