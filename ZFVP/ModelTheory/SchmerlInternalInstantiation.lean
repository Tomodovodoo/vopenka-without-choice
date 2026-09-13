import ZFVP.ModelTheory.SchmerlInternalSubstitutionTransport
import ZFVP.ModelTheory.SchmerlInternalQuantifierAxioms

/-! Universal elimination and existential introduction for arbitrary internal
terms. Substitution lifts under binders and evaluates to the actual witness
assignment, including in nonstandard finite contexts. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def instantiationState (n t : V) : V :=
  substitutionState (succ n) n (assignmentPrepend n (boundVariableAssignment n) t) ∅

instance instantiationState_definable : ℒₛₑₜ-function₂[V] instantiationState := by
  unfold instantiationState substitutionState
  have hB : ℒₛₑₜ-function₁[V] boundVariableAssignment := boundVariableAssignmentFormula_defined.to_definable
  let := hB
  definability

theorem instantiationState_valid {L n t : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (ht : t ∈ termSet L ∅ n) : IsSubstitutionState L ∅ ∅ (instantiationState n t) := by
  simp only [instantiationState, IsSubstitutionState, stateSource_code, stateTarget_code,
    stateBound_code, stateFree_code]
  exact ⟨ω_succ_closed hn, hn,
    assignmentPrepend_mem_function hn (boundVariableAssignment_mem_language hL hn) ht,
    mem_function.intro (by simp) (by simp)⟩

theorem instantiationState_assignment {L M n t b : V} (hL : IsLanguageCode L)
    (hM : IsStructureCode L M) (hn : n ∈ (ω : V)) (ht : t ∈ termSet L ∅ n)
    (hb : b ∈ structureDomain M ^ n) :
    compose (stateBound (instantiationState n t)) (termEvaluation L ∅ n M b ∅) =
      assignmentPrepend n b ((termEvaluation L ∅ n M b ∅) ‘ t) := by
  have he : (∅ : V) ∈ structureDomain M ^ (∅ : V) := mem_function.intro (by simp) (by simp)
  have hT := termEvaluation_mem_function hM hn ∅ hb he
  have hB := boundVariableAssignment_mem_language hL hn
  have hidentity : compose (boundVariableAssignment n) (termEvaluation L ∅ n M b ∅) = b := by
    apply function_eq_of_values (compose_function hB hT) hb
    intro i hi
    rw [value_compose_of_mem_function hB hT hi, boundVariableAssignment_value hi,
      termEvaluation_boundVar hL hn ∅ M b ∅ hi]
  simp only [instantiationState, stateBound_code]
  rw [compose_assignmentPrepend hn hB hT ht, hidentity]

noncomputable def instantiateCode (L H n t φ : V) : V :=
  substituteCode L H (instantiationState n t) φ

instance instantiateCode_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (instantiateCode : V → V → V → V → V → V) := by
  unfold instantiateCode
  exact Language.DefinableFunction₄.comp (by definability) (by definability)
    (Language.DefinableFunction₂.comp (F := instantiationState) (by definability) (by definability)) (by definability)

theorem holds_instantiateCode {L H F M n t φ b : V} (hH : IsFragment L H) (hF : IsFragment L F)
    (hM : IsStructureCode L M) (hn : n ∈ (ω : V)) (ht : t ∈ termSet L ∅ n)
    (hφ : ⟨succ n, φ⟩ₖ ∈ H) (hinst : ⟨n, instantiateCode L H n t φ⟩ₖ ∈ F)
    (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n (instantiateCode L H n t φ) b ↔
      Holds L H M (succ n) φ (assignmentPrepend n b ((termEvaluation L ∅ n M b ∅) ‘ t)) := by
  have hs := instantiationState_valid hH.1 hn ht
  have hsφ : ⟨stateSource (instantiationState n t), φ⟩ₖ ∈ H := by
    simpa only [instantiationState, stateSource_code] using hφ
  have hsource : stateSource (instantiationState n t) = succ n := by
    simp only [instantiationState, stateSource_code]
  have htarget : stateTarget (instantiationState n t) = n := by
    simp only [instantiationState, stateTarget_code]
  have hsinst := substituteCode_mem (L := L) hsφ
  rw [htarget] at hsinst
  have hsub := holds_substituteCode hH hM hs hsφ (b := b) (htarget.symm ▸ hb)
  rw [hsource, htarget, instantiationState_assignment hH.1 hM hn ht hb] at hsub
  exact (holds_fragment_iff hF (substitutionFragment_valid hH hs) _ _ hinst hsinst b).trans hsub

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₅.comp

def IsQuantifierInstantiationAxiom (L n χ : V) : Prop := ∃ H φ t,
  n ∈ (ω : V) ∧ IsFragment L H ∧ ⟨succ n, φ⟩ₖ ∈ H ∧ t ∈ termSet L ∅ n ∧
  (χ = impCode (allCode φ) (instantiateCode L H n t φ) ∨
    χ = impCode (instantiateCode L H n t φ) (exsCode φ))

instance isQuantifierInstantiationAxiom_definable : ℒₛₑₜ-relation₃[V] IsQuantifierInstantiationAxiom := by
  unfold IsQuantifierInstantiationAxiom
  definability

theorem IsQuantifierInstantiationAxiom.sound {L F M n χ b : V}
    (hχ : IsQuantifierInstantiationAxiom L n χ) (hF : IsFragment L F)
    (hM : IsStructureCode L M) (hc : ⟨n, χ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n χ b := by
  obtain ⟨H, φ, t, hn, hH, hφ, ht, hχ⟩ := hχ
  have he : (∅ : V) ∈ structureDomain M ^ (∅ : V) := mem_function.intro (by simp) (by simp)
  have hx := function_value_mem (termEvaluation_mem_function hM hn ∅ hb he) ht
  rcases hχ with rfl | rfl
  · have hall := hF.imp_left_mem hc
    have hi := hF.imp_right_mem hc
    rw [holds_imp hF hc hb, holds_all hF hall hb,
      holds_instantiateCode hH hF hM hn ht hφ hi hb]
    intro h
    exact (holds_fragment_iff hH hF _ _ hφ (hF.all_mem hall) _).mpr (h _ hx)
  · have hi := hF.imp_left_mem hc
    have hex := hF.imp_right_mem hc
    rw [holds_imp hF hc hb, holds_instantiateCode hH hF hM hn ht hφ hi hb, holds_exs hF hex hb]
    intro h
    exact ⟨_, hx, (holds_fragment_iff hF hH _ _ (hF.exs_mem hex) hφ _).mpr h⟩

namespace EndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem map_instantiationState (n t : V) : j (instantiationState n t) = instantiationState (j n) (j t) := by
  simp only [instantiationState, j.map_substitutionState, j.map_succ,
    j.map_assignmentPrepend, j.map_boundVariableAssignment, j.map_empty]

theorem map_instantiateCode {L H n t : V} (hH : IsFragment L H)
    (hn : n ∈ (ω : V)) (ht : t ∈ termSet L ∅ n) (φ : V) :
    j (instantiateCode L H n t φ) = instantiateCode (j L) (j H) (j n) (j t) (j φ) := by
  rw [instantiateCode, map_substituteCode j hH (instantiationState_valid hH.1 hn ht), map_instantiationState]
  rfl

theorem quantifierInstantiationAxiom_map {L n χ : V} (hχ : IsQuantifierInstantiationAxiom L n χ) :
    IsQuantifierInstantiationAxiom (j L) (j n) (j χ) := by
  obtain ⟨H, φ, t, hn, hH, hφ, ht, hχ⟩ := hχ
  refine ⟨j H, j φ, j t, (j.natural_iff _).mpr hn, fragment_map j hH, ?_, ?_, ?_⟩
  · simpa only [j.map_kpair, j.map_succ] using (j.mem_iff _ _).mpr hφ
  · simpa only [j.map_termSet hH.1 hn, j.map_empty] using (j.mem_iff _ _).mpr ht
  · rcases hχ with rfl | rfl
    · exact Or.inl (by rw [map_impCode, map_allCode, map_instantiateCode j hH hn ht])
    · exact Or.inr (by rw [map_impCode, map_exsCode, map_instantiateCode j hH hn ht])

end EndExtension
end ZFVP.Infinitary.Internal
