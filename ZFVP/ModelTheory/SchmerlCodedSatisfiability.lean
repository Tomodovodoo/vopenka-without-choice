import ZFVP.ModelTheory.SchmerlEndExtensionFragmentCoding

/-! Satisfiability inside an ambient ZF model. A witness is an internal
structure code, and Q uses internal countability. Logical equality is already
literal equality in `AtomicHolds`; it needs no extra relation interpretation.
Old witnesses survive membership end extensions that preserve omega-one. -/

set_option autoImplicit false

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A closed sentence in a valid internal fragment has a nonempty internal
model. The sentence-node condition is part of the predicate. -/
structure CodedSatisfiable (L H φ : V) : Prop where
  fragment : IsFragment L H
  sentence : ⟨(0 : V), φ⟩ₖ ∈ H
  model : ∃ M : V, IsStructureCode L M ∧ Holds L H M (0 : V) φ ∅

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The original coded model witnesses upward satisfiability. This applies
to all internal fragments, including countable ones, without standard omega
or external well-foundedness assumptions. -/
theorem CodedSatisfiable.map_endExtension {L H φ : V}
    (h : CodedSatisfiable L H φ) (j : MembershipEndExtension V W)
    (hAC : InternalChoice V)
    (hω₁ : j (hartogsNumber (ω : V)) = hartogsNumber (ω : W)) :
    CodedSatisfiable (j L) (j H) (j φ) := by
  have hzero : j (0 : V) = (0 : W) := j.map_numeral 0
  refine ⟨EndExtension.fragment_map j h.fragment, ?_, ?_⟩
  · rw [← hzero, ← j.map_kpair, j.mem_iff]
    exact h.sentence
  · obtain ⟨M, hM, ht⟩ := h.model
    refine ⟨j M, (j.structureCode_iff L M).mpr hM, ?_⟩
    simpa only [hzero, j.map_empty] using
      (EndExtension.holds_iff j hAC hω₁ h.fragment M (0 : V) φ ∅).mpr ht

/-- An internally uncountable coded carrier in an externally countable
ambient model distinguishes internal Q from external standard Q, already
on the formula `Q x, True`. -/
theorem internalQ_univ_not_eval_q_verum [Countable V] {M : V} {Λ : Language}
    [Structure Λ (CodedDomain M)] (hD : ¬IsInternallyCountable (structureDomain M)) :
    InternalQ M Set.univ ∧
      ¬Formula.Eval (.q (.fo (.verum : Semisentence Λ 1))) (![] : Fin 0 → CodedDomain M) := by
  constructor
  · apply (internalQ_iff (fun _ h ↦ h) (fun x ↦ ?_)).mpr hD
    exact iff_of_true (Set.mem_univ x) x.property
  · change ¬¬Set.Countable {x : CodedDomain M | True}
    exact not_not.mpr (Set.to_countable _)

end ZFVP.Infinitary.Internal
