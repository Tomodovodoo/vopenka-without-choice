import ZFVP.ModelTheory.InternalNamedSupport

/-! Explicit source parameters and distinguished names in raw unary and binary
formula instances. Source names are fixed during finite realizations. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem SourceNaming.compose_source {M j f n b : V} (hf : SourceNaming M j f)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hb : b ∈ structureDomain M ^ n) :
    compose (compose b j) f = b := by
  apply function_eq_of_values (compose_function (compose_function hb hj) hf.1) hb
  intro i hi
  rw [value_compose_of_mem_function (compose_function hb hj) hf.1 hi,
    value_compose_of_mem_function hb hj hi]
  exact hf.2 _ (function_value_mem hb hi)

noncomputable def namedUnaryInstance (j n φ b a : V) : V :=
  ⟨⟨succ n, φ⟩ₖ, assignmentPrepend n (compose b j) a⟩ₖ

noncomputable def namedBinaryInstance (j n φ b a c : V) : V :=
  ⟨⟨succ (succ n), φ⟩ₖ, assignmentPrepend (succ n) (assignmentPrepend n (compose b j) c) a⟩ₖ

instance namedUnaryInstance_definable : Language.DefinableFunction₅ ℒₛₑₜ (namedUnaryInstance (V := V)) := by
  unfold namedUnaryInstance
  definability

instance namedBinaryInstance_definable (j : V) : Language.DefinableFunction₅ ℒₛₑₜ (namedBinaryInstance j) := by
  unfold namedBinaryInstance
  definability

theorem namedUnaryInstance_valid {L M j n φ b a : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L ∅ (succ n))
    (hj : j ∈ (ω : V) ^ structureDomain M) (hb : b ∈ structureDomain M ^ n) (ha : a ∈ (ω : V)) :
    namedUnaryInstance j n φ b a ∈ namedFormulaSet L (ω : V) :=
  (pair_mem_namedFormulaSet_iff hL).mpr ⟨hφ, assignmentPrepend_mem_function hn (compose_function hb hj) ha⟩

theorem namedBinaryInstance_valid {L M j n φ b a c : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L ∅ (succ (succ n)))
    (hj : j ∈ (ω : V) ^ structureDomain M) (hb : b ∈ structureDomain M ^ n)
    (ha : a ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    namedBinaryInstance j n φ b a c ∈ namedFormulaSet L (ω : V) :=
  (pair_mem_namedFormulaSet_iff hL).mpr ⟨hφ, assignmentPrepend_mem_function (ω_succ_closed hn)
    (assignmentPrepend_mem_function hn (compose_function hb hj) hc) ha⟩

theorem SourceNaming.unary_iff {L M j f n φ b a : V} (hf : SourceNaming M j f)
    (hn : n ∈ (ω : V)) (hj : j ∈ (ω : V) ^ structureDomain M)
    (hb : b ∈ structureDomain M ^ n) (ha : a ∈ (ω : V)) :
    NamedHolds L M f (namedUnaryInstance j n φ b a) ↔
      Satisfies L ∅ M ∅ (succ n) φ (assignmentPrepend n b (f ‘ a)) := by
  rw [namedUnaryInstance, namedHolds_pair,
    compose_assignmentPrepend hn (compose_function hb hj) hf.1 ha, hf.compose_source hj hb]

theorem SourceNaming.binary_iff {L M j f n φ b a c : V} (hf : SourceNaming M j f)
    (hn : n ∈ (ω : V)) (hj : j ∈ (ω : V) ^ structureDomain M)
    (hb : b ∈ structureDomain M ^ n) (ha : a ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    NamedHolds L M f (namedBinaryInstance j n φ b a c) ↔
      Satisfies L ∅ M ∅ (succ (succ n)) φ
        (assignmentPrepend (succ n) (assignmentPrepend n b (f ‘ c)) (f ‘ a)) := by
  rw [namedBinaryInstance, namedHolds_pair,
    compose_assignmentPrepend (ω_succ_closed hn)
      (assignmentPrepend_mem_function hn (compose_function hb hj) hc) hf.1 ha,
    compose_assignmentPrepend hn (compose_function hb hj) hf.1 hc, hf.compose_source hj hb]

theorem SourceNaming.diagram {L M j f : V} (hf : SourceNaming M j f)
    (hL : IsLanguageCode L) (hj : j ∈ (ω : V) ^ structureDomain M) :
    ∀ p ∈ namedElementaryDiagram L M j, NamedHolds L M f p := by
  intro p hp
  obtain ⟨n, _, φ, _, b, hb, rfl, hs⟩ := namedElementaryDiagram_cases hL hp
  rw [namedHolds_pair, hf.compose_source hj hb]
  exact hs

end ZFVP
