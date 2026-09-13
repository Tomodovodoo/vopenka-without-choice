import ZFVP.ModelTheory.SchmerlInternalQuantifierAxioms
import ZFVP.Syntax.EndExtensionMembershipSyntax

/-! The internal Q two-points axiom uses logical equality tokens, rather
than a language's distinguished relation. Indices range over internal
finite arities. Soundness needs neither internal Choice nor standard omega. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def equalityCode (i j : V) : V := foCode (atomCode equalityToken (boundPairArguments i j))

instance equalityCode_definable : ℒₛₑₜ-function₂[V] equalityCode := by
  unfold equalityCode equalityToken
  definability

theorem holds_equalityCode {L F M n i j b : V} (hF : IsFragment L F)
    (ht : ⟨n, equalityCode i j⟩ₖ ∈ F) (hi : i ∈ n) (hj : j ∈ n)
    (hb : b ∈ structureDomain M ^ n) : Holds L F M n (equalityCode i j) b ↔ b ‘ i = b ‘ j := by
  have hn := (hF.node ht).1
  have ha : IsAtomicArguments L ∅ n equalityToken (boundPairArguments i j) := by
    refine Or.inl ⟨rfl, ?_⟩
    apply standardTuple_mem_function
    intro a
    have hc := (termSet_closed hF.1 hn ∅).1
    exact Fin.cases (hc i hi) (fun k ↦ Fin.cases (hc j hj) (fun l ↦ Fin.elim0 l) k) a
  have he : evaluatedArguments L ∅ M ∅ n b (boundPairArguments i j) = standardTuple ![b ‘ i, b ‘ j] := by
    unfold evaluatedArguments evaluateWithFreeAssignment boundPairArguments
    rw [compose_standardTuple]
    · congr 1
      funext k
      exact Fin.cases (termEvaluation_boundVar hF.1 hn ∅ M b ∅ hi)
        (fun a ↦ Fin.cases (termEvaluation_boundVar hF.1 hn ∅ M b ∅ hj) (fun l ↦ Fin.elim0 l) a) k
    · intro k
      simp only [domain_termEvaluation]
      have hc := (termSet_closed hF.1 hn ∅).1
      exact Fin.cases (hc i hi) (fun a ↦ Fin.cases (hc j hj) (fun l ↦ Fin.elim0 l) a) k
  rw [equalityCode, holds_fo hF ht, satisfies_atom hF.1 hn ha hb, atomicHolds_equality, he]
  change (standardTuple ![b ‘ i, b ‘ j]) ‘ (((0 : Fin 2).val : ℕ) : V) =
    (standardTuple ![b ‘ i, b ‘ j]) ‘ (((1 : Fin 2).val : ℕ) : V) ↔ _
  simp only [value_standardTuple]
  rfl

noncomputable def twoPointsBody (i j : V) : V :=
  negCode (andCode (negCode (equalityCode 0 (succ i))) (negCode (equalityCode 0 (succ j))))

noncomputable def qTwoPointsCode (i j : V) : V := negCode (qCode (twoPointsBody i j))

instance twoPointsBody_definable : ℒₛₑₜ-function₂[V] twoPointsBody := by unfold twoPointsBody; definability
instance qTwoPointsCode_definable : ℒₛₑₜ-function₂[V] qTwoPointsCode := by unfold qTwoPointsCode; definability

theorem holds_twoPointsBody {L F M n i j b x : V} (hF : IsFragment L F)
    (ht : ⟨succ n, twoPointsBody i j⟩ₖ ∈ F) (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n)
    (hb : b ∈ structureDomain M ^ n) (hx : x ∈ structureDomain M) :
    Holds L F M (succ n) (twoPointsBody i j) (assignmentPrepend n b x) ↔ x = b ‘ i ∨ x = b ‘ j := by
  have hb' := assignmentPrepend_mem_function hn hb hx
  have hand := hF.neg_mem ht
  have hl := hF.and_left_mem hand
  have hr := hF.and_right_mem hand
  rw [twoPointsBody, holds_neg hF ht hb', holds_and hF hand hb',
    holds_neg hF hl hb', holds_neg hF hr hb',
    holds_equalityCode hF (hF.neg_mem hl) (zero_mem_succ_natural hn) (succ_mem_succ_of_natural_mem hn hi) hb',
    holds_equalityCode hF (hF.neg_mem hr) (zero_mem_succ_natural hn) (succ_mem_succ_of_natural_mem hn hj) hb',
    assignmentPrepend_zero hn, assignmentPrepend_succ hn hi, assignmentPrepend_succ hn hj]
  tauto

def IsQTwoPointsAxiom (n χ : V) : Prop := ∃ i ∈ n, ∃ j ∈ n, χ = qTwoPointsCode i j

instance isQTwoPointsAxiom_definable : ℒₛₑₜ-relation[V] IsQTwoPointsAxiom := by
  unfold IsQTwoPointsAxiom
  definability

theorem IsQTwoPointsAxiom.sound {L F M n χ b : V} (hχ : IsQTwoPointsAxiom n χ)
    (hF : IsFragment L F) (ht : ⟨n, χ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n χ b := by
  obtain ⟨i, hi, j, hj, rfl⟩ := hχ
  have hn := (hF.node ht).1
  have hq := hF.neg_mem ht
  have hbody := hF.q_mem hq
  rw [qTwoPointsCode, holds_neg hF ht hb, holds_q hF hq hb]
  apply not_not.mpr
  apply internallyCountable_subset (internal_twoPoints_countable (b ‘ i) (b ‘ j))
  intro x hx
  obtain ⟨hx, hbodyx⟩ := mem_sep_iff.mp hx
  have he := (holds_twoPointsBody hF hbody hn hi hj hb hx).mp hbodyx
  simpa using he

namespace EndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem map_equalityCode (i k : V) : j (equalityCode i k) = equalityCode (j i) (j k) := by
  simp only [equalityCode, map_foCode, j.map_atomCode, j.map_boundPairArguments, equalityToken, j.map_empty]

theorem map_qTwoPointsCode (i k : V) : j (qTwoPointsCode i k) = qTwoPointsCode (j i) (j k) := by
  simp only [qTwoPointsCode, twoPointsBody, map_negCode, map_qCode, map_andCode, map_equalityCode,
    j.map_succ, (show j (0 : V) = (0 : W) from j.map_numeral 0)]

theorem qTwoPointsAxiom_map {n χ : V} (h : IsQTwoPointsAxiom n χ) : IsQTwoPointsAxiom (j n) (j χ) := by
  obtain ⟨i, hi, k, hk, rfl⟩ := h
  exact ⟨j i, (j.mem_iff i n).mpr hi, j k, (j.mem_iff k n).mpr hk, map_qTwoPointsCode j i k⟩

end EndExtension
end ZFVP.Infinitary.Internal
