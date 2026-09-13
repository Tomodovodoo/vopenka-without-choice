import ZFVP.Syntax.MembershipAtomicSyntax

/-! Closed membership formulas have the same meaning in every free-variable domain. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem boundPairArguments_valid_free (Γ : V) {n i j : V}
    (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n) :
    boundPairArguments i j ∈ termSet membershipLanguageCode Γ n ^ (2 : V) := by
  apply standardTuple_mem_function
  intro a
  have hc := (termSet_closed (membershipLanguageCode_valid (V := V)) hn Γ).1
  refine Fin.cases ?_ (fun a ↦ Fin.cases ?_ (fun b ↦ Fin.elim0 b) a) a
  · exact hc i hi
  · exact hc j hj

theorem closedAtomicArguments_free (Γ : V) {n r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) :
    IsAtomicArguments membershipLanguageCode Γ n r args := by
  obtain ⟨_, i, hi, j, hj, rfl⟩ := (membershipAtomicArguments_iff hn).mp ha
  have hargs := boundPairArguments_valid_free Γ hn hi hj
  rcases ha with ⟨hr, _⟩ | ⟨s, hs, hr, ha⟩
  · exact Or.inl ⟨hr, hargs⟩
  · have har : (relationArities (membershipLanguageCode : V)) ‘ s = (2 : V) := by
      simp only [membershipLanguageCode, relationArities_code]
      exact value_constantGraph _ _ (by simpa [membershipLanguageCode] using hs)
    exact Or.inr ⟨s, hs, hr, by rw [har]; exact hargs⟩

theorem evaluated_boundPairArguments (Γ M e b : V) {n i j : V}
    (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n) :
    evaluatedArguments membershipLanguageCode Γ M e n b (boundPairArguments i j) =
      standardTuple ![b ‘ i, b ‘ j] := by
  unfold evaluatedArguments evaluateWithFreeAssignment boundPairArguments
  rw [compose_standardTuple]
  · congr 1
    funext a
    refine Fin.cases ?_ (fun a ↦ Fin.cases ?_ (fun z ↦ Fin.elim0 z) a) a
    · exact termEvaluation_boundVar membershipLanguageCode_valid hn Γ M b e hi
    · exact termEvaluation_boundVar membershipLanguageCode_valid hn Γ M b e hj
  · intro a
    simp only [domain_termEvaluation]
    have hc := (termSet_closed (membershipLanguageCode_valid (V := V)) hn Γ).1
    refine Fin.cases ?_ (fun a ↦ Fin.cases ?_ (fun z ↦ Fin.elim0 z) a) a
    · exact hc i hi
    · exact hc j hj

theorem closedAtomicHolds_free (Γ M e f b : V) {n r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) :
    AtomicHolds membershipLanguageCode Γ M e n b r args ↔
      AtomicHolds membershipLanguageCode ∅ M f n b r args := by
  obtain ⟨_, i, hi, j, hj, rfl⟩ := (membershipAtomicArguments_iff hn).mp ha
  unfold AtomicHolds
  rw [evaluated_boundPairArguments Γ M e b hn hi hj,
    evaluated_boundPairArguments ∅ M f b hn hi hj]

theorem closedFormula_free (Γ M e f : V) {n φ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    φ ∈ formulaSet membershipLanguageCode Γ n ∧
      ∀ b ∈ structureDomain M ^ n,
        Satisfies membershipLanguageCode Γ M e n φ b ↔
          Satisfies membershipLanguageCode ∅ M f n φ b := by
  apply formulaSet_induction membershipLanguageCode_valid ∅ (fun n φ ↦
    φ ∈ formulaSet membershipLanguageCode Γ n ∧ ∀ b ∈ structureDomain M ^ n,
      Satisfies membershipLanguageCode Γ M e n φ b ↔
        Satisfies membershipLanguageCode ∅ M f n φ b) (by unfold Satisfies; definability) ?_ ?_ ?_ ?_ n φ hφ
  · intro n hn
    exact ⟨⟨(formulaSet_constants membershipLanguageCode_valid hn Γ).1,
      fun b _ ↦ (satisfies_truth membershipLanguageCode_valid hn).trans
        (satisfies_truth membershipLanguageCode_valid hn).symm⟩,
      ⟨(formulaSet_constants membershipLanguageCode_valid hn Γ).2,
      fun b _ ↦ iff_of_false (not_satisfies_falsity membershipLanguageCode_valid hn)
        (not_satisfies_falsity membershipLanguageCode_valid hn)⟩⟩
  · intro n hn r args ha
    have hΓ := closedAtomicArguments_free Γ hn ha
    constructor
    · refine ⟨(formulaSet_atoms membershipLanguageCode_valid hn hΓ).1, ?_⟩
      intro b hb
      rw [satisfies_atom membershipLanguageCode_valid hn hΓ hb,
        satisfies_atom membershipLanguageCode_valid hn ha hb]
      exact closedAtomicHolds_free Γ M e f b hn ha
    · refine ⟨(formulaSet_atoms membershipLanguageCode_valid hn hΓ).2, ?_⟩
      intro b hb
      rw [satisfies_negAtom membershipLanguageCode_valid hn hΓ hb,
        satisfies_negAtom membershipLanguageCode_valid hn ha hb,
        closedAtomicHolds_free Γ M e f b hn ha]
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · refine ⟨(formulaSet_binary membershipLanguageCode_valid hn ihφ.1 ihψ.1).1, ?_⟩
      intro b hb
      rw [satisfies_and membershipLanguageCode_valid hn ihφ.1 ihψ.1 hb,
        satisfies_and membershipLanguageCode_valid hn hφ hψ hb, ihφ.2 b hb, ihψ.2 b hb]
    · refine ⟨(formulaSet_binary membershipLanguageCode_valid hn ihφ.1 ihψ.1).2, ?_⟩
      intro b hb
      rw [satisfies_or membershipLanguageCode_valid hn ihφ.1 ihψ.1 hb,
        satisfies_or membershipLanguageCode_valid hn hφ hψ hb, ihφ.2 b hb, ihψ.2 b hb]
  · intro n hn φ hφ ih
    constructor
    · refine ⟨(formulaSet_quantifiers membershipLanguageCode_valid hn ih.1).1, ?_⟩
      intro b hb
      rw [satisfies_all membershipLanguageCode_valid hn ih.1 hb,
        satisfies_all membershipLanguageCode_valid hn hφ hb]
      exact forall_congr' (fun x ↦ forall_congr' (fun hx ↦ ih.2 _ (assignmentPrepend_mem_function hn hb hx)))
    · refine ⟨(formulaSet_quantifiers membershipLanguageCode_valid hn ih.1).2, ?_⟩
      intro b hb
      rw [satisfies_exists membershipLanguageCode_valid hn ih.1 hb,
        satisfies_exists membershipLanguageCode_valid hn hφ hb]
      exact exists_congr (fun x ↦ and_congr_right (fun hx ↦ ih.2 _ (assignmentPrepend_mem_function hn hb hx)))

end ZFVP
