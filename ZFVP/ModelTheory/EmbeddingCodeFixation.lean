import ZFVP.ModelTheory.EmbeddingNaturalFixation
import ZFVP.Syntax.MembershipTruthTableDefinition

/-! Every pure membership formula code is fixed by a coded elementary graph on a coding support. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding

variable {A B f : V} [hA : IsCodingSupport A] [IsTransitive B]

theorem value_codeExpression (h : IsCodedMembershipEmbedding A B f) {n : ℕ}
    (t : CodeExpression n) (v : Fin n → V) (hv : ∀ i, v i ∈ A) (hfix : ∀ i, f ‘ (v i) = v i) :
    f ‘ (t.eval v) = t.eval v := by
  induction t with
  | var i => exact hfix i
  | num k => exact h.value_numeral k
  | kpair t u iht ihu =>
    have ht := t.eval_mem v hv
    have hu := u.eval_mem v hv
    exact (h.value_pair ht hu (hA.kpair_closed _ ht _ hu)).trans (by rw [iht, ihu]; rfl)
  | doubleton t u iht ihu =>
    have ht := t.eval_mem v hv
    have hu := u.eval_mem v hv
    exact (h.value_doubleton ht hu (hA.doubleton_closed _ ht _ hu)).trans (by rw [iht, ihu]; rfl)
  | succ t iht =>
    have ht := t.eval_mem v hv
    exact (h.value_succ ht (hA.succ_closed _ ht)).trans (by rw [iht]; rfl)

theorem value_closedExpression (h : IsCodedMembershipEmbedding A B f) (t : CodeExpression 0) :
    f ‘ (t.eval ![]) = t.eval ![] := h.value_codeExpression t ![] (Fin.elim0 ·) (Fin.elim0 ·)

theorem value_unaryExpression (h : IsCodedMembershipEmbedding A B f) (t : CodeExpression 1)
    {x : V} (hx : x ∈ A) (hfix : f ‘ x = x) : f ‘ (t.eval ![x]) = t.eval ![x] :=
  h.value_codeExpression t ![x] (by simpa using hx) (by simpa using hfix)

theorem value_binaryExpression (h : IsCodedMembershipEmbedding A B f) (t : CodeExpression 2)
    {x y : V} (hx : x ∈ A) (hy : y ∈ A) (hfix : f ‘ x = x) (hfix' : f ‘ y = y) :
    f ‘ (t.eval ![x, y]) = t.eval ![x, y] :=
  h.value_codeExpression t ![x, y] (by simpa using And.intro hx hy) (by simpa using And.intro hfix hfix')

theorem value_atomicArguments (h : IsCodedMembershipEmbedding A B f) {n r args : V}
    (hn : n ∈ (ω : V)) (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) :
    f ‘ r = r ∧ f ‘ args = args := by
  obtain ⟨hr, i, hi, j, hj, rfl⟩ := (membershipAtomicArguments_iff hn).mp ha
  constructor
  · rcases hr with rfl | rfl | rfl
    · exact h.value_empty IsCodingSupport.empty_mem
    · exact h.value_closedExpression (.relation (.num 0))
    · exact h.value_closedExpression (.relation (.num 1))
  · have hiω := IsOrdinal.toIsTransitive.mem_trans hi hn
    have hjω := IsOrdinal.toIsTransitive.mem_trans hj hn
    simpa [CodeExpression.eval] using h.value_binaryExpression (.boundArgs (.var 0) (.var 1))
      (IsCodingSupport.natural_mem hiω) (IsCodingSupport.natural_mem hjω)
      (h.value_natural hiω) (h.value_natural hjω)

theorem value_formulaCode (h : IsCodedMembershipEmbedding A B f) {n φ : V}
    (hφ : IsMembershipFormulaCode n φ) : f ‘ φ = φ := by
  apply formulaSet_induction membershipLanguageCode_valid ∅ (fun _ φ ↦ f ‘ φ = φ)
    (by definability) ?_ ?_ ?_ ?_ n φ hφ.valid
  · intro n hn
    exact ⟨h.value_closedExpression .truth, h.value_closedExpression .falsity⟩
  · intro n hn r args ha
    obtain ⟨hr, hargs⟩ := membershipAtomicArguments_mem_support (U := A) hn ha
    obtain ⟨hfr, hfa⟩ := h.value_atomicArguments hn ha
    exact ⟨h.value_binaryExpression (.atom (.var 0) (.var 1)) hr hargs hfr hfa,
      h.value_binaryExpression (.negAtom (.var 0) (.var 1)) hr hargs hfr hfa⟩
  · intro n hn φ ψ hφ hψ ihφ ihψ
    have hφA := membershipFormulaCode_formula_mem_support (U := A) ((mem_formulaSet_iff _ _ _ _).mp hφ)
    have hψA := membershipFormulaCode_formula_mem_support (U := A) ((mem_formulaSet_iff _ _ _ _).mp hψ)
    exact ⟨h.value_binaryExpression (.conj (.var 0) (.var 1)) hφA hψA ihφ ihψ,
      h.value_binaryExpression (.disj (.var 0) (.var 1)) hφA hψA ihφ ihψ⟩
  · intro n hn φ hφ ih
    have hφA := membershipFormulaCode_formula_mem_support (U := A) ((mem_formulaSet_iff _ _ _ _).mp hφ)
    exact ⟨h.value_unaryExpression (.all (.var 0)) hφA ih,
      h.value_unaryExpression (.exs (.var 0)) hφA ih⟩

end IsCodedMembershipEmbedding

end ZFVP
