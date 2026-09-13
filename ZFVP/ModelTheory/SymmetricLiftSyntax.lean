import ZFVP.ModelTheory.SymmetricLiftAssignments
import ZFVP.Syntax.SequenceSupportSyntax

/-! Fixing the symbols fixes every internally coded term and formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (L : SymmetricLiftData S U W f)

theorem graph_value_codeExpression {n : ℕ} (t : CodeExpression n) (v : Fin n → S.Model)
    (hv : ∀ i, v i ∈ domain L.graph) (hfix : ∀ i, L.graph ‘ (v i) = v i) :
    L.graph ‘ (t.eval v) = t.eval v := by
  induction t with
  | var i => exact hfix i
  | num k => exact L.graph_value_numeral k
  | kpair t u iht ihu =>
    exact (L.graph_value_pair (t.eval_mem v hv) (u.eval_mem v hv)).trans (by rw [iht, ihu]; rfl)
  | doubleton t u iht ihu =>
    exact (L.graph_value_doubleton (t.eval_mem v hv) (u.eval_mem v hv)).trans (by rw [iht, ihu]; rfl)
  | succ t iht =>
    exact (L.graph_value_succ (t.eval_mem v hv)).trans (by rw [iht]; rfl)

theorem graph_value_closedExpression (t : CodeExpression 0) :
    L.graph ‘ (t.eval ![]) = t.eval ![] := L.graph_value_codeExpression t ![] (Fin.elim0 ·) (Fin.elim0 ·)

theorem graph_value_unaryExpression (t : CodeExpression 1) {x : S.Model}
    (hx : x ∈ domain L.graph) (hfix : L.graph ‘ x = x) :
    L.graph ‘ (t.eval ![x]) = t.eval ![x] :=
  L.graph_value_codeExpression t ![x] (by simpa using hx) (by simpa using hfix)

theorem graph_value_binaryExpression (t : CodeExpression 2) {x y : S.Model}
    (hx : x ∈ domain L.graph) (hy : y ∈ domain L.graph)
    (hfix : L.graph ‘ x = x) (hfix' : L.graph ‘ y = y) :
    L.graph ‘ (t.eval ![x, y]) = t.eval ![x, y] :=
  L.graph_value_codeExpression t ![x, y] (by simpa using And.intro hx hy) (by simpa using And.intro hfix hfix')

theorem graph_value_term {language Γ n t : S.Model} (hL : IsLanguageCode language)
    (hF : functionSymbols language ⊆ domain L.graph) (hΓ : Γ ⊆ domain L.graph)
    (hfixF : ∀ g ∈ functionSymbols language, L.graph ‘ g = g)
    (hfixΓ : ∀ x ∈ Γ, L.graph ‘ x = x)
    (hn : n ∈ (ω : S.Model)) (ht : t ∈ termSet language Γ n) : L.graph ‘ t = t := by
  have hsub := termSet_subset_sequenceSupport hL hF hΓ hn
  apply termSet_induction hL hn Γ (fun t ↦ L.graph ‘ t = t) (by definability) ?_ ?_ ?_ t ht
  · intro i hi
    have hiω := IsOrdinal.toIsTransitive.mem_trans hi hn
    exact L.graph_value_unaryExpression (.boundVar (.var 0))
      (IsCodingSupport.natural_mem hiω) (L.graph_value_natural hiω)
  · intro x hx
    exact L.graph_value_unaryExpression (.kpair (.num 1) (.var 0)) (hΓ x hx) (hfixΓ x hx)
  · intro g hg args ha ih
    have : IsFunction args := IsFunction.of_mem ha
    have han := hL.function_arity_natural hg
    have haD := mem_function_of_mem_function_of_subset ha hsub
    have ha_mem := function_mem_sequenceSupport (subset_refl (domain L.graph)) han haD
    have hfixa : L.graph ‘ args = args := L.graph_value_assignment_fixed han haD (by
      intro i hi
      exact ih _ (mem_range_of_kpair_mem (kpair_value_mem
        (by simpa only [domain_eq_of_mem_function ha] using hi))))
    exact L.graph_value_binaryExpression (.atom (.var 0) (.var 1)) (hF g hg) ha_mem (hfixF g hg) hfixa

theorem graph_value_atomicArguments {language Γ n r args : S.Model} (hL : IsLanguageCode language)
    (hF : functionSymbols language ⊆ domain L.graph) (hR : relationSymbols language ⊆ domain L.graph)
    (hΓ : Γ ⊆ domain L.graph)
    (hfixF : ∀ g ∈ functionSymbols language, L.graph ‘ g = g)
    (hfixR : ∀ g ∈ relationSymbols language, L.graph ‘ g = g)
    (hfixΓ : ∀ x ∈ Γ, L.graph ‘ x = x)
    (hn : n ∈ (ω : S.Model)) (ha : IsAtomicArguments language Γ n r args) :
    L.graph ‘ r = r ∧ L.graph ‘ args = args := by
  have hsub := termSet_subset_sequenceSupport hL hF hΓ hn
  have hargs {k : S.Model} (hk : k ∈ (ω : S.Model)) (hargs : args ∈ termSet language Γ n ^ k) :
      L.graph ‘ args = args := by
    apply L.graph_value_assignment_fixed hk (mem_function_of_mem_function_of_subset hargs hsub)
    intro i hi
    exact L.graph_value_term hL hF hΓ hfixF hfixΓ hn (function_value_mem hargs hi)
  rcases ha with ⟨rfl, ha⟩ | ⟨s, hs, rfl, ha⟩
  · exact ⟨L.graph_value_empty, hargs (by simp) ha⟩
  · exact ⟨L.graph_value_unaryExpression (.relation (.var 0)) (hR s hs) (hfixR s hs),
      hargs (hL.relation_arity_natural hs) ha⟩

theorem graph_value_formula {language Γ n φ : S.Model} (hL : IsLanguageCode language)
    (hF : functionSymbols language ⊆ domain L.graph) (hR : relationSymbols language ⊆ domain L.graph)
    (hΓ : Γ ⊆ domain L.graph)
    (hfixF : ∀ g ∈ functionSymbols language, L.graph ‘ g = g)
    (hfixR : ∀ g ∈ relationSymbols language, L.graph ‘ g = g)
    (hfixΓ : ∀ x ∈ Γ, L.graph ‘ x = x)
    (hφ : φ ∈ formulaSet language Γ n) : L.graph ‘ φ = φ := by
  apply formulaSet_induction hL Γ (fun _ φ ↦ L.graph ‘ φ = φ) (by definability) ?_ ?_ ?_ ?_ n φ hφ
  · intro n hn
    exact ⟨L.graph_value_closedExpression .truth, L.graph_value_closedExpression .falsity⟩
  · intro n hn r args ha
    obtain ⟨hr, hargs⟩ := atomicArguments_mem_sequenceSupport hL hF hR hΓ hn ha
    obtain ⟨hfr, hfa⟩ := L.graph_value_atomicArguments hL hF hR hΓ hfixF hfixR hfixΓ hn ha
    exact ⟨L.graph_value_binaryExpression (.atom (.var 0) (.var 1)) hr hargs hfr hfa,
      L.graph_value_binaryExpression (.negAtom (.var 0) (.var 1)) hr hargs hfr hfa⟩
  · intro n hn φ ψ hφ hψ ihφ ihψ
    have hφD := formula_mem_sequenceSupport hL hF hR hΓ hφ
    have hψD := formula_mem_sequenceSupport hL hF hR hΓ hψ
    exact ⟨L.graph_value_binaryExpression (.conj (.var 0) (.var 1)) hφD hψD ihφ ihψ,
      L.graph_value_binaryExpression (.disj (.var 0) (.var 1)) hφD hψD ihφ ihψ⟩
  · intro n hn φ hφ ih
    have hφD := formula_mem_sequenceSupport hL hF hR hΓ hφ
    exact ⟨L.graph_value_unaryExpression (.all (.var 0)) hφD ih,
      L.graph_value_unaryExpression (.exs (.var 0)) hφD ih⟩

end SymmetricLiftData
end ZFVP
