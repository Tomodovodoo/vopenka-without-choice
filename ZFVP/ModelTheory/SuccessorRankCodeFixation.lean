import ZFVP.ModelTheory.SuccessorRankInternalForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ ε f : V} (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (he : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f)

include hδ hε he in
private theorem value_natural {n : V} (hn : n ∈ (ω : V)) : f ‘ n = n := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hierarchy_transitive (succ δ)
  let := hierarchy_transitive (succ ε)
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  have hU : hierarchy δ ∈ hierarchy (succ δ) := by rw [hierarchy_succ, mem_power_iff]
  have hlow : hierarchy δ ⊆ hierarchy (succ δ) := (hierarchy_transitive (succ δ)).transitive _ hU
  apply naturalNumber_induction (fun n ↦ f ‘ n = n) (by definability)
    (he.value_empty (hlow _ IsCodingSupport.empty_mem)) ?_ n hn
  intro i hi ih
  rw [he.value_succ (hlow _ (IsCodingSupport.natural_mem hi))
    (hlow _ (IsCodingSupport.natural_mem (ω_succ_closed hi))), ih]

include hδ hε he in
private theorem value_expression {n : ℕ} (t : CodeExpression n) (v : Fin n → V)
    (hv : ∀ i, v i ∈ hierarchy δ) (hfix : ∀ i, f ‘ (v i) = v i) : f ‘ (t.eval v) = t.eval v := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hierarchy_transitive (succ δ)
  let := hierarchy_transitive (succ ε)
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  have hU : hierarchy δ ∈ hierarchy (succ δ) := by rw [hierarchy_succ, mem_power_iff]
  have hlow : hierarchy δ ⊆ hierarchy (succ δ) := (hierarchy_transitive (succ δ)).transitive _ hU
  induction t with
  | var i => exact hfix i
  | num k => exact value_natural hδ hε he (n := (k : V)) (by simp)
  | kpair t u iht ihu =>
    have ht := t.eval_mem v hv
    have hu := u.eval_mem v hv
    exact (he.value_pair (hlow _ ht) (hlow _ hu) (hlow _ (IsCodingSupport.kpair_closed _ ht _ hu))).trans
      (by rw [iht, ihu]; rfl)
  | doubleton t u iht ihu =>
    have ht := t.eval_mem v hv
    have hu := u.eval_mem v hv
    exact (he.value_doubleton (hlow _ ht) (hlow _ hu) (hlow _ (IsCodingSupport.doubleton_closed _ ht _ hu))).trans
      (by rw [iht, ihu]; rfl)
  | succ t iht =>
    have ht := t.eval_mem v hv
    exact (he.value_succ (hlow _ ht) (hlow _ (IsCodingSupport.succ_closed _ ht))).trans (by rw [iht]; rfl)

include hδ hε he in
private theorem value_closed (t : CodeExpression 0) : f ‘ (t.eval ![]) = t.eval ![] :=
  value_expression hδ hε he t ![] (Fin.elim0 ·) (Fin.elim0 ·)

include hδ hε he in
private theorem value_unary (t : CodeExpression 1) {x : V}
    (hx : x ∈ hierarchy δ) (hfix : f ‘ x = x) : f ‘ (t.eval ![x]) = t.eval ![x] :=
  value_expression hδ hε he t ![x] (by simpa using hx) (by simpa using hfix)

include hδ hε he in
private theorem value_binary (t : CodeExpression 2) {x y : V}
    (hx : x ∈ hierarchy δ) (hy : y ∈ hierarchy δ) (hfix : f ‘ x = x) (hfix' : f ‘ y = y) :
    f ‘ (t.eval ![x, y]) = t.eval ![x, y] :=
  value_expression hδ hε he t ![x, y] (by simpa using And.intro hx hy) (by simpa using And.intro hfix hfix')

include hδ hε he in
private theorem value_atomicArguments {n r args : V}
    (hn : n ∈ (ω : V)) (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) :
    f ‘ r = r ∧ f ‘ args = args := by
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  obtain ⟨hr, i, hi, j, hj, rfl⟩ := (membershipAtomicArguments_iff hn).mp ha
  constructor
  · rcases hr with rfl | rfl | rfl
    · exact value_closed hδ hε he (.num 0)
    · exact value_closed hδ hε he (.relation (.num 0))
    · exact value_closed hδ hε he (.relation (.num 1))
  · have hiω := IsOrdinal.toIsTransitive.mem_trans hi hn
    have hjω := IsOrdinal.toIsTransitive.mem_trans hj hn
    simpa [CodeExpression.eval] using value_binary hδ hε he (.boundArgs (.var 0) (.var 1))
      (IsCodingSupport.natural_mem hiω) (IsCodingSupport.natural_mem hjω)
      (value_natural hδ hε he hiω) (value_natural hδ hε he hjω)

include hδ hε he in
theorem successorRankEmbedding_value_formulaCode {n φ : V} (hφ : IsMembershipFormulaCode n φ) :
    f ‘ φ = φ := by
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  apply formulaSet_induction membershipLanguageCode_valid ∅ (fun _ φ ↦ f ‘ φ = φ)
    (by definability) ?_ ?_ ?_ ?_ n φ hφ.valid
  · intro n hn
    exact ⟨value_closed hδ hε he .truth, value_closed hδ hε he .falsity⟩
  · intro n hn r args ha
    obtain ⟨hr, hargs⟩ := membershipAtomicArguments_mem_support (U := hierarchy δ) hn ha
    obtain ⟨hfr, hfa⟩ := value_atomicArguments hδ hε he hn ha
    exact ⟨value_binary hδ hε he (.atom (.var 0) (.var 1)) hr hargs hfr hfa,
      value_binary hδ hε he (.negAtom (.var 0) (.var 1)) hr hargs hfr hfa⟩
  · intro n hn φ ψ hφ hψ ihφ ihψ
    have hφU := membershipFormulaCode_formula_mem_support (U := hierarchy δ) ((mem_formulaSet_iff _ _ _ _).mp hφ)
    have hψU := membershipFormulaCode_formula_mem_support (U := hierarchy δ) ((mem_formulaSet_iff _ _ _ _).mp hψ)
    exact ⟨value_binary hδ hε he (.conj (.var 0) (.var 1)) hφU hψU ihφ ihψ,
      value_binary hδ hε he (.disj (.var 0) (.var 1)) hφU hψU ihφ ihψ⟩
  · intro n hn φ hφ ih
    have hφU := membershipFormulaCode_formula_mem_support (U := hierarchy δ) ((mem_formulaSet_iff _ _ _ _).mp hφ)
    exact ⟨value_unary hδ hε he (.all (.var 0)) hφU ih, value_unary hδ hε he (.exs (.var 0)) hφU ih⟩

include hδ hε he in
theorem successorRankEmbedding_lowInternalForces_sameCode {P R n φ b p : V}
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ)
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ lowRankNameSet P δ ^ n) (hp : p ∈ P) :
    InternalForces P R (lowRankNameSet P δ) n φ b p ↔
      InternalForces (f ‘ P) (f ‘ R) (lowRankNameSet (f ‘ P) ε) n φ (f ‘ b) (f ‘ p) := by
  simpa only [value_natural hδ hε he hφ.context, successorRankEmbedding_value_formulaCode hδ hε he hφ] using
    successorRankEmbedding_lowInternalForces_iff hδ hε he hP hR hφ hb hp

end ZFVP
