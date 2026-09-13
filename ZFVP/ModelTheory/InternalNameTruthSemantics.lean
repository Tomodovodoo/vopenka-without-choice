import ZFVP.ModelTheory.InternalBinaryQuotientTruth
import ZFVP.ModelTheory.InternalBinaryQuotientSemantics

/-! An actual name truth table evaluates every standard formula in its name
prestructure. No equality laws are assumed in this bridge. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem directNameAtomicHolds_pair_iff {E R n b r i j : V} (hi : i ∈ n) (hj : j ∈ n) :
    DirectNameAtomicHolds E R n b r (boundPairArguments i j) ↔
      (((r = equalityToken ∨ r = relationToken 0) ∧ ⟨b ‘ i, b ‘ j⟩ₖ ∈ E) ∨
        (r = relationToken 1 ∧ ⟨b ‘ i, b ‘ j⟩ₖ ∈ R)) := by
  constructor
  · rintro ⟨k, _, l, _, he, hh⟩
    have ht := standardTuple_injective he
    have hik := (kpair_iff.mp (congrFun ht 0)).2
    have hjl := (kpair_iff.mp (congrFun ht 1)).2
    change i = k at hik
    change j = l at hjl
    subst k
    subst l
    exact hh
  · exact fun hh ↦ ⟨i, hi, j, hj, rfl, hh⟩

private theorem term_index {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) : ∃ i : Fin n, t = .bvar i := by
  cases t with
  | bvar i => exact ⟨i, rfl⟩
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

private theorem termPair_indices {n : ℕ} (ts : Fin 2 → Semiterm ℒₛₑₜ Empty n) :
    ∃ i j : Fin n, ts = ![.bvar i, .bvar j] := by
  obtain ⟨i, hi⟩ := term_index (ts 0)
  obtain ⟨j, hj⟩ := term_index (ts 1)
  refine ⟨i, j, funext fun k ↦ ?_⟩
  exact Fin.cases hi (fun k ↦ Fin.cases hj (fun l ↦ Fin.elim0 l) k) k

theorem IsNameTruthTable.encode_atoms {D E R T : V} (hT : IsNameTruthTable D E R T)
    {n k : ℕ} (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ Empty n)
    (b : Fin n → SetDomain D) :
    (TableHolds T (n : V) (encodeMembershipFormula (.rel r ts)) (standardTuple (fun i ↦ (b i).val)) ↔
      (.rel r ts : SetTheorySemisentence n).Evalb (s := internalNameStructure D E R) b) ∧
    (TableHolds T (n : V) (encodeMembershipFormula (.nrel r ts)) (standardTuple (fun i ↦ (b i).val)) ↔
      (.nrel r ts : SetTheorySemisentence n).Evalb (s := internalNameStructure D E R) b) := by
  have hb := standardTuple_mem_function (fun i ↦ (b i).val) (fun i ↦ (b i).property)
  cases r with
  | eq =>
    obtain ⟨i, j, rfl⟩ := termPair_indices ts
    have hi := natCast_mem_of_lt (V := V) i.isLt
    have hj := natCast_mem_of_lt (V := V) j.isLt
    have ha : IsMembershipAtomicArguments (n : V) (relationToken 0) (boundPairArguments (i.val : V) (j.val : V)) :=
      ⟨Or.inr (Or.inl rfl), i.val, hi, j.val, hj, rfl⟩
    have hh := (hT _ (by simp) _ hb).2.1 _ _ ha
    rw [directNameAtomicHolds_pair_iff hi hj, value_standardTuple, value_standardTuple] at hh
    have hne := (equalityToken_ne_relationToken (V := V) 0).symm
    change (TableHolds T (n : V) (atomCode (relationToken 0) (boundPairArguments (i.val : V) (j.val : V)))
      (standardTuple (fun l ↦ (b l).val)) ↔ ⟨(b i).val, (b j).val⟩ₖ ∈ E) ∧
      (TableHolds T (n : V) (negAtomCode (relationToken 0) (boundPairArguments (i.val : V) (j.val : V)))
        (standardTuple (fun l ↦ (b l).val)) ↔ ¬⟨(b i).val, (b j).val⟩ₖ ∈ E)
    simpa only [hne, relationToken_inj, SetTheory.zero_ne_one, false_or, true_and, false_and, or_false] using hh
  | mem =>
    obtain ⟨i, j, rfl⟩ := termPair_indices ts
    have hi := natCast_mem_of_lt (V := V) i.isLt
    have hj := natCast_mem_of_lt (V := V) j.isLt
    have ha : IsMembershipAtomicArguments (n : V) (relationToken 1) (boundPairArguments (i.val : V) (j.val : V)) :=
      ⟨Or.inr (Or.inr rfl), i.val, hi, j.val, hj, rfl⟩
    have hh := (hT _ (by simp) _ hb).2.1 _ _ ha
    rw [directNameAtomicHolds_pair_iff hi hj, value_standardTuple, value_standardTuple] at hh
    have hne := (equalityToken_ne_relationToken (V := V) 1).symm
    change (TableHolds T (n : V) (atomCode (relationToken 1) (boundPairArguments (i.val : V) (j.val : V)))
      (standardTuple (fun l ↦ (b l).val)) ↔ ⟨(b i).val, (b j).val⟩ₖ ∈ R) ∧
      (TableHolds T (n : V) (negAtomCode (relationToken 1) (boundPairArguments (i.val : V) (j.val : V)))
        (standardTuple (fun l ↦ (b l).val)) ↔ ¬⟨(b i).val, (b j).val⟩ₖ ∈ R)
    simpa only [hne, relationToken_inj, SetTheory.one_ne_zero, false_or, true_and, false_and, or_false] using hh

theorem IsNameTruthTable.encode_iff {D E R T : V} (hT : IsNameTruthTable D E R T)
    {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → SetDomain D) :
    TableHolds T (n : V) (encodeMembershipFormula φ) (standardTuple (fun i ↦ (b i).val)) ↔
      φ.Evalb (s := internalNameStructure D E R) b := by
  let : Structure ℒₛₑₜ (SetDomain D) := internalNameStructure D E R
  have hv {n : ℕ} (ψ : SetTheorySemisentence n) : IsMembershipFormulaCode (n : V) (encodeMembershipFormula ψ) :=
    (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem ψ)
  induction φ with
  | verum => exact iff_of_true (hT _ (by simp) _ (standardTuple_mem_function _ (fun i ↦ (b i).property))).1.1 trivial
  | falsum => exact iff_of_false (hT _ (by simp) _ (standardTuple_mem_function _ (fun i ↦ (b i).property))).1.2 id
  | rel r ts => exact (hT.encode_atoms r ts b).1
  | nrel r ts => exact (hT.encode_atoms r ts b).2
  | and φ ψ ihφ ihψ =>
    exact ((hT _ (by simp) _ (standardTuple_mem_function _ (fun i ↦ (b i).property))).2.2.1 _ _ (hv φ) (hv ψ)).1.trans
      (and_congr (ihφ b) (ihψ b))
  | or φ ψ ihφ ihψ =>
    exact ((hT _ (by simp) _ (standardTuple_mem_function _ (fun i ↦ (b i).property))).2.2.1 _ _ (hv φ) (hv ψ)).2.trans
      (or_congr (ihφ b) (ihψ b))
  | @all n φ ih =>
    have hφ : IsMembershipFormulaCode (succ (n : V)) (encodeMembershipFormula φ) := by
      simpa only [num_succ_def] using hv φ
    change TableHolds T (n : V) (allCode (encodeMembershipFormula φ)) (standardTuple (fun i ↦ (b i).val)) ↔ _
    rw [((hT _ (by simp) _ (standardTuple_mem_function _ (fun i ↦ (b i).property))).2.2.2 _ hφ).1]
    change (∀ x ∈ D, _) ↔ ∀ x : SetDomain D, φ.Evalb _
    constructor
    · intro hh x
      apply (ih (x :> b)).mp
      simpa [standardTuple, num_succ_def] using hh x.val x.property
    · intro hh x hx
      let x' : SetDomain D := ⟨x, hx⟩
      have hh' := (ih (x' :> b)).mpr (hh x')
      change TableHolds T (succ (n : V)) (encodeMembershipFormula φ)
        (assignmentPrepend (n : V) (standardTuple (fun i ↦ (b i).val)) x'.val)
      simpa [standardTuple, num_succ_def] using hh'
  | @exs n φ ih =>
    have hφ : IsMembershipFormulaCode (succ (n : V)) (encodeMembershipFormula φ) := by
      simpa only [num_succ_def] using hv φ
    change TableHolds T (n : V) (existsCode (encodeMembershipFormula φ)) (standardTuple (fun i ↦ (b i).val)) ↔ _
    rw [((hT _ (by simp) _ (standardTuple_mem_function _ (fun i ↦ (b i).property))).2.2.2 _ hφ).2]
    change (∃ x ∈ D, _) ↔ ∃ x : SetDomain D, φ.Evalb _
    constructor
    · rintro ⟨x, hx, hh⟩
      let x' : SetDomain D := ⟨x, hx⟩
      refine ⟨x', (ih (x' :> b)).mp ?_⟩
      change TableHolds T (succ (n : V)) (encodeMembershipFormula φ)
        (assignmentPrepend (n : V) (standardTuple (fun i ↦ (b i).val)) x'.val) at hh
      simpa [standardTuple, num_succ_def] using hh
    · rintro ⟨x, hh⟩
      refine ⟨x.val, x.property, ?_⟩
      have hh' := (ih (x :> b)).mpr hh
      simpa [standardTuple, num_succ_def] using hh'

end ZFVP
