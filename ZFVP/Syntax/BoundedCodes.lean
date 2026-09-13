import ZFVP.Syntax.MembershipSatisfaction
import ZFVP.Syntax.FormulaInduction

/-! Bounded set-theory formulas as an internal least closed family.
The bound variable is an internal index, and all arities range over internal omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def boundedGuardArguments (i : V) : V :=
  standardTuple ![boundVarCode (0 : V), boundVarCode (succ i)]

instance boundedGuardArguments_definable : ℒₛₑₜ-function₁[V] boundedGuardArguments := by
  unfold boundedGuardArguments standardTuple
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  definability

noncomputable def boundedAllCode (i φ : V) : V :=
  allCode (orCode (negAtomCode (relationToken (1 : V)) (boundedGuardArguments i)) φ)

noncomputable def boundedExistsCode (i φ : V) : V :=
  existsCode (andCode (atomCode (relationToken (1 : V)) (boundedGuardArguments i)) φ)

instance boundedAllCode_definable : ℒₛₑₜ-function₂[V] boundedAllCode := by
  unfold boundedAllCode
  definability

instance boundedExistsCode_definable : ℒₛₑₜ-function₂[V] boundedExistsCode := by
  unfold boundedExistsCode
  definability

theorem boundedGuardArguments_valid {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) :
    IsAtomicArguments membershipLanguageCode ∅ (succ n) (relationToken (1 : V)) (boundedGuardArguments i) := by
  have hr := membershipSymbol_valid (V := V) Language.Set.Rel.mem
  change (1 : V) ∈ relationSymbols membershipLanguageCode ∧
    (relationArities (membershipLanguageCode : V)) ‘ (1 : V) = (2 : V) at hr
  refine Or.inr ⟨1, hr.1, rfl, ?_⟩
  rw [hr.2]
  have hc := (termSet_closed (membershipLanguageCode_valid (V := V)) (ω_succ_closed hn) ∅).1
  apply standardTuple_mem_function
  intro j
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) j
  · exact hc 0 (zero_mem_succ_natural hn)
  · exact hc (succ i) (succ_mem_succ_of_natural_mem hn hi)

def IsBoundedFormulaClosed (Q : V) : Prop := ∀ n ∈ (ω : V),
  (⟨n, truthCode⟩ₖ ∈ Q ∧ ⟨n, falsityCode⟩ₖ ∈ Q) ∧
  (∀ r args, IsAtomicArguments membershipLanguageCode ∅ n r args →
    ⟨n, atomCode r args⟩ₖ ∈ Q ∧ ⟨n, negAtomCode r args⟩ₖ ∈ Q) ∧
  (∀ φ ψ, ⟨n, φ⟩ₖ ∈ Q → ⟨n, ψ⟩ₖ ∈ Q →
    ⟨n, andCode φ ψ⟩ₖ ∈ Q ∧ ⟨n, orCode φ ψ⟩ₖ ∈ Q) ∧
  ∀ i ∈ n, ∀ φ, ⟨succ n, φ⟩ₖ ∈ Q →
    ⟨n, boundedAllCode i φ⟩ₖ ∈ Q ∧ ⟨n, boundedExistsCode i φ⟩ₖ ∈ Q

instance isBoundedFormulaClosed_definable : ℒₛₑₜ-predicate[V] IsBoundedFormulaClosed := by
  unfold IsBoundedFormulaClosed truthCode falsityCode
  definability

theorem formulaFamily_boundedClosed :
    IsBoundedFormulaClosed (formulaFamily (membershipLanguageCode : V) ∅) := by
  intro n hn
  have hc := formulaFamily_closed (membershipLanguageCode_valid (V := V)) ∅ n hn
  refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
  intro i hi φ hφ
  have hcs := formulaFamily_closed (membershipLanguageCode_valid (V := V)) ∅ (succ n) (ω_succ_closed hn)
  have ha := hcs.2.1 _ _ (boundedGuardArguments_valid hn hi)
  exact ⟨(hc.2.2.2 _ (hcs.2.2.1 _ _ ha.2 hφ).2).1,
    (hc.2.2.2 _ (hcs.2.2.1 _ _ ha.1 hφ).1).2⟩

noncomputable def boundedFormulaFamily : V :=
  {p ∈ formulaFamily (membershipLanguageCode : V) ∅ ; ∀ Q : V, IsBoundedFormulaClosed Q → p ∈ Q}

theorem mem_boundedFormulaFamily_iff (p : V) : p ∈ (boundedFormulaFamily : V) ↔
    p ∈ formulaFamily (membershipLanguageCode : V) ∅ ∧ ∀ Q : V, IsBoundedFormulaClosed Q → p ∈ Q := by
  simp [boundedFormulaFamily]

theorem boundedFormulaFamily_minimal {Q : V} (hQ : IsBoundedFormulaClosed Q) :
    boundedFormulaFamily ⊆ Q := fun p hp ↦ ((mem_boundedFormulaFamily_iff p).mp hp).2 Q hQ

theorem boundedFormulaFamily_subset :
    (boundedFormulaFamily : V) ⊆ formulaFamily membershipLanguageCode ∅ :=
  fun p hp ↦ ((mem_boundedFormulaFamily_iff p).mp hp).1

theorem boundedFormulaFamily_closed : IsBoundedFormulaClosed (boundedFormulaFamily : V) := by
  intro n hn
  have hc := formulaFamily_boundedClosed (V := V) n hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨(mem_boundedFormulaFamily_iff _).mpr ⟨hc.1.1, fun Q hQ ↦ (hQ n hn).1.1⟩,
      (mem_boundedFormulaFamily_iff _).mpr ⟨hc.1.2, fun Q hQ ↦ (hQ n hn).1.2⟩⟩
  · intro r args ha
    exact ⟨(mem_boundedFormulaFamily_iff _).mpr ⟨(hc.2.1 r args ha).1, fun Q hQ ↦ (hQ n hn).2.1 r args ha |>.1⟩,
      (mem_boundedFormulaFamily_iff _).mpr ⟨(hc.2.1 r args ha).2, fun Q hQ ↦ (hQ n hn).2.1 r args ha |>.2⟩⟩
  · intro φ ψ hφ hψ
    have ha := hc.2.2.1 φ ψ (boundedFormulaFamily_subset _ hφ) (boundedFormulaFamily_subset _ hψ)
    exact ⟨(mem_boundedFormulaFamily_iff _).mpr ⟨ha.1, fun Q hQ ↦
        ((hQ n hn).2.2.1 φ ψ (boundedFormulaFamily_minimal hQ _ hφ) (boundedFormulaFamily_minimal hQ _ hψ)).1⟩,
      (mem_boundedFormulaFamily_iff _).mpr ⟨ha.2, fun Q hQ ↦
        ((hQ n hn).2.2.1 φ ψ (boundedFormulaFamily_minimal hQ _ hφ) (boundedFormulaFamily_minimal hQ _ hψ)).2⟩⟩
  · intro i hi φ hφ
    have ha := hc.2.2.2 i hi φ (boundedFormulaFamily_subset _ hφ)
    exact ⟨(mem_boundedFormulaFamily_iff _).mpr ⟨ha.1, fun Q hQ ↦
        ((hQ n hn).2.2.2 i hi φ (boundedFormulaFamily_minimal hQ _ hφ)).1⟩,
      (mem_boundedFormulaFamily_iff _).mpr ⟨ha.2, fun Q hQ ↦
        ((hQ n hn).2.2.2 i hi φ (boundedFormulaFamily_minimal hQ _ hφ)).2⟩⟩

theorem boundedFormulaFamily_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (hc : ∀ n ∈ (ω : V), P ⟨n, truthCode⟩ₖ ∧ P ⟨n, falsityCode⟩ₖ)
    (ha : ∀ n ∈ (ω : V), ∀ r args, IsAtomicArguments membershipLanguageCode ∅ n r args →
      P ⟨n, atomCode r args⟩ₖ ∧ P ⟨n, negAtomCode r args⟩ₖ)
    (hb : ∀ n ∈ (ω : V), ∀ φ ψ, ⟨n, φ⟩ₖ ∈ (boundedFormulaFamily : V) →
      ⟨n, ψ⟩ₖ ∈ (boundedFormulaFamily : V) → P ⟨n, φ⟩ₖ → P ⟨n, ψ⟩ₖ →
      P ⟨n, andCode φ ψ⟩ₖ ∧ P ⟨n, orCode φ ψ⟩ₖ)
    (hq : ∀ n ∈ (ω : V), ∀ i ∈ n, ∀ φ, ⟨succ n, φ⟩ₖ ∈ (boundedFormulaFamily : V) →
      P ⟨succ n, φ⟩ₖ → P ⟨n, boundedAllCode i φ⟩ₖ ∧ P ⟨n, boundedExistsCode i φ⟩ₖ) :
    ∀ p ∈ (boundedFormulaFamily : V), P p := by
  let S : V := {p ∈ (boundedFormulaFamily : V) ; P p}
  have hS : IsBoundedFormulaClosed S := by
    intro n hn
    have hf := boundedFormulaFamily_closed (V := V) n hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨mem_sep_iff.mpr ⟨hf.1.1, (hc n hn).1⟩,
        mem_sep_iff.mpr ⟨hf.1.2, (hc n hn).2⟩⟩
    · intro r args hargs
      exact ⟨mem_sep_iff.mpr ⟨(hf.2.1 r args hargs).1, (ha n hn r args hargs).1⟩,
        mem_sep_iff.mpr ⟨(hf.2.1 r args hargs).2, (ha n hn r args hargs).2⟩⟩
    · intro φ ψ hφ hψ
      obtain ⟨hφf, hφP⟩ := mem_sep_iff.mp hφ
      obtain ⟨hψf, hψP⟩ := mem_sep_iff.mp hψ
      exact ⟨mem_sep_iff.mpr ⟨(hf.2.2.1 φ ψ hφf hψf).1, (hb n hn φ ψ hφf hψf hφP hψP).1⟩,
        mem_sep_iff.mpr ⟨(hf.2.2.1 φ ψ hφf hψf).2, (hb n hn φ ψ hφf hψf hφP hψP).2⟩⟩
    · intro i hi φ hφ
      obtain ⟨hφf, hφP⟩ := mem_sep_iff.mp hφ
      exact ⟨mem_sep_iff.mpr ⟨(hf.2.2.2 i hi φ hφf).1, (hq n hn i hi φ hφf hφP).1⟩,
        mem_sep_iff.mpr ⟨(hf.2.2.2 i hi φ hφf).2, (hq n hn i hi φ hφf hφP).2⟩⟩
  intro p hp
  exact (mem_sep_iff.mp (boundedFormulaFamily_minimal hS p hp)).2

def IsBoundedFormulaCode (n φ : V) : Prop := ⟨n, φ⟩ₖ ∈ (boundedFormulaFamily : V)

instance isBoundedFormulaCode_definable : ℒₛₑₜ-relation[V] IsBoundedFormulaCode := by
  unfold IsBoundedFormulaCode
  definability

theorem IsBoundedFormulaCode.valid {n φ : V} (hφ : IsBoundedFormulaCode n φ) :
    φ ∈ formulaSet membershipLanguageCode ∅ n :=
  (mem_formulaSet_iff _ _ _ _).mpr (boundedFormulaFamily_subset _ hφ)

theorem IsBoundedFormulaCode.context {n φ : V} (hφ : IsBoundedFormulaCode n φ) : n ∈ (ω : V) :=
  formulaSet_context membershipLanguageCode_valid hφ.valid

theorem encodeMembershipFormula_boundedAll {n : ℕ} (i : Fin n) (φ : SetTheorySemisentence (n + 1)) :
    encodeMembershipFormula (boundedSetAll (.bvar i) φ) =
      boundedAllCode (i.val : V) (encodeMembershipFormula φ) := by
  simp [encodeMembershipFormula, boundedSetAll, encodeSemiformula,
    membershipSymbol, boundedAllCode, boundedGuardArguments]
  congr 4
  funext j
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) j <;>
    simp [encodeSemiterm, num_succ_def]

theorem encodeMembershipFormula_boundedExists {n : ℕ} (i : Fin n) (φ : SetTheorySemisentence (n + 1)) :
    encodeMembershipFormula (boundedSetExs (.bvar i) φ) =
      boundedExistsCode (i.val : V) (encodeMembershipFormula φ) := by
  simp [encodeMembershipFormula, boundedSetExs, encodeSemiformula,
    membershipSymbol, boundedExistsCode, boundedGuardArguments]
  congr 4
  funext j
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) j <;>
    simp [encodeSemiterm, num_succ_def]

theorem IsBoundedSetFormula.encode {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ) :
    IsBoundedFormulaCode (n : V) (encodeMembershipFormula φ) := by
  have hc := boundedFormulaFamily_closed (V := V)
  induction hφ with
  | verum => exact (hc _ (by simp)).1.1
  | falsum => exact (hc _ (by simp)).1.2
  | @rel n k r ts =>
    apply ((hc _ (by simp)).2.1 _ _ ?_).1
    refine Or.inr ⟨membershipSymbol r, (membershipSymbol_valid r).1, rfl, ?_⟩
    rw [(membershipSymbol_valid r).2]
    exact standardTuple_mem_function _ (fun i ↦ encodeSemiterm_mem membershipLanguageCode_valid
      (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) Empty.elim
      (fun k f ↦ membershipFunctionSymbol_valid (k := k) f) (fun x ↦ Empty.elim x) (ts i))
  | @nrel n k r ts =>
    apply ((hc _ (by simp)).2.1 _ _ ?_).2
    refine Or.inr ⟨membershipSymbol r, (membershipSymbol_valid r).1, rfl, ?_⟩
    rw [(membershipSymbol_valid r).2]
    exact standardTuple_mem_function _ (fun i ↦ encodeSemiterm_mem membershipLanguageCode_valid
      (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) Empty.elim
      (fun k f ↦ membershipFunctionSymbol_valid (k := k) f) (fun x ↦ Empty.elim x) (ts i))
  | and hφ hψ ihφ ihψ => exact ((hc _ (by simp)).2.2.1 _ _ ihφ ihψ).1
  | or hφ hψ ihφ ihψ => exact ((hc _ (by simp)).2.2.1 _ _ ihφ ihψ).2
  | @all n t φ hφ ih =>
    cases t with
    | bvar i =>
      rw [encodeMembershipFormula_boundedAll]
      exact ((hc _ (by simp)).2.2.2 _ (natCast_mem_of_lt i.isLt) _ (by simpa [IsBoundedFormulaCode, num_succ_def] using ih)).1
    | fvar x => exact Empty.elim x
    | func f ts => exact Empty.elim f
  | @exs n t φ hφ ih =>
    cases t with
    | bvar i =>
      rw [encodeMembershipFormula_boundedExists]
      exact ((hc _ (by simp)).2.2.2 _ (natCast_mem_of_lt i.isLt) _ (by simpa [IsBoundedFormulaCode, num_succ_def] using ih)).2
    | fvar x => exact Empty.elim x
    | func f ts => exact Empty.elim f

end ZFVP


