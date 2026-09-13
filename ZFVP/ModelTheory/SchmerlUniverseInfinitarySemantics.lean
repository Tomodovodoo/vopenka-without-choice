import ZFVP.ModelTheory.SchmerlUniverseInfinitaryCodes

/-! The standard universe interprets represented infinitary formulas with
exactly the external standard uncountability quantifier. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Schmerl

variable {Λ : Language}

theorem universe_witnessFiber_countable_iff (M n b g φ : Universe.{u})
    (P : CodedDomain M → Prop)
    (hP : ∀ x : CodedDomain M,
      assignmentPrepend n b x.val ∈ g ‘ ⟨succ n, φ⟩ₖ ↔ P x) :
    IsInternallyCountable (witnessFiber M n b g φ) ↔ Set.Countable {x : CodedDomain M | P x} := by
  rw [universe_internalCountable_iff, ← Set.countable_coe_iff]
  let e : {x : Universe.{u} // x ∈ witnessFiber M n b g φ} ≃ {x : CodedDomain M // P x} :=
    { toFun := fun x ↦ ⟨⟨x.val, (mem_sep_iff.mp x.property).1⟩,
        (hP _).mp (mem_sep_iff.mp x.property).2⟩
      invFun := fun x ↦ ⟨x.val.val, mem_sep_iff.mpr ⟨x.val.property, (hP _).mpr x.property⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact e.countable_iff

set_option maxHeartbeats 800000 in
theorem universeHolds_iff_eval {L M : Universe.{u}} (hM : IsStructureCode L M)
    (F : ∀ {k}, Λ.Func k → Universe.{u}) (R : ∀ {k}, Λ.Rel k → Universe.{u})
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : Universe.{u}))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧
      (relationArities L) ‘ (R r) = (k : Universe.{u}))
    {A : Set (Σ n, Formula Λ n)} [Small.{u} A] (hA : SubformulaClosed A)
    {n : ℕ} (φ : Formula Λ n) (hφ : ⟨n, φ⟩ ∈ A) (b : Fin n → CodedDomain M) :
    Holds L (universeFragment F R A) M (n : Universe.{u}) (universeFormulaCode F R φ)
      (standardTuple (fun i ↦ (b i).val)) ↔
      @Formula.Eval Λ (CodedDomain M) (codedFoundationStructure hM F R hF) n φ b := by
  have hfrag := universeFragment_valid hM.language F R hF hR hA
  have hb : ∀ {k} (v : Fin k → CodedDomain M),
      standardTuple (fun i ↦ (v i).val) ∈ structureDomain M ^ (k : Universe.{u}) :=
    fun v ↦ standardTuple_mem_function _ (fun i ↦ (v i).property)
  have node {k : ℕ} (ψ : Formula Λ k) (hψ : ⟨k, ψ⟩ ∈ A) :
      ⟨(k : Universe.{u}), universeFormulaCode F R ψ⟩ₖ ∈ universeFragment F R A :=
    contextCode_mem_universeFragment F R (n := k) hψ
  revert hφ b
  induction φ with
  | @fo n φ =>
    intro hφ b
    rw [universeFormulaCode, holds_fo hfrag (node (.fo φ) hφ)]
    exact encodeSemiformula_satisfies hM F R hF hR Empty.elim (fun x ↦ Empty.elim x)
      Empty.elim (fun x ↦ Empty.elim x) b φ
  | @neg n φ ih =>
    intro hφ b
    rw [universeFormulaCode, holds_neg hfrag (node (.neg φ) hφ) (hb b)]
    exact not_congr (ih (hA _ hφ (Or.inr (Formula.self_mem_subformulas φ))) b)
  | @conj n φ ih =>
    intro hφ b
    rw [universeFormulaCode, holds_conj hfrag (node (.conj φ) hφ) (hb b)]
    rw [universe_standardOmega.forall_iff]
    simp only [value_universeSequence, Formula.eval_conj]
    apply forall_congr'
    intro i
    exact ih i (hA _ hφ (Or.inr (Set.mem_iUnion.mpr ⟨i, Formula.self_mem_subformulas (φ i)⟩))) b
  | @exs n φ ih =>
    intro hφ b
    rw [universeFormulaCode, holds_exs hfrag (node (.exs φ) hφ) (hb b)]
    have hc := hA _ hφ (Or.inr (Formula.self_mem_subformulas φ))
    change (∃ x ∈ structureDomain M,
      Holds L (universeFragment F R A) M ((n + 1 : ℕ) : Universe.{u}) (universeFormulaCode F R φ)
        (assignmentPrepend (n : Universe.{u}) (standardTuple (fun i ↦ (b i).val)) x)) ↔
      ∃ x : CodedDomain M, _
    constructor
    · rintro ⟨x, hx, h⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      exact (ih hc (⟨x, hx⟩ :> b)).mp h
    · rintro ⟨x, hx⟩
      exact ⟨x.val, x.property, (ih hc (x :> b)).mpr hx⟩
  | @q n φ ih =>
    intro hφ b
    rw [universeFormulaCode, holds_q hfrag (node (.q φ) hφ) (hb b)]
    have hc := hA _ hφ (Or.inr (Formula.self_mem_subformulas φ))
    change (¬IsInternallyCountable _) ↔ ¬Set.Countable _
    apply not_congr
    apply universe_witnessFiber_countable_iff
    intro x
    exact ih hc (x :> b)

theorem formulaFragment_holds_iff_eval {L M : Universe.{u}} (hM : IsStructureCode L M)
    (F : ∀ {k}, Λ.Func k → Universe.{u}) (R : ∀ {k}, Λ.Rel k → Universe.{u})
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : Universe.{u}))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧
      (relationArities L) ‘ (R r) = (k : Universe.{u}))
    {n : ℕ} (φ : Formula Λ n) (b : Fin n → CodedDomain M) :
    Holds L (formulaFragment F R φ) M (n : Universe.{u}) (universeFormulaCode F R φ)
      (standardTuple (fun i ↦ (b i).val)) ↔
      @Formula.Eval Λ (CodedDomain M) (codedFoundationStructure hM F R hF) n φ b :=
  universeHolds_iff_eval hM F R hF hR (fun _ h ↦ Formula.subformulas_subset_of_mem h)
    φ (Formula.self_mem_subformulas φ) b

end ZFVP.Infinitary.Internal
