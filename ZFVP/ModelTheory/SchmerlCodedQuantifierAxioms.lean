import ZFVP.ModelTheory.SchmerlCodedInfinitarySemantics

/-! The Q-union and Q-interchange axioms hold for represented formulas.
Their countable witness families are constructed inside the ambient model. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language} {L H M : V}
  {F : ∀ {k}, Λ.Func k → V} {R : ∀ {k}, Λ.Rel k → V}
  {C : {n : ℕ} → Formula Λ n → V} {A : Set (Σ n, Formula Λ n)}

namespace IsFragmentCoding

variable (h : IsFragmentCoding L H F R C A) (hω : HasStandardOmega V) (hAC : InternalChoice V)
  (hM : IsStructureCode L M)
  (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧ (functionArities L) ‘ (F f) = (k : V))
  (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧ (relationArities L) ‘ (R r) = (k : V))

include h hω hAC hM hF hR

set_option maxHeartbeats 800000 in
theorem evalWithQ_qCountableUnion {n} (φ : ℕ → Formula Λ (n + 1))
    (hφ : ⟨n + 1, Formula.disj φ⟩ ∈ A) (b : Fin n → CodedDomain M) :
    @Formula.EvalWithQ Λ (CodedDomain M) (codedFoundationStructure hM F R hF)
      (InternalQ M) n (Formula.qCountableUnion φ) b := by
  classical
  let := codedFoundationStructure hM F R hF
  have hconj := h.neg_mem hφ
  obtain ⟨f, _, _, _, hval⟩ := h.conj (fun i ↦ .neg (φ i)) hconj
  let T : V → V → Prop := fun i x ↦
    ¬Holds L H M ((n + 1 : ℕ) : V) (f ‘ i) (assignmentPrepend (n : V) (standardTuple (fun j ↦ (b j).val)) x)
  have hT : ℒₛₑₜ-relation T := by unfold T Holds; definability
  let := hT
  have hTi (i : ℕ) (x : CodedDomain M) : T (i : V) x.val ↔
      Formula.EvalWithQ (InternalQ M) (φ i) (x :> b) := by
    unfold T
    rw [hval]
    have hi := h.holds_iff_evalWithQ hω hM hF hR (.neg (φ i)) (h.conj_mem hconj i) (x :> b)
    exact (not_congr hi).trans (by simp)
  have he : InternalQ M {x | ∃ i, Formula.EvalWithQ (InternalQ M) (φ i) (x :> b)} ↔
      ¬IsInternallyCountable {x ∈ structureDomain M ; ∃ i ∈ (ω : V), T i x} := by
    apply internalQ_iff (fun x hx ↦ (mem_sep_iff.mp hx).1)
    intro x
    simp only [mem_sep_iff, x.property, true_and, hω.exists_iff]
    exact exists_congr fun i ↦ (hTi i x).symm
  simp only [Formula.qCountableUnion, Formula.evalWithQ_imp, Formula.evalWithQ_q,
    Formula.evalWithQ_disj]
  intro hq
  obtain ⟨i, hi, hbig⟩ := internal_uncountable_exists_nat hAC (structureDomain M) T hT (he.mp hq)
  obtain ⟨j, rfl⟩ := hω i hi
  refine ⟨j, ?_⟩
  apply (internalQ_iff (fun x hx ↦ (mem_sep_iff.mp hx).1) (fun x ↦ ?_)).mpr hbig
  simp only [mem_sep_iff, x.property, true_and]
  exact (hTi j x).symm

set_option maxHeartbeats 800000 in
theorem evalWithQ_qInterchange {n} (φ : Formula Λ (n + 1 + 1))
    (hφ : ⟨n + 1 + 1, φ⟩ ∈ A) (b : Fin n → CodedDomain M) :
    @Formula.EvalWithQ Λ (CodedDomain M) (codedFoundationStructure hM F R hF)
      (InternalQ M) n (Formula.qInterchange φ) b := by
  classical
  let := codedFoundationStructure hM F R hF
  let T : V → V → Prop := fun x y ↦ Holds L H M ((n + 1 + 1 : ℕ) : V) (C φ)
    (assignmentPrepend ((n + 1 : ℕ) : V)
      (assignmentPrepend (n : V) (standardTuple (fun i ↦ (b i).val)) y) x)
  have hT : ℒₛₑₜ-relation T := by unfold T Holds; definability
  let := hT
  have hTxy (x y : CodedDomain M) : T x.val y.val ↔
      Formula.EvalWithQ (InternalQ M) φ (x :> y :> b) :=
    h.holds_iff_evalWithQ hω hM hF hR φ hφ (x :> y :> b)
  have hy : InternalQ M {y | ∃ x, Formula.EvalWithQ (InternalQ M) φ (x :> y :> b)} ↔
      ¬IsInternallyCountable {y ∈ structureDomain M ; ∃ x ∈ structureDomain M, T x y} := by
    apply internalQ_iff (fun y hy ↦ (mem_sep_iff.mp hy).1)
    intro y
    simp only [mem_sep_iff, y.property, true_and]
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x.val, x.property, (hTxy x y).mpr hx⟩
    · rintro ⟨x, hx, hxy⟩; exact ⟨⟨x, hx⟩, (hTxy ⟨x, hx⟩ y).mp hxy⟩
  have hx : InternalQ M {x | ∃ y, Formula.EvalWithQ (InternalQ M) φ (x :> y :> b)} ↔
      ¬IsInternallyCountable (sep (structureDomain M) (fun x ↦ ∃ y ∈ structureDomain M, T x y)
        (by unfold T Holds; definability)) := by
    apply internalQ_iff (fun x hx ↦ (mem_sep_iff.mp hx).1)
    intro x
    simp only [mem_sep_iff, x.property, true_and]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y.val, y.property, (hTxy x y).mpr hy⟩
    · rintro ⟨y, hy, hxy⟩; exact ⟨⟨y, hy⟩, (hTxy x ⟨y, hy⟩).mp hxy⟩
  have hf (x : CodedDomain M) : InternalQ M {y | Formula.EvalWithQ (InternalQ M) φ (x :> y :> b)} ↔
      ¬IsInternallyCountable (sep (structureDomain M) (fun y ↦ T x.val y)
        (by unfold T Holds; definability)) := by
    apply internalQ_iff (fun y hy ↦ (mem_sep_iff.mp hy).1)
    intro y
    simp only [mem_sep_iff, y.property, true_and]
    exact (hTxy x y).symm
  simp only [Formula.qInterchange, Formula.evalWithQ_imp, Formula.evalWithQ_or,
    Formula.evalWithQ_q, Formula.evalWithQ_exs, Formula.evalWithQ_swapFirstTwo]
  intro hq
  rcases internal_uncountable_interchange hAC (structureDomain M) T hT (hy.mp hq) with hsome | hmany
  · obtain ⟨x, hx, hbig⟩ := hsome
    exact Or.inl ⟨⟨x, hx⟩, (hf ⟨x, hx⟩).mpr hbig⟩
  · exact Or.inr (hx.mpr hmany)

end IsFragmentCoding

theorem evalWithQ_qMonotonicity [Structure Λ (CodedDomain M)] {n}
    (φ ψ : Formula Λ (n + 1)) (b : Fin n → CodedDomain M) :
    Formula.EvalWithQ (InternalQ M) (Formula.qMonotonicity φ ψ) b := by
  simp only [Formula.qMonotonicity, Formula.evalWithQ_imp, Formula.evalWithQ_all, Formula.evalWithQ_q]
  intro hxy hφ
  exact internalQ_mono (fun x hx ↦ hxy x hx) hφ

theorem evalWithQ_qTwoPoints [Λ.Eq] [Structure Λ (CodedDomain M)] [Structure.Eq Λ (CodedDomain M)]
    {n} (i j : Fin n) (b : Fin n → CodedDomain M) :
    Formula.EvalWithQ (InternalQ M) (Formula.qTwoPoints (L := Λ) i j) b := by
  simp only [Formula.qTwoPoints, Formula.evalWithQ_neg, Formula.evalWithQ_q,
    Formula.evalWithQ_or, Formula.evalWithQ_equal, Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact not_internalQ_twoPoints (b i) (b j)

end ZFVP.Infinitary.Internal
