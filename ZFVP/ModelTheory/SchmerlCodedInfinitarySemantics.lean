import ZFVP.ModelTheory.SchmerlGeneralizedInfinitarySemantics
import ZFVP.ModelTheory.SchmerlUniverseInfinitaryCodes
import ZFVP.ModelTheory.SchmerlInternalQuantifierLaws

/-! A represented fragment has an external generalized-quantifier semantics.
Its Q witnesses are small exactly when an actual internally countable set
covers them. This semantics does not identify internal and external countability. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language}

def InternalQ (M : V) (S : Set (CodedDomain M)) : Prop :=
  ¬∃ A : V, IsInternallyCountable A ∧ ∀ x ∈ S, x.val ∈ A

theorem internalQ_iff {M A : V} {S : Set (CodedDomain M)} (hA : A ⊆ structureDomain M)
    (hS : ∀ x : CodedDomain M, x ∈ S ↔ x.val ∈ A) :
    InternalQ M S ↔ ¬IsInternallyCountable A := by
  apply not_congr
  constructor
  · rintro ⟨B, hB, hcover⟩
    apply internallyCountable_subset hB
    intro x hx
    exact hcover ⟨x, hA x hx⟩ ((hS _).mpr hx)
  · intro h
    exact ⟨A, h, fun x hx ↦ (hS x).mp hx⟩

theorem internalQ_mono {M : V} {S T : Set (CodedDomain M)} (hST : S ⊆ T)
    (hS : InternalQ M S) : InternalQ M T := by
  rintro ⟨A, hA, hcover⟩
  exact hS ⟨A, hA, fun x hx ↦ hcover x (hST hx)⟩

theorem not_internalQ_twoPoints {M : V} (a b : CodedDomain M) :
    ¬InternalQ M {x | x = a ∨ x = b} := by
  intro h
  apply h
  refine ⟨{a.val, b.val}, internal_twoPoints_countable _ _, ?_⟩
  intro x hx
  rcases hx with rfl | rfl <;> simp

structure IsFragmentCoding (L H : V)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V)
    (C : {n : ℕ} → Formula Λ n → V) (A : Set (Σ n, Formula Λ n)) : Prop where
  fragment : IsFragment L H
  closed : SubformulaClosed A
  node : ∀ {n} (φ : Formula Λ n), ⟨n, φ⟩ ∈ A → ⟨(n : V), C φ⟩ₖ ∈ H
  fo : ∀ {n} (φ : Semisentence Λ n), ⟨n, Formula.fo φ⟩ ∈ A → C (.fo φ) = foCode (encodeSemiformula F R Empty.elim φ)
  neg : ∀ {n} (φ : Formula Λ n), ⟨n, Formula.neg φ⟩ ∈ A → C (.neg φ) = negCode (C φ)
  conj : ∀ {n} (φ : ℕ → Formula Λ n), ⟨n, Formula.conj φ⟩ ∈ A → ∃ f : V,
    IsFunction f ∧ domain f = (ω : V) ∧ C (.conj φ) = conjCode f ∧ ∀ i : ℕ, f ‘ (i : V) = C (φ i)
  exs : ∀ {n} (φ : Formula Λ (n + 1)), ⟨n, Formula.exs φ⟩ ∈ A → C (.exs φ) = exsCode (C φ)
  q : ∀ {n} (φ : Formula Λ (n + 1)), ⟨n, Formula.q φ⟩ ∈ A → C (.q φ) = qCode (C φ)

namespace IsFragmentCoding

variable {L H : V} {F : ∀ {k}, Λ.Func k → V} {R : ∀ {k}, Λ.Rel k → V}
  {C : {n : ℕ} → Formula Λ n → V} {A : Set (Σ n, Formula Λ n)}
  (h : IsFragmentCoding L H F R C A)

include h

theorem neg_mem {n} {φ : Formula Λ n} (hφ : ⟨n, .neg φ⟩ ∈ A) : ⟨n, φ⟩ ∈ A :=
  h.closed _ hφ (Or.inr (Formula.self_mem_subformulas φ))
theorem conj_mem {n} {φ : ℕ → Formula Λ n} (hφ : ⟨n, .conj φ⟩ ∈ A) (i : ℕ) : ⟨n, φ i⟩ ∈ A :=
  h.closed _ hφ (Or.inr (Set.mem_iUnion.mpr ⟨i, Formula.self_mem_subformulas (φ i)⟩))
theorem exs_mem {n} {φ : Formula Λ (n + 1)} (hφ : ⟨n, .exs φ⟩ ∈ A) : ⟨n + 1, φ⟩ ∈ A :=
  h.closed _ hφ (Or.inr (Formula.self_mem_subformulas φ))
theorem q_mem {n} {φ : Formula Λ (n + 1)} (hφ : ⟨n, .q φ⟩ ∈ A) : ⟨n + 1, φ⟩ ∈ A :=
  h.closed _ hφ (Or.inr (Formula.self_mem_subformulas φ))

set_option maxHeartbeats 800000 in
theorem holds_iff_evalWithQ (hω : HasStandardOmega V) {M : V} (hM : IsStructureCode L M)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧ (functionArities L) ‘ (F f) = (k : V))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧ (relationArities L) ‘ (R r) = (k : V))
    {n} (φ : Formula Λ n) (hφ : ⟨n, φ⟩ ∈ A) (b : Fin n → CodedDomain M) :
    Holds L H M (n : V) (C φ) (standardTuple (fun i ↦ (b i).val)) ↔
      @Formula.EvalWithQ Λ (CodedDomain M) (codedFoundationStructure hM F R hF) (InternalQ M) n φ b := by
  let := codedFoundationStructure hM F R hF
  have hb {k} (v : Fin k → CodedDomain M) :
      standardTuple (fun i ↦ (v i).val) ∈ structureDomain M ^ (k : V) :=
    standardTuple_mem_function _ (fun i ↦ (v i).property)
  revert hφ b
  induction φ with
  | fo φ =>
    intro hφ b
    have hn := h.node (.fo φ) hφ
    rw [h.fo φ hφ] at hn ⊢
    rw [holds_fo h.fragment hn]
    exact encodeSemiformula_satisfies hM F R hF hR Empty.elim (fun x ↦ Empty.elim x)
      Empty.elim (fun x ↦ Empty.elim x) b φ
  | neg φ ih =>
    intro hφ b
    have hn := h.node (.neg φ) hφ
    rw [h.neg φ hφ] at hn ⊢
    rw [holds_neg h.fragment hn (hb b)]
    exact not_congr (ih (h.neg_mem hφ) b)
  | conj φ ih =>
    intro hφ b
    have hn := h.node (.conj φ) hφ
    obtain ⟨f, _, _, he, hval⟩ := h.conj φ hφ
    rw [he] at hn ⊢
    rw [holds_conj h.fragment hn (hb b), hω.forall_iff]
    simp only [hval, Formula.evalWithQ_conj]
    exact forall_congr' fun i ↦ ih i (h.conj_mem hφ i) b
  | @exs n φ ih =>
    intro hφ b
    have hn := h.node (.exs φ) hφ
    rw [h.exs φ hφ] at hn ⊢
    rw [holds_exs h.fragment hn (hb b)]
    constructor
    · rintro ⟨x, hx, he⟩
      exact ⟨⟨x, hx⟩, (ih (h.exs_mem hφ) (⟨x, hx⟩ :> b)).mp he⟩
    · rintro ⟨x, hx⟩
      exact ⟨x.val, x.property, (ih (h.exs_mem hφ) (x :> b)).mpr hx⟩
  | @q n φ ih =>
    intro hφ b
    have hn := h.node (.q φ) hφ
    rw [h.q φ hφ] at hn ⊢
    rw [holds_q h.fragment hn (hb b)]
    apply Iff.symm
    apply internalQ_iff (fun x hx ↦ (mem_sep_iff.mp hx).1)
    intro x
    simp only [mem_sep_iff, x.property, true_and]
    exact (ih (h.q_mem hφ) (x :> b)).symm

end IsFragmentCoding
end ZFVP.Infinitary.Internal
