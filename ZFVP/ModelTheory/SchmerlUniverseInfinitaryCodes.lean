import ZFVP.ModelTheory.SchmerlUniverseGraphs
import ZFVP.ModelTheory.SchmerlInternalInfinitaryEquations
import ZFVP.ModelTheory.InfinitarySubformulas
import ZFVP.Syntax.FoundationSemantics

/-! Each external infinitary formula has an actual countable code fragment
in the standard universe, with genuine omega-indexed conjunction graphs. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Schmerl

variable {Λ : Language}

noncomputable def universeFormulaCode (F : ∀ {k}, Λ.Func k → Universe.{u})
    (R : ∀ {k}, Λ.Rel k → Universe.{u}) : {n : ℕ} → Formula Λ n → Universe.{u}
  | _, .fo φ => foCode (encodeSemiformula F R Empty.elim φ)
  | _, .neg φ => negCode (universeFormulaCode F R φ)
  | _, .conj φ => conjCode (universeSequence (fun i ↦ universeFormulaCode F R (φ i)))
  | _, .exs φ => exsCode (universeFormulaCode F R φ)
  | _, .q φ => qCode (universeFormulaCode F R φ)

noncomputable def universeContextCode (F : ∀ {k}, Λ.Func k → Universe.{u})
    (R : ∀ {k}, Λ.Rel k → Universe.{u}) (a : Σ n, Formula Λ n) : Universe.{u} :=
  ⟨(a.1 : Universe.{u}), universeFormulaCode F R a.2⟩ₖ

noncomputable def universeFragment (F : ∀ {k}, Λ.Func k → Universe.{u})
    (R : ∀ {k}, Λ.Rel k → Universe.{u}) (A : Set (Σ n, Formula Λ n)) [Small.{u} A] : Universe.{u} :=
  Universe.mk (universeContextCode F R '' A)

theorem mem_universeFragment (F : ∀ {k}, Λ.Func k → Universe.{u})
    (R : ∀ {k}, Λ.Rel k → Universe.{u}) (A : Set (Σ n, Formula Λ n)) [Small.{u} A]
    (t : Universe.{u}) : t ∈ universeFragment F R A ↔ ∃ a ∈ A, universeContextCode F R a = t := by
  simp only [universeFragment, Universe.mem_mk, Set.mem_image]

theorem contextCode_mem_universeFragment (F : ∀ {k}, Λ.Func k → Universe.{u})
    (R : ∀ {k}, Λ.Rel k → Universe.{u}) {A : Set (Σ n, Formula Λ n)} [Small.{u} A]
    {n : ℕ} {φ : Formula Λ n} (hφ : ⟨n, φ⟩ ∈ A) :
    ⟨(n : Universe.{u}), universeFormulaCode F R φ⟩ₖ ∈ universeFragment F R A :=
  (mem_universeFragment F R A _).mpr ⟨⟨n, φ⟩, hφ, rfl⟩

def SubformulaClosed (A : Set (Σ n, Formula Λ n)) : Prop :=
  ∀ a ∈ A, Formula.subformulas a.2 ⊆ A

set_option maxHeartbeats 800000 in
theorem universeFragment_valid {L : Universe.{u}} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → Universe.{u}) (R : ∀ {k}, Λ.Rel k → Universe.{u})
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : Universe.{u}))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧
      (relationArities L) ‘ (R r) = (k : Universe.{u}))
    {A : Set (Σ n, Formula Λ n)} [Small.{u} A] (hA : SubformulaClosed A) :
    IsFragment L (universeFragment F R A) := by
  refine ⟨hL, ?_⟩
  intro t ht
  obtain ⟨⟨n, φ⟩, hφ, rfl⟩ := (mem_universeFragment F R A t).mp ht
  simp only [universeContextCode, kpair.π₁_kpair, kpair.π₂_kpair]
  refine ⟨trivial, by simp, ?_⟩
  have hc := hA ⟨n, φ⟩ hφ
  cases φ with
  | fo φ =>
    refine Or.inl ⟨encodeSemiformula F R Empty.elim φ, ?_, rfl⟩
    exact (mem_formulaSet_iff _ _ _ _).mpr
      (encodeSemiformula_mem_family hL F R Empty.elim hF hR (fun x ↦ Empty.elim x) φ)
  | neg φ =>
    refine Or.inr (Or.inl ⟨universeFormulaCode F R φ, rfl, ?_⟩)
    apply contextCode_mem_universeFragment F R
    exact hc (Or.inr (Formula.self_mem_subformulas φ))
  | conj φ =>
    refine Or.inr (Or.inr (Or.inl
      ⟨universeSequence (fun i ↦ universeFormulaCode F R (φ i)), inferInstance,
        domain_universeSequence _, rfl, ?_⟩))
    intro i hi
    obtain ⟨k, rfl⟩ := universe_standardOmega i hi
    rw [value_universeSequence]
    apply contextCode_mem_universeFragment F R
    exact hc (Or.inr (Set.mem_iUnion.mpr ⟨k, Formula.self_mem_subformulas (φ k)⟩))
  | @exs n φ =>
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨universeFormulaCode F R φ, rfl, ?_⟩)))
    have hh : (⟨n + 1, φ⟩ : Σ m, Formula Λ m) ∈ A :=
      hc (Or.inr (Formula.self_mem_subformulas φ))
    simpa only [num_succ_def] using (contextCode_mem_universeFragment F R (n := n + 1) hh)
  | @q n φ =>
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨universeFormulaCode F R φ, rfl, ?_⟩)))
    have hh : (⟨n + 1, φ⟩ : Σ m, Formula Λ m) ∈ A :=
      hc (Or.inr (Formula.self_mem_subformulas φ))
    simpa only [num_succ_def] using (contextCode_mem_universeFragment F R (n := n + 1) hh)

theorem universeFragment_countable (F : ∀ {k}, Λ.Func k → Universe.{u})
    (R : ∀ {k}, Λ.Rel k → Universe.{u}) {A : Set (Σ n, Formula Λ n)} [Small.{u} A]
    (hA : A.Countable) : IsInternallyCountable (universeFragment F R A) := by
  apply internalCountable_of_external
  have hc := hA.image (universeContextCode F R)
  have he : {t : Universe.{u} | t ∈ universeFragment F R A} = universeContextCode F R '' A := by
    ext t
    exact mem_universeFragment F R A t
  have hh : Set.Countable {t : Universe.{u} | t ∈ universeFragment F R A} := by
    rw [he]
    exact hc
  exact hh.to_subtype

noncomputable def formulaFragment (F : ∀ {k}, Λ.Func k → Universe.{u})
    (R : ∀ {k}, Λ.Rel k → Universe.{u}) {n : ℕ} (φ : Formula Λ n) : Universe.{u} := by
  have := (Formula.subformulas_countable φ).to_subtype
  exact universeFragment F R (Formula.subformulas φ)

theorem formulaFragment_valid {L : Universe.{u}} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → Universe.{u}) (R : ∀ {k}, Λ.Rel k → Universe.{u})
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : Universe.{u}))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧
      (relationArities L) ‘ (R r) = (k : Universe.{u})) {n : ℕ} (φ : Formula Λ n) :
    IsFragment L (formulaFragment F R φ) :=
  universeFragment_valid hL F R hF hR (fun _ h ↦ Formula.subformulas_subset_of_mem h)

theorem formulaFragment_countable (F : ∀ {k}, Λ.Func k → Universe.{u})
    (R : ∀ {k}, Λ.Rel k → Universe.{u}) {n : ℕ} (φ : Formula Λ n) :
    IsInternallyCountable (formulaFragment F R φ) :=
  universeFragment_countable F R (Formula.subformulas_countable φ)

theorem self_mem_formulaFragment (F : ∀ {k}, Λ.Func k → Universe.{u})
    (R : ∀ {k}, Λ.Rel k → Universe.{u}) {n : ℕ} (φ : Formula Λ n) :
    ⟨(n : Universe.{u}), universeFormulaCode F R φ⟩ₖ ∈ formulaFragment F R φ :=
  contextCode_mem_universeFragment F R (Formula.self_mem_subformulas φ)

end ZFVP.Infinitary.Internal
