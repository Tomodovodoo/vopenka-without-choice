import ZFVP.ModelTheory.SchmerlInfinitaryDownwardLSClosure

/-! Downward Löwenheim–Skolem for a single `L_{ω₁,ω}(Q)` sentence.
The witness hull preserves every constructor subformula, with parameters from
the hull, and has cardinality at most `ℵ₁` in a countable language. -/

universe u

namespace ZFVP.Infinitary.DownwardLS
open LO LO.FirstOrder

variable {L : Language.{u}} {M : Type u} [Nonempty M] [Structure L M]
  {k : ℕ} (φ : Formula L k) (s : Set M)

theorem term_val {ξ : Type*} {n : ℕ} (t : Semiterm L ξ n)
    (b : Fin n → hull φ s) (f : ξ → hull φ s) :
    ((t.val b f : hull φ s) : M) = t.val (fun i ↦ (b i : M)) (fun i ↦ (f i : M)) := by
  exact Structure.HomClass.val_term (hull φ s).inclusion b f t

theorem firstOrder_eval {n : ℕ} (ψ : Semisentence L n) (b : Fin n → hull φ s) :
    ψ.Evalb b ↔ ψ.Evalb (fun i ↦ (b i : M)) :=
  match ψ with
  | .rel R v | .nrel R v => by
      simp [Semiformula.eval_rel, Semiformula.eval_nrel,
        Structure.ClosedSubset.rel, term_val, Empty.eq_elim, Function.comp_def]
  | ⊤ | ⊥ => by simp
  | ψ ⋏ χ | ψ ⋎ χ => by simp [firstOrder_eval ψ, firstOrder_eval χ]
  | ∀¹ ψ => by
      suffices
          (∃ x ∈ hull φ s, (∼ψ).Evalb (x :> (fun i ↦ (b i : M)))) ↔
          (∃ x : M, (∼ψ).Evalb (x :> (fun i ↦ (b i : M)))) by
        apply not_iff_not.mp
        simpa [firstOrder_eval ψ, Matrix.comp_vecCons']
      constructor
      · rintro ⟨x, _, hx⟩
        exact ⟨x, hx⟩
      · exact firstOrder_witness_mem φ s (∼ψ) _ (fun i ↦ (b i).property)
  | ∃¹ ψ => by
      suffices
          (∃ x ∈ hull φ s, ψ.Evalb (x :> (fun i ↦ (b i : M)))) ↔
          (∃ x : M, ψ.Evalb (x :> (fun i ↦ (b i : M)))) by
        simpa [firstOrder_eval ψ, Matrix.comp_vecCons']
      constructor
      · rintro ⟨x, _, hx⟩
        exact ⟨x, hx⟩
      · exact firstOrder_witness_mem φ s ψ _ (fun i ↦ (b i).property)

theorem uncountable_hull_witnesses {n : ℕ} (ψ : Formula L (n + 1))
    (hψ : ⟨n + 1, ψ⟩ ∈ φ.subformulas) (b : Fin n → hull φ s)
    (hQ : ¬Set.Countable {x : M | Formula.Eval ψ (x :> (fun i ↦ (b i : M)))}) :
    ¬Set.Countable {x : hull φ s |
      Formula.Eval ψ ((x : M) :> (fun i ↦ (b i : M)))} := by
  intro hc
  let p : M → Prop := fun x ↦ Formula.Eval ψ (x :> (fun i ↦ (b i : M)))
  let f : Index.{u} → {x : hull φ s // p (x : M)} := fun i ↦
    ⟨⟨manyWitness p i, manyWitness_mem φ s ψ hψ _ (fun j ↦ (b j).property) i⟩,
      manyWitness_spec hQ i⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact manyWitness_injective hQ (congrArg (fun x ↦ (x.val : M)) hij)
  have : Countable {x : hull φ s // p (x : M)} := hc
  exact index_not_countable hf.countable

theorem eval {n : ℕ} (ψ : Formula L n)
    (hψ : ⟨n, ψ⟩ ∈ φ.subformulas) (b : Fin n → hull φ s) :
    Formula.Eval ψ b ↔ Formula.Eval ψ (fun i ↦ (b i : M)) :=
  match ψ with
  | .fo ψ => firstOrder_eval φ s ψ b
  | .neg ψ => by
      have hchild : ⟨_, ψ⟩ ∈ φ.subformulas :=
        Formula.subformulas_subset_of_mem hψ (Or.inr ψ.self_mem_subformulas)
      exact not_congr (eval ψ hchild b)
  | .conj ψ => by
      apply forall_congr'
      intro i
      have hchild : ⟨_, ψ i⟩ ∈ φ.subformulas :=
        Formula.subformulas_subset_of_mem hψ
          (Or.inr (Set.mem_iUnion.mpr ⟨i, (ψ i).self_mem_subformulas⟩))
      exact eval (ψ i) hchild b
  | .exs ψ => by
      have hchild : ⟨_, ψ⟩ ∈ φ.subformulas :=
        Formula.subformulas_subset_of_mem hψ (Or.inr ψ.self_mem_subformulas)
      change (∃ x : hull φ s, Formula.Eval ψ (x :> b)) ↔
        ∃ x : M, Formula.Eval ψ (x :> (fun i ↦ (b i : M)))
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        simpa only [Matrix.comp_vecCons'] using (eval ψ hchild (x :> b)).mp hx
      · intro hx
        obtain ⟨x, hxmem, hx⟩ := infinitary_witness_mem φ s ψ hchild _
          (fun i ↦ (b i).property) hx
        refine ⟨⟨x, hxmem⟩, ?_⟩
        apply (eval ψ hchild (⟨x, hxmem⟩ :> b)).mpr
        simpa only [Matrix.comp_vecCons'] using hx
  | .q ψ => by
      have hchild : ⟨_, ψ⟩ ∈ φ.subformulas :=
        Formula.subformulas_subset_of_mem hψ (Or.inr ψ.self_mem_subformulas)
      have hsets : {x : hull φ s | Formula.Eval ψ (x :> b)} =
          {x : hull φ s | Formula.Eval ψ ((x : M) :> (fun i ↦ (b i : M)))} := by
        ext x
        simpa only [Set.mem_ofPred_eq, Matrix.comp_vecCons'] using eval ψ hchild (x :> b)
      change (¬Set.Countable {x : hull φ s | Formula.Eval ψ (x :> b)}) ↔
        ¬Set.Countable {x : M | Formula.Eval ψ (x :> (fun i ↦ (b i : M)))}
      rw [hsets]
      constructor
      · intro h hcount
        exact h (hcount.preimage Subtype.val_injective)
      · exact uncountable_hull_witnesses φ s ψ hchild b

theorem sentence_eval (ψ : Sentence L) (s : Set M) :
    Formula.Eval ψ (M := hull ψ s) ![] ↔ Formula.Eval ψ (M := M) ![] := by
  simpa only [Matrix.empty_eq] using eval ψ s ψ ψ.self_mem_subformulas ![]

end ZFVP.Infinitary.DownwardLS

namespace ZFVP.Infinitary
open LO LO.FirstOrder

/-- Every satisfiable sentence in a countable language has a standard model of
cardinality at most `ℵ₁`. This uses witness closure of the given model. -/
theorem exists_small_model {L : Language.{0}} [L.Encodable] (φ : Sentence L)
    (hφ : Satisfiable φ) :
    ∃ N : Type, ∃ _ : Nonempty N, ∃ 𝓼 : Structure L N,
      Cardinal.mk N ≤ Cardinal.aleph 1 ∧ @Formula.Eval L N 𝓼 0 φ ![] := by
  obtain ⟨M, hM, 𝓼, hφ⟩ := hφ
  let : Nonempty M := hM
  let : Structure L M := 𝓼
  let N := DownwardLS.hull φ (∅ : Set M)
  refine ⟨N, inferInstance, inferInstance, ?_, ?_⟩
  · exact DownwardLS.hull_card_le φ ∅ (by simp)
  · exact (DownwardLS.sentence_eval φ ∅).mpr hφ

end ZFVP.Infinitary
