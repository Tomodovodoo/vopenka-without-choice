import ZFVP.ModelTheory.InfinitaryWeakChainStructure

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakOmegaChain
open FragmentClosure
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  (C : WeakOmegaChain.{u,v} S)

theorem stageEval_neg {n} {φ : Formula L n}
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S) (b : Fin n → C.Limit) :
    C.StageEval (.neg φ) b ↔ ¬C.StageEval φ b := by
  obtain ⟨i, a, rfl⟩ := C.tuple_cover b
  rw [C.stageEval_fromStage (.neg φ) (neg_closed hφ), C.stageEval_fromStage φ hφ]
  rfl

/-- Every conjunct is evaluated at the same stage as the common finite tuple. -/
theorem stageEval_conj {n} (f : ℕ → Formula L n)
    (hf : ⟨n, .conj f⟩ ∈ FragmentClosure.carrier S)
    (hfi : ∀ l, ⟨n, f l⟩ ∈ FragmentClosure.carrier S) (b : Fin n → C.Limit) :
    C.StageEval (.conj f) b ↔ ∀ l, C.StageEval (f l) b := by
  obtain ⟨i, a, rfl⟩ := C.tuple_cover b
  rw [C.stageEval_fromStage (.conj f) hf]
  exact forall_congr' fun l ↦ (C.stageEval_fromStage (f l) (hfi l) a).symm

theorem stageEval_exs {n} {φ : Formula L (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S) (b : Fin n → C.Limit) :
    C.StageEval (.exs φ) b ↔ ∃ x, C.StageEval φ (x :> b) := by
  obtain ⟨i, a, rfl⟩ := C.tuple_cover b
  rw [C.stageEval_fromStage (.exs φ) (exs_closed hφ)]
  change (∃ x : (C.model i).Domain, Formula.WeakEval (C.model i).Q φ (x :> a)) ↔ _
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨C.fromStage i x, ?_⟩
    have ht := (C.stageEval_fromStage φ hφ (x :> a)).mpr hx
    simpa only [C.fromStage_cons] using ht
  · rintro ⟨x, hx⟩
    obtain ⟨j, y, rfl⟩ := C.stage_cover x
    let k := max i j
    have hi : i ≤ k := Nat.le_max_left _ _
    have hj : j ≤ k := Nat.le_max_right _ _
    have hy : Formula.WeakEval (C.model k).Q φ (C.map hj y :> C.map hi ∘ a) := by
      apply (C.stageEval_fromStage φ hφ _).mp
      simpa only [C.fromStage_cons, ← Function.comp_assoc, C.fromStage_comp,
        C.fromStage_coherent] using hx
    exact (C.map hi).elementary (.exs φ) (exs_closed hφ) a |>.mp ⟨C.map hj y, hy⟩

/-- A fiber is defined from stage evaluation before the limit quantifier is chosen. -/
def LimitFiber {n} (φ : Formula L (n + 1)) (b : Fin n → C.Limit) : Set C.Limit :=
  {x | C.StageEval φ (x :> b)}

/-- The upward closure of the fibers that some source stage declares large. -/
def limitQuantifier (A : Set C.Limit) : Prop :=
  ∃ n, ∃ φ : Formula L (n + 1), ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S ∧
    ∃ i, ∃ b : Fin n → (C.model i).Domain,
      Formula.WeakEval (C.model i).Q (.q φ) b ∧ C.LimitFiber φ (C.fromStage i ∘ b) ⊆ A

theorem limitQuantifier_mono : Monotone C.limitQuantifier := by
  rintro A B hAB ⟨n, φ, hφ, i, b, hq, hs⟩
  exact ⟨n, φ, hφ, i, b, hq, hs.trans hAB⟩

theorem limitQuantifier_fiber {n} {φ : Formula L (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S) (b : Fin n → C.Limit) :
    C.limitQuantifier (C.LimitFiber φ b) ↔ C.StageEval (.q φ) b := by
  obtain ⟨i, a, rfl⟩ := C.tuple_cover b
  rw [C.stageEval_fromStage (.q φ) (q_closed hφ)]
  constructor
  · rintro ⟨m, ψ, hψ, j, c, hq, hs⟩
    let k := max i j
    have hi : i ≤ k := Nat.le_max_left _ _
    have hj : j ≤ k := Nat.le_max_right _ _
    have hqk := (C.map hj).elementary (.q ψ) (q_closed hψ) c |>.mpr hq
    have hsub : {x : (C.model k).Domain |
          Formula.WeakEval (C.model k).Q ψ (x :> C.map hj ∘ c)} ⊆
        {x : (C.model k).Domain |
          Formula.WeakEval (C.model k).Q φ (x :> C.map hi ∘ a)} := by
      intro x hx
      have hx' : C.fromStage k x ∈ C.LimitFiber ψ (C.fromStage j ∘ c) := by
        change C.StageEval ψ _
        have ht := (C.stageEval_fromStage ψ hψ (x :> C.map hj ∘ c)).mpr hx
        simpa only [C.fromStage_cons, ← Function.comp_assoc, C.fromStage_comp] using ht
      have hy := hs hx'
      change C.StageEval φ (C.fromStage k x :> C.fromStage i ∘ a) at hy
      apply (C.stageEval_fromStage φ hφ (x :> C.map hi ∘ a)).mp
      simpa only [C.fromStage_cons, ← Function.comp_assoc, C.fromStage_comp] using hy
    have ht := (C.model k).mono hsub hqk
    exact (C.map hi).elementary (.q φ) (q_closed hφ) a |>.mp ht
  · intro hq
    exact ⟨n, φ, hφ, i, a, hq, Set.Subset.rfl⟩

/-- Equal limit fibers have equal Q truth, even when their formulas, arities,
parameters, and source stages differ. -/
theorem limitFiber_q_extensional {n m} {φ : Formula L (n + 1)} {ψ : Formula L (m + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S)
    (hψ : ⟨m + 1, ψ⟩ ∈ FragmentClosure.carrier S)
    (b : Fin n → C.Limit) (c : Fin m → C.Limit)
    (he : C.LimitFiber φ b = C.LimitFiber ψ c) :
    C.StageEval (.q φ) b ↔ C.StageEval (.q ψ) c := by
  rw [← C.limitQuantifier_fiber hφ, ← C.limitQuantifier_fiber hψ, he]

theorem limit_weak_truth {n} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S) (b : Fin n → C.Limit) :
    Formula.WeakEval C.limitQuantifier φ b ↔ C.StageEval φ b := by
  induction φ with
  | fo φ => exact (C.stageEval_firstOrder φ b).symm
  | neg φ ih =>
    have hc := subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    exact (not_congr (ih hc b)).trans (C.stageEval_neg hc b).symm
  | conj f ih =>
    have hc (l : ℕ) : ⟨_, f l⟩ ∈ FragmentClosure.carrier S :=
      subformulas_closed hφ (Or.inr (Set.mem_iUnion.mpr ⟨l, Formula.self_mem_subformulas (f l)⟩))
    exact (forall_congr' fun l ↦ ih l (hc l) b).trans (C.stageEval_conj f hφ hc b).symm
  | exs φ ih =>
    have hc := subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    exact (exists_congr fun x ↦ ih hc (x :> b)).trans (C.stageEval_exs hc b).symm
  | q φ ih =>
    have hc := subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    have he : {x : C.Limit | Formula.WeakEval C.limitQuantifier φ (x :> b)} =
        C.LimitFiber φ b := by
      ext x
      exact ih hc (x :> b)
    change C.limitQuantifier _ ↔ C.StageEval (.q φ) b
    rw [he]
    exact C.limitQuantifier_fiber hc b

theorem weakEval_fromStage {n i} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S) (b : Fin n → (C.model i).Domain) :
    Formula.WeakEval C.limitQuantifier φ (C.fromStage i ∘ b) ↔
      Formula.WeakEval (C.model i).Q φ b :=
  (C.limit_weak_truth φ hφ _).trans (C.stageEval_fromStage φ hφ b)

noncomputable def limitModel : WeakModel.{u,v} L where
  Domain := C.Limit
  str := C.limitStructure
  eq := C.limitStructure_eq
  nonempty := C.limit_nonempty
  countable := C.limit_countable
  Q := C.limitQuantifier
  mono := C.limitQuantifier_mono

noncomputable def limitEmbedding (i : ℕ) :
    WeakElementaryMap (FragmentClosure.carrier S) (C.model i) C.limitModel where
  toFun := C.fromStage i
  injective := C.fromStage_injective i
  func := fun f b ↦ (C.func_fromStage f b).symm
  rel := C.rel_fromStage
  elementary := C.weakEval_fromStage

theorem limitEmbedding_coherent {i j} (h : i ≤ j) (x : (C.model i).Domain) :
    C.limitEmbedding j (C.map h x) = C.limitEmbedding i x := C.fromStage_coherent h x

/-- The limit is constructed from the chain. No limit-model or model-existence
hypothesis is required. Countability and nonemptiness are fields of the result. -/
theorem exists_countable_weak_limit :
    ∃ N : WeakModel.{u,v} L,
      ∃ e : ∀ i, WeakElementaryMap (FragmentClosure.carrier S) (C.model i) N,
        (∀ i j (h : i ≤ j) x, e j (C.map h x) = e i x) ∧
        ∀ x : N.Domain, ∃ i, ∃ a : (C.model i).Domain, e i a = x :=
  ⟨C.limitModel, C.limitEmbedding, (fun _ _ h x ↦ C.limitEmbedding_coherent h x), C.stage_cover⟩

end WeakOmegaChain
end ZFVP.Infinitary
