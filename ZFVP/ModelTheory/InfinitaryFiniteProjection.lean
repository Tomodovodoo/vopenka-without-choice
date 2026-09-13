import ZFVP.ModelTheory.InfinitaryHenkinSequenceDensity

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L : Language}

/-- Existentially remove the first `k` coordinates. -/
def exsN : (k : ℕ) → {n : ℕ} → Formula L (n + k) → Formula L n
  | 0, _, φ => φ
  | k + 1, _, φ => exsN k (.exs φ)

variable {M : Type*} [Structure L M] (Q : Set M → Prop)

@[simp] theorem weakEval_disj {n} (f : ℕ → Formula L n) (b : Fin n → M) :
    WeakEval Q (disj f) b ↔ ∃ i, WeakEval Q (f i) b := by
  classical
  change (¬∀ i, ¬WeakEval Q (f i) b) ↔ _
  simp

theorem weakEval_exsN_congr (k : ℕ) {n} {φ ψ : Formula L (n + k)}
    (h : ∀ b, WeakEval Q φ b ↔ WeakEval Q ψ b) (b : Fin n → M) :
    WeakEval Q (exsN k φ) b ↔ WeakEval Q (exsN k ψ) b := by
  induction k with
  | zero => exact h b
  | succ k ih => exact ih (fun e ↦ exists_congr fun x ↦ h (x :> e))

theorem weakEval_exsN_mono (k : ℕ) {n} {φ ψ : Formula L (n + k)}
    (h : ∀ b, WeakEval Q φ b → WeakEval Q ψ b) (b : Fin n → M) :
    WeakEval Q (exsN k φ) b → WeakEval Q (exsN k ψ) b := by
  induction k with
  | zero => exact h b
  | succ k ih => exact ih (fun e ⟨x, hx⟩ ↦ ⟨x, h (x :> e) hx⟩)

theorem weakEval_exsN_or (k : ℕ) {n} (φ ψ : Formula L (n + k)) (b : Fin n → M) :
    WeakEval Q (exsN k (φ.or ψ)) b ↔
      WeakEval Q (exsN k φ) b ∨ WeakEval Q (exsN k ψ) b := by
  induction k with
  | zero => exact weakEval_or Q φ ψ b
  | succ k ih =>
    exact (weakEval_exsN_congr Q k (φ := .exs (φ.or ψ)) (ψ := (Formula.exs φ).or (.exs ψ))
      (fun e ↦ by simp only [weakEval_exs, weakEval_or, exists_or]) b).trans (ih (.exs φ) (.exs ψ))

theorem weakEval_exsN_disj (k : ℕ) {n} (f : ℕ → Formula L (n + k)) (b : Fin n → M) :
    WeakEval Q (exsN k (disj f)) b ↔ ∃ i, WeakEval Q (exsN k (f i)) b := by
  induction k with
  | zero => exact weakEval_disj Q f b
  | succ k ih =>
    exact (weakEval_exsN_congr Q k (φ := .exs (disj f)) (ψ := disj fun i ↦ .exs (f i))
      (fun e ↦ by simp only [weakEval_exs, weakEval_disj]; exact exists_comm) b).trans
      (ih (fun i ↦ .exs (f i)))

end Formula
namespace FragmentClosure
variable {L : Language} [L.Encodable]

theorem exsN_closed {S : Set (TaggedFormula L)} (k : ℕ) {n} {φ : Formula L (n + k)}
    (hφ : ⟨n + k, φ⟩ ∈ carrier S) : ⟨n, Formula.exsN k φ⟩ ∈ carrier S := by
  induction k with
  | zero => exact hφ
  | succ k ih => exact ih (exs_closed hφ)

end FragmentClosure
namespace SequenceClosure
variable {L : Language} [L.Encodable]

theorem conj_exsN_closed {S : Set (TaggedFormula L)} (k : ℕ) {n} {f : ℕ → Formula L (n + k)}
    (hf : ⟨n + k, .conj f⟩ ∈ carrier S) :
    ⟨n, .conj fun i ↦ Formula.exsN k (f i)⟩ ∈ carrier S := by
  induction k with
  | zero => exact hf
  | succ k ih => exact ih (conj_exs_closed hf)

end SequenceClosure
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ (FragmentClosure.carrier S))

theorem fiber_weakEval {φ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (x : H.Domain) :
    x ∈ H.fiber φ ↔ Formula.WeakEval H.weakQuantifier φ (x :> Fin.elim0) := by
  have ht := H.weak_truth φ hφ (Fin.cases x.out Fin.elim0)
  have he : (fun i ↦ H.classOf (Fin.cases x.out Fin.elim0 i)) = (x :> Fin.elim0) := by
    funext i
    cases i using Fin.cases with
    | zero => exact Quotient.out_eq x
    | succ i => exact i.elim0
  rw [he] at ht
  change φ.subst (Fin.cases x.out Semiterm.bvar) ∈ H.carrier ↔ _
  have hv : (Semiterm.bvar : Fin 0 → Semiterm (limit L) Empty 0) = Fin.elim0 :=
    Subsingleton.elim _ _
  simp only [hv]
  exact ht.symm

theorem fiber_exsN_or (k : ℕ) {φ ψ : Formula (limit L) (1 + k)}
    (hφ : ⟨1 + k, φ⟩ ∈ FragmentClosure.carrier S)
    (hψ : ⟨1 + k, ψ⟩ ∈ FragmentClosure.carrier S) :
    H.fiber (Formula.exsN k (φ.or ψ)) =
      H.fiber (Formula.exsN k φ) ∪ H.fiber (Formula.exsN k ψ) := by
  ext x
  simp only [Set.mem_union, H.fiber_weakEval (exsN_closed k (or_closed hφ hψ)),
    H.fiber_weakEval (exsN_closed k hφ), H.fiber_weakEval (exsN_closed k hψ)]
  exact Formula.weakEval_exsN_or _ k φ ψ _

theorem q_mem_projected_split (k : ℕ) {φ ψ : Formula (limit L) (1 + k)}
    (hφ : ⟨1 + k, φ⟩ ∈ FragmentClosure.carrier S)
    (hψ : ⟨1 + k, ψ⟩ ∈ FragmentClosure.carrier S)
    (hq : .q (Formula.exsN k φ) ∈ H.carrier) :
    .q (Formula.exsN k (φ.and ψ)) ∈ H.carrier ∨
      .q (Formula.exsN k (φ.and (.neg ψ))) ∈ H.carrier := by
  have hl := exsN_closed k (and_closed hφ hψ)
  have hr := exsN_closed k (and_closed hφ (neg_closed hψ))
  have he : H.fiber (Formula.exsN k φ) =
      H.fiber ((Formula.exsN k (φ.and ψ)).or (Formula.exsN k (φ.and (.neg ψ)))) := by
    rw [H.fiber_or hl hr, ← H.fiber_exsN_or k (and_closed hφ hψ) (and_closed hφ (neg_closed hψ))]
    ext x
    rw [H.fiber_weakEval (exsN_closed k hφ),
      H.fiber_weakEval (exsN_closed k (or_closed (and_closed hφ hψ) (and_closed hφ (neg_closed hψ))))]
    apply Formula.weakEval_exsN_congr
    intro b
    simp only [Formula.weakEval_or, Formula.weakEval_and, Formula.weakEval_neg]
    tauto
  exact (H.q_mem_or_iff hl hr).mp
    ((H.q_mem_extensional (exsN_closed k hφ) (or_closed hl hr) he).mp hq)

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary



