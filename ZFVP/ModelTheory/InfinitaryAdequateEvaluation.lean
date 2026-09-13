import ZFVP.ModelTheory.InfinitaryAdequateGenericChain

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v

namespace RightCoordinate
/-- Coordinates are numbered from the right, so front extensions preserve them. -/
def index {i n : ℕ} (h : i < n) : Fin n := ⟨n - (i + 1), by omega⟩

@[simp] theorem embed_index {i n m : ℕ} (hi : i < n) (h : n ≤ m) :
    Formula.rightEmbed h (index hi) = index (hi.trans_le h) := by
  apply Fin.ext
  simp only [Formula.rightEmbed, index]
  omega

def width {n} (ts : Fin n → ℕ) : ℕ := Finset.univ.sup ts + 1

theorem lt_width {n} (ts : Fin n → ℕ) (i : Fin n) : ts i < width ts := by
  have h : ts i ≤ Finset.univ.sup ts := Finset.le_sup (by simp)
  exact Nat.lt_succ_of_le h
end RightCoordinate

namespace WeakModel.AdequateGenericChain
open AdequateFiniteCondition
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}
  {p₀ : AdequateFiniteCondition M S} (C : AdequateGenericChain M S p₀)

def EvalAt (p : AdequateFiniteCondition M S) {n} (φ : ParameterInstance M S n)
    (ts : Fin n → ℕ) : Prop :=
  ∃ h : ∀ i, ts i < 1 + p.1, ∀ b, p.2.formula.Eval b →
    φ.Eval (fun i ↦ b (RightCoordinate.index (h i)))

def Eval {n} (φ : ParameterInstance M S n) (ts : Fin n → ℕ) : Prop :=
  ∃ k, EvalAt (C.point k) φ ts

theorem evalAt_persistent {p q : AdequateFiniteCondition M S} (hpq : Refines p q) {n}
    {φ : ParameterInstance M S n} {ts : Fin n → ℕ} (hp : EvalAt p φ ts) : EvalAt q φ ts := by
  obtain ⟨g, hg⟩ := hpq
  obtain ⟨h, hh⟩ := hp
  refine ⟨fun i ↦ (h i).trans_le (Nat.add_le_add_left g 1), ?_⟩
  intro b hb
  have ht := hh _ (hg b hb)
  simpa only [Function.comp_def, RightCoordinate.embed_index] using ht

theorem coordinate_cofinal (N : ℕ) : ∃ k, N ≤ 1 + (C.point k).1 := by
  obtain ⟨k, hk⟩ := C.arity_unbounded N
  exact ⟨k, by have := hk k (le_refl k); omega⟩

theorem eval_of_valid {n} (φ : ParameterInstance M S n) (ts : Fin n → ℕ)
    (hφ : ∀ a, φ.Eval a) : C.Eval φ ts := by
  obtain ⟨k, hk⟩ := C.coordinate_cofinal (RightCoordinate.width ts)
  exact ⟨k, fun i ↦ (RightCoordinate.lt_width ts i).trans_le hk, fun b _ ↦ hφ _⟩

theorem eval_mono {n} {φ ψ : ParameterInstance M S n} {ts : Fin n → ℕ}
    (h : ∀ b, φ.Eval b → ψ.Eval b) (he : C.Eval φ ts) : C.Eval ψ ts := by
  obtain ⟨k, hk, hh⟩ := he
  exact ⟨k, hk, fun b hb ↦ h _ (hh b hb)⟩

theorem eval_congr {n} {φ ψ : ParameterInstance M S n} {ts : Fin n → ℕ}
    (h : ∀ b, φ.Eval b ↔ ψ.Eval b) : C.Eval φ ts ↔ C.Eval ψ ts :=
  ⟨C.eval_mono (fun b ↦ (h b).mp), C.eval_mono (fun b ↦ (h b).mpr)⟩

theorem eval_of_forces_rename {k n m} (φ : ParameterInstance M S n) (ts : Fin n → ℕ)
    (ht : ∀ i, ts i < m)
    (hf : Forces (C.point k) (φ.rename (fun i ↦ RightCoordinate.index (ht i)))) : C.Eval φ ts := by
  obtain ⟨h, hh⟩ := hf
  refine ⟨k, fun i ↦ (ht i).trans_le h, ?_⟩
  intro b hb
  have he := (ParameterInstance.eval_rename _ _ _).mp (hh b hb)
  simpa only [Function.comp_def, RightCoordinate.embed_index] using he

theorem eval_decided {n} (φ : ParameterInstance M S n) (ts : Fin n → ℕ) :
    C.Eval φ ts ∨ C.Eval φ.neg ts := by
  let ht := RightCoordinate.lt_width ts
  obtain ⟨k, hk⟩ := C.decides (φ.rename (fun i ↦ RightCoordinate.index (ht i)))
  rcases hk k (le_refl k) with hp | hn
  · exact Or.inl (C.eval_of_forces_rename φ ts ht hp)
  · exact Or.inr (C.eval_of_forces_rename φ.neg ts ht hn)

theorem eval_not_both {n} (φ : ParameterInstance M S n) (ts : Fin n → ℕ) :
    ¬(C.Eval φ ts ∧ C.Eval φ.neg ts) := by
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  obtain ⟨h, hh⟩ := evalAt_persistent (C.refines (Nat.le_max_left k l)) hk
  obtain ⟨g, hg⟩ := evalAt_persistent (C.refines (Nat.le_max_right k l)) hl
  obtain ⟨b, hb⟩ := (C.point (max k l)).2.nonempty C.adequate
  exact hg b hb (hh b hb)

@[simp] theorem eval_neg {n} (φ : ParameterInstance M S n) (ts : Fin n → ℕ) :
    C.Eval φ.neg ts ↔ ¬C.Eval φ ts := by
  constructor
  · exact fun hn hp ↦ C.eval_not_both φ ts ⟨hp, hn⟩
  · exact fun hn ↦ (C.eval_decided φ ts).resolve_left hn

@[simp] theorem eval_and {n} (φ ψ : ParameterInstance M S n) (ts : Fin n → ℕ) :
    C.Eval (φ.and ψ) ts ↔ C.Eval φ ts ∧ C.Eval ψ ts := by
  constructor
  · intro h
    exact ⟨C.eval_mono (fun b hb ↦ (ParameterInstance.eval_and _ _ b).mp hb |>.1) h,
      C.eval_mono (fun b hb ↦ (ParameterInstance.eval_and _ _ b).mp hb |>.2) h⟩
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    obtain ⟨h, hh⟩ := evalAt_persistent (C.refines (Nat.le_max_left k l)) hk
    obtain ⟨g, hg⟩ := evalAt_persistent (C.refines (Nat.le_max_right k l)) hl
    exact ⟨max k l, h, fun b hb ↦ (ParameterInstance.eval_and _ _ _).mpr ⟨hh b hb, hg b hb⟩⟩

end WeakModel.AdequateGenericChain
end ZFVP.Infinitary

