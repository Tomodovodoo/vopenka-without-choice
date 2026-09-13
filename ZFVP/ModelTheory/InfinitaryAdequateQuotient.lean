import ZFVP.ModelTheory.InfinitaryAdequateLogicalLaws

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel.AdequateGenericChain
open AdequateFiniteCondition
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}
  {p₀ : AdequateFiniteCondition M S} (C : AdequateGenericChain M S p₀)

def EqualAt (p : AdequateFiniteCondition M S) (i j : ℕ) : Prop :=
  ∃ hi : i < 1 + p.1, ∃ hj : j < 1 + p.1, ∀ b, p.2.formula.Eval b →
    b (RightCoordinate.index hi) = b (RightCoordinate.index hj)

def Equal (i j : ℕ) : Prop := ∃ k, EqualAt (C.point k) i j

theorem equalAt_persistent {p q : AdequateFiniteCondition M S} (hpq : Refines p q) {i j}
    (he : EqualAt p i j) : EqualAt q i j := by
  obtain ⟨g, hg⟩ := hpq
  obtain ⟨hi, hj, he⟩ := he
  refine ⟨hi.trans_le (Nat.add_le_add_left g 1), hj.trans_le (Nat.add_le_add_left g 1), ?_⟩
  intro b hb
  have ht := he _ (hg b hb)
  simpa only [Function.comp_apply, RightCoordinate.embed_index] using ht

theorem equal_refl (i : ℕ) : C.Equal i i := by
  obtain ⟨k, hk⟩ := C.coordinate_cofinal (i + 1)
  exact ⟨k, by omega, by omega, fun _ _ ↦ rfl⟩

theorem equal_symm {i j} (h : C.Equal i j) : C.Equal j i := by
  obtain ⟨k, hi, hj, h⟩ := h
  exact ⟨k, hj, hi, fun b hb ↦ (h b hb).symm⟩

theorem equal_trans {i j l} (hij : C.Equal i j) (hjl : C.Equal j l) : C.Equal i l := by
  obtain ⟨k, hk⟩ := hij
  obtain ⟨m, hm⟩ := hjl
  obtain ⟨hi, hj, hh⟩ := equalAt_persistent (C.refines (Nat.le_max_left k m)) hk
  obtain ⟨hj', hl, hg⟩ := equalAt_persistent (C.refines (Nat.le_max_right k m)) hm
  exact ⟨max k m, hi, hl, fun b hb ↦ (hh b hb).trans (hg b hb)⟩

def coordinateSetoid : Setoid ℕ where
  r := C.Equal
  iseqv := ⟨C.equal_refl, C.equal_symm, C.equal_trans⟩

def Domain : Type := Quotient C.coordinateSetoid

def classOf (i : ℕ) : C.Domain := Quotient.mk C.coordinateSetoid i

theorem classOf_eq_iff {i j} : C.classOf i = C.classOf j ↔ C.Equal i j := Quotient.eq

instance domain_countable : Countable C.Domain := inferInstanceAs (Countable (Quotient _))
instance domain_nonempty : Nonempty C.Domain := ⟨C.classOf 0⟩

theorem eval_of_equal {n} (φ : ParameterInstance M S n) {ts us : Fin n → ℕ}
    (he : ∀ i, C.Equal (ts i) (us i)) (hp : C.Eval φ ts) : C.Eval φ us := by
  classical
  obtain ⟨k, hk⟩ := hp
  choose j hj using he
  let m := max k (Finset.univ.sup j)
  have hjm (i : Fin n) : j i ≤ m := (Finset.le_sup (by simp)).trans (Nat.le_max_right _ _)
  have heq (i : Fin n) := equalAt_persistent (C.refines (hjm i)) (hj i)
  choose ht hu hh using heq
  obtain ⟨hf, hg⟩ := evalAt_persistent (C.refines (Nat.le_max_left _ _)) hk
  refine ⟨m, hu, ?_⟩
  intro b hb
  have he : (fun i ↦ b (RightCoordinate.index (hf i))) =
      fun i ↦ b (RightCoordinate.index (hu i)) := funext fun i ↦ hh i b hb
  exact he ▸ hg b hb

theorem eval_equal_iff {n} (φ : ParameterInstance M S n) {ts us : Fin n → ℕ}
    (he : ∀ i, C.Equal (ts i) (us i)) : C.Eval φ ts ↔ C.Eval φ us :=
  ⟨C.eval_of_equal φ he, C.eval_of_equal φ (fun i ↦ C.equal_symm (he i))⟩

/-- Evaluation on the quotient before a structure or quantifier has been defined. -/
def QuotientEval {n} (φ : ParameterInstance M S n) (b : Fin n → C.Domain) : Prop :=
  C.Eval φ (fun i ↦ (b i).out)

theorem quotientEval_classOf {n} (φ : ParameterInstance M S n) (ts : Fin n → ℕ) :
    C.QuotientEval φ (C.classOf ∘ ts) ↔ C.Eval φ ts := by
  apply C.eval_equal_iff
  intro i
  exact C.classOf_eq_iff.mp (Quotient.out_eq (C.classOf (ts i)))

theorem classOf_surjective : Function.Surjective C.classOf := by
  intro x
  exact ⟨x.out, Quotient.out_eq x⟩

theorem classOf_cons {n} (t : ℕ) (ts : Fin n → ℕ) :
    C.classOf ∘ (t :> ts) = C.classOf t :> C.classOf ∘ ts := by
  funext i
  cases i using Fin.cases <;> rfl

end WeakModel.AdequateGenericChain
end ZFVP.Infinitary
