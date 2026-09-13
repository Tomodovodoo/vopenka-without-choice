import ZFVP.ModelTheory.InfinitarySubformulas
import Foundation.FirstOrder.Basic.Coding
import Foundation.FirstOrder.Basic.Semantics.Elementary
import Mathlib.ModelTheory.Substructures
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Aleph

/-! Witness closure for a countable infinitary fragment. The auxiliary function
symbols select ordinary witnesses and an injective family of `ℵ₁` witnesses
whenever a standard uncountability quantifier is true. -/

universe u

namespace ZFVP.Infinitary.DownwardLS
open LO LO.FirstOrder Cardinal

abbrev Index : Type u := (Cardinal.aleph.{u} 1).out

@[simp] theorem mk_index : Cardinal.mk Index.{u} = Cardinal.aleph 1 :=
  Cardinal.mk_out _

noncomputable def largeEmbedding {M : Type u} (p : M → Prop)
    (hp : ¬Set.Countable {x | p x}) : Index.{u} ↪ {x // p x} :=
  Classical.choice ((Cardinal.le_def _ _).mp (by
    rw [mk_index, Cardinal.aleph_one_le_iff, ← not_le]
    exact fun h ↦ hp (Cardinal.le_aleph0_iff_set_countable.mp h)))

noncomputable def manyWitness {M : Type u} [Nonempty M] (p : M → Prop)
    (i : Index.{u}) : M := by
  classical
  exact if hp : ¬Set.Countable {x | p x} then (largeEmbedding p hp i).val
    else Classical.choice ‹Nonempty M›

theorem manyWitness_spec {M : Type u} [Nonempty M] {p : M → Prop}
    (hp : ¬Set.Countable {x | p x}) (i : Index.{u}) : p (manyWitness p i) := by
  classical
  simp only [manyWitness, dite_eq_left hp]
  exact (largeEmbedding p hp i).property

theorem manyWitness_injective {M : Type u} [Nonempty M] {p : M → Prop}
    (hp : ¬Set.Countable {x | p x}) : Function.Injective (manyWitness p) := by
  classical
  intro i j h
  simp only [manyWitness, dite_eq_left hp] at h
  exact (largeEmbedding p hp).injective (Subtype.ext h)

theorem index_not_countable : ¬Countable Index.{u} := by
  intro h
  have hh : Cardinal.mk Index.{u} ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  rw [mk_index] at hh
  exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hh

variable {L : Language.{u}} {k : ℕ} (φ : Formula L k)

abbrev Fragment (n : ℕ) := {ψ : Formula L n // ⟨n, ψ⟩ ∈ φ.subformulas}

instance fragment_countable (n : ℕ) : Countable (Fragment φ n) := by
  exact φ.subformulas_countable.preimage (f := Sigma.mk n) (by
    intro a b h
    cases h
    rfl)

abbrev Symbol (n : ℕ) :=
  L.Func n ⊕ (Semisentence L (n + 1) ⊕ (Fragment φ (n + 1) × Option Index.{u}))

def language : _root_.FirstOrder.Language.{u, u} where
  Functions := Symbol φ
  Relations _ := PEmpty

variable {M : Type u} [Nonempty M] [𝓼 : Structure L M]

noncomputable instance witnessStructure : (language φ).Structure M where
  funMap := fun {_n} f b ↦ match f with
    | .inl f => Structure.func f b
    | .inr (.inl ψ) => Classical.epsilon fun x ↦ ψ.Evalb (x :> b)
    | .inr (.inr (ψ, .none)) => Classical.epsilon fun x ↦ Formula.Eval ψ.val (x :> b)
    | .inr (.inr (ψ, .some i)) => manyWitness (fun x ↦ Formula.Eval ψ.val (x :> b)) i
  RelMap := fun r _ ↦ PEmpty.elim r

noncomputable def hull (s : Set M) : Structure.ClosedSubset L M where
  domain := _root_.FirstOrder.Language.Substructure.closure (language φ) s
  domain_closed := fun {_n} f b hb ↦
    (_root_.FirstOrder.Language.Substructure.closure (language φ) s).fun_mem
      (.inl f) b hb

theorem subset_hull (s : Set M) : s ⊆ hull φ s :=
  _root_.FirstOrder.Language.Substructure.subset_closure

theorem symbol_mem_hull (s : Set M) {n : ℕ} (f : Symbol φ n)
    (b : Fin n → M) (hb : ∀ i, b i ∈ hull φ s) :
    _root_.FirstOrder.Language.Structure.funMap (L := language φ) f b ∈ hull φ s :=
  (_root_.FirstOrder.Language.Substructure.closure (language φ) s).fun_mem f b hb

theorem firstOrder_witness_mem (s : Set M) {n : ℕ} (ψ : Semisentence L (n + 1))
    (b : Fin n → M) (hb : ∀ i, b i ∈ hull φ s)
    (hex : ∃ x, ψ.Evalb (x :> b)) :
    ∃ x ∈ hull φ s, ψ.Evalb (x :> b) := by
  refine ⟨Classical.epsilon (fun x ↦ ψ.Evalb (x :> b)), ?_, Classical.epsilon_spec hex⟩
  exact symbol_mem_hull φ s (.inr (.inl ψ)) b hb

theorem hull_nonempty (s : Set M) : (hull φ s : Set M).Nonempty := by
  obtain ⟨x, hx, _⟩ := firstOrder_witness_mem φ s
    (⊤ : Semisentence L 1) ![] (by simp) (by simp)
  exact ⟨x, hx⟩

noncomputable instance hullNonempty (s : Set M) : Nonempty (hull φ s) :=
  (hull_nonempty φ s).to_subtype

theorem infinitary_witness_mem (s : Set M) {n : ℕ} (ψ : Formula L (n + 1))
    (hψ : ⟨n + 1, ψ⟩ ∈ φ.subformulas)
    (b : Fin n → M) (hb : ∀ i, b i ∈ hull φ s)
    (hex : ∃ x, Formula.Eval ψ (x :> b)) :
    ∃ x ∈ hull φ s, Formula.Eval ψ (x :> b) := by
  refine ⟨Classical.epsilon (fun x ↦ Formula.Eval ψ (x :> b)), ?_,
    Classical.epsilon_spec hex⟩
  exact symbol_mem_hull φ s (.inr (.inr (⟨ψ, hψ⟩, .none))) b hb

theorem manyWitness_mem (s : Set M) {n : ℕ} (ψ : Formula L (n + 1))
    (hψ : ⟨n + 1, ψ⟩ ∈ φ.subformulas)
    (b : Fin n → M) (hb : ∀ i, b i ∈ hull φ s) (i : Index.{u}) :
    manyWitness (fun x ↦ Formula.Eval ψ (x :> b)) i ∈ hull φ s :=
  symbol_mem_hull φ s (.inr (.inr (⟨ψ, hψ⟩, .some i))) b hb

section cardinality
variable [L.Encodable]

theorem symbol_card_le (n : ℕ) : Cardinal.mk (Symbol φ n) ≤ Cardinal.aleph 1 := by
  have hω : Cardinal.aleph0 ≤ Cardinal.aleph.{u} 1 := Cardinal.aleph0_le_aleph 1
  have hcount (α : Type u) [Countable α] : Cardinal.mk α ≤ Cardinal.aleph 1 :=
    Cardinal.mk_le_aleph0.trans hω
  dsimp [Symbol]
  rw [Cardinal.mk_sum, Cardinal.mk_sum, Cardinal.mk_prod]
  simp only [Cardinal.lift_id]
  apply Cardinal.add_le_of_le hω (hcount _)
  apply Cardinal.add_le_of_le hω (hcount _)
  apply Cardinal.mul_le_of_le hω (hcount _)
  rw [Cardinal.mk_option, mk_index]
  exact Cardinal.add_le_of_le hω le_rfl (Cardinal.one_le_aleph0.trans hω)

theorem symbols_card_le : Cardinal.mk (Σ n, Symbol φ n) ≤ Cardinal.aleph 1 := by
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun n ↦ Cardinal.mk (Symbol φ n)) ≤
        Cardinal.sum (fun _ : ℕ ↦ Cardinal.aleph.{u} 1) :=
      Cardinal.sum_le_sum _ _ (symbol_card_le φ)
    _ = Cardinal.aleph 1 := by
      rw [Cardinal.sum_const]
      simp only [Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_aleph, Ordinal.lift_one]
      exact Cardinal.mul_eq_right (Cardinal.aleph0_le_aleph 1)
        (Cardinal.aleph0_le_aleph 1) Cardinal.aleph0_ne_zero

theorem hull_card_le (s : Set M) (hs : Cardinal.mk s ≤ Cardinal.aleph 1) :
    Cardinal.mk (hull φ s) ≤ Cardinal.aleph 1 := by
  have h := _root_.FirstOrder.Language.Substructure.lift_card_closure_le
    (L := language φ) (s := s)
  simp only [Cardinal.lift_id] at h
  change Cardinal.mk (_root_.FirstOrder.Language.Substructure.closure (language φ) s) ≤ _
  refine h.trans (max_le (Cardinal.aleph0_le_aleph 1) ?_)
  exact Cardinal.add_le_of_le (Cardinal.aleph0_le_aleph 1) hs (symbols_card_le φ)

end cardinality
end ZFVP.Infinitary.DownwardLS
