import Foundation.FirstOrder.Basic.Coding
import ZFVP.ModelTheory.InfinitarySubformulas
import ZFVP.ModelTheory.InfinitaryRewritingLaws
import ZFVP.ModelTheory.InfinitaryFirstOrderExpansion

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u
variable {L : Language.{u}} [L.Encodable]
abbrev TaggedFormula (L : Language) := Σ n, Formula L n

namespace FragmentClosure

def firstOrder : Set (TaggedFormula L) :=
  Set.range (fun a : Σ n, Semisentence L n ↦ ⟨a.1, .fo a.2⟩) ∪
  Set.range (fun a : Σ n, Semisentence L n ↦ ⟨a.1, Formula.expandFirstOrder a.2⟩)

def successors (a : TaggedFormula L) : Set (TaggedFormula L) :=
  a.2.subformulas ∪ {⟨a.1, .neg a.2⟩} ∪
    ⋃ m : ℕ, Set.range (fun σ : Fin a.1 → Semiterm L Empty m ↦ ⟨m, a.2.subst σ⟩)

theorem firstOrder_countable : (firstOrder (L := L)).Countable := by
  have : Countable (Σ n, Semisentence L n) := inferInstance
  exact (Set.countable_range _).union (Set.countable_range _)

theorem successors_countable (a : TaggedFormula L) : (successors a).Countable := by
  have : ∀ m, Countable (Fin a.1 → Semiterm L Empty m) := fun _ ↦ inferInstance
  exact (a.2.subformulas_countable.union (Set.countable_singleton _)).union
    (Set.countable_iUnion fun _ ↦ Set.countable_range _)

def binders : TaggedFormula L → Set (TaggedFormula L)
  | ⟨0, _⟩ => ∅
  | ⟨n + 1, φ⟩ => {⟨n, .exs φ⟩, ⟨n, .q φ⟩}

def combine (a b : TaggedFormula L) : TaggedFormula L :=
  if h : b.1 = a.1 then ⟨a.1, Formula.and a.2 (h ▸ b.2)⟩ else a

theorem binders_countable (a : TaggedFormula L) : (binders a).Countable := by
  rcases a with ⟨n, φ⟩
  cases n <;> simp only [binders] <;> exact Set.to_countable _

def step (S : Set (TaggedFormula L)) : Set (TaggedFormula L) :=
  S ∪ ((⋃ a ∈ S, successors a) ∪ (⋃ a ∈ S, binders a) ∪
    ⋃ a ∈ S, ⋃ b ∈ S, {combine a b})

def stages (S : Set (TaggedFormula L)) : ℕ → Set (TaggedFormula L)
  | 0 => S ∪ firstOrder
  | n + 1 => step (stages S n)

def carrier (S : Set (TaggedFormula L)) : Set (TaggedFormula L) := ⋃ n, stages S n

theorem stages_mono (S : Set (TaggedFormula L)) : Monotone (stages S) :=
  monotone_nat_of_le_succ (fun _ ↦ Set.subset_union_left)

theorem stages_countable {S : Set (TaggedFormula L)} (hS : S.Countable) (n : ℕ) :
    (stages S n).Countable := by
  induction n with
  | zero => exact hS.union firstOrder_countable
  | succ n ih =>
    exact ih.union (((ih.biUnion (fun a _ ↦ successors_countable a)).union
      (ih.biUnion (fun a _ ↦ binders_countable a))).union
      (ih.biUnion fun a _ ↦ ih.biUnion fun b _ ↦ Set.countable_singleton (combine a b)))

theorem carrier_countable {S : Set (TaggedFormula L)} (hS : S.Countable) :
    (carrier S).Countable := Set.countable_iUnion (stages_countable hS)

theorem subset_carrier (S : Set (TaggedFormula L)) : S ⊆ carrier S :=
  Set.subset_union_left.trans (Set.subset_iUnion (stages S) 0)

theorem firstOrder_subset_carrier (S : Set (TaggedFormula L)) : firstOrder ⊆ carrier S :=
  Set.subset_union_right.trans (Set.subset_iUnion (stages S) 0)

theorem successors_subset_carrier {S : Set (TaggedFormula L)} {a : TaggedFormula L}
    (ha : a ∈ carrier S) : successors a ⊆ carrier S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  intro b hb
  apply Set.mem_iUnion.mpr
  exact ⟨n + 1, Or.inr (Or.inl (Or.inl
    (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨hn, hb⟩⟩)))⟩

theorem subformulas_closed {S : Set (TaggedFormula L)} {n} {φ : Formula L n}
    (hφ : ⟨n, φ⟩ ∈ carrier S) : φ.subformulas ⊆ carrier S := by
  intro b hb
  exact successors_subset_carrier hφ (Or.inl (Or.inl hb))

theorem neg_closed {S : Set (TaggedFormula L)} {n} {φ : Formula L n}
    (hφ : ⟨n, φ⟩ ∈ carrier S) : ⟨n, .neg φ⟩ ∈ carrier S :=
  successors_subset_carrier hφ (Or.inl (Or.inr rfl))

theorem subst_closed {S : Set (TaggedFormula L)} {n m} {φ : Formula L n}
    (hφ : ⟨n, φ⟩ ∈ carrier S) (σ : Fin n → Semiterm L Empty m) :
    ⟨m, φ.subst σ⟩ ∈ carrier S :=
  successors_subset_carrier hφ (Or.inr (Set.mem_iUnion.mpr ⟨m, ⟨σ, rfl⟩⟩))

theorem binders_subset_carrier {S : Set (TaggedFormula L)} {a : TaggedFormula L}
    (ha : a ∈ carrier S) : binders a ⊆ carrier S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  intro b hb
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Or.inl (Or.inr
    (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨hn, hb⟩⟩)))⟩

theorem exs_closed {S : Set (TaggedFormula L)} {n} {φ : Formula L (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ carrier S) : ⟨n, .exs φ⟩ ∈ carrier S :=
  binders_subset_carrier hφ (Or.inl rfl)

theorem q_closed {S : Set (TaggedFormula L)} {n} {φ : Formula L (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ carrier S) : ⟨n, .q φ⟩ ∈ carrier S :=
  binders_subset_carrier hφ (Or.inr rfl)

theorem and_closed {S : Set (TaggedFormula L)} {n} {φ ψ : Formula L n}
    (hφ : ⟨n, φ⟩ ∈ carrier S) (hψ : ⟨n, ψ⟩ ∈ carrier S) :
    ⟨n, Formula.and φ ψ⟩ ∈ carrier S := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hφ
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hψ
  have hi' := stages_mono S (Nat.le_max_left i j) hi
  have hj' := stages_mono S (Nat.le_max_right i j) hj
  apply Set.mem_iUnion.mpr
  refine ⟨max i j + 1, Or.inr (Or.inr ?_)⟩
  exact Set.mem_iUnion.mpr ⟨⟨n, φ⟩, Set.mem_iUnion.mpr ⟨hi',
    Set.mem_iUnion.mpr ⟨⟨n, ψ⟩, Set.mem_iUnion.mpr ⟨hj', by simp [combine]⟩⟩⟩⟩

theorem all_closed {S : Set (TaggedFormula L)} {n} {φ : Formula L (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ carrier S) : ⟨n, Formula.all φ⟩ ∈ carrier S :=
  neg_closed (exs_closed (neg_closed hφ))

theorem or_closed {S : Set (TaggedFormula L)} {n} {φ ψ : Formula L n}
    (hφ : ⟨n, φ⟩ ∈ carrier S) (hψ : ⟨n, ψ⟩ ∈ carrier S) :
    ⟨n, Formula.or φ ψ⟩ ∈ carrier S :=
  neg_closed (and_closed (neg_closed hφ) (neg_closed hψ))

theorem imp_closed {S : Set (TaggedFormula L)} {n} {φ ψ : Formula L n}
    (hφ : ⟨n, φ⟩ ∈ carrier S) (hψ : ⟨n, ψ⟩ ∈ carrier S) :
    ⟨n, Formula.imp φ ψ⟩ ∈ carrier S :=
  or_closed (neg_closed hφ) hψ

theorem iff_closed {S : Set (TaggedFormula L)} {n} {φ ψ : Formula L n}
    (hφ : ⟨n, φ⟩ ∈ carrier S) (hψ : ⟨n, ψ⟩ ∈ carrier S) :
    ⟨n, Formula.iff φ ψ⟩ ∈ carrier S :=
  and_closed (imp_closed hφ hψ) (imp_closed hψ hφ)

end FragmentClosure
end ZFVP.Infinitary
