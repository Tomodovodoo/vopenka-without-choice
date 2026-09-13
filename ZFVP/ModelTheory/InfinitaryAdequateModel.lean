import ZFVP.ModelTheory.InfinitaryWeakChain
import ZFVP.ModelTheory.InfinitarySequenceClosure
import ZFVP.ModelTheory.InfinitaryQInterchangeDensity

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v w

namespace Formula
variable {L : Language}

def qFiniteUnion {n} (φ ψ : Formula L (n + 1)) : Formula L n :=
  (Formula.q (φ.or ψ)).imp ((Formula.q φ).or (Formula.q ψ))

/-- Bind all parameter variables using finitely many ordinary universal quantifiers. -/
def universalClosure : {n : ℕ} → Formula L n → Sentence L
  | 0, φ => φ
  | _n + 1, φ => universalClosure (Formula.all φ)

theorem weakEval_universalClosure {M : Type*} [Structure L M] (Q : Set M → Prop)
    {n} (φ : Formula L n) :
    WeakEval Q (universalClosure φ) Fin.elim0 ↔ ∀ b : Fin n → M, WeakEval Q φ b := by
  induction n with
  | zero =>
    constructor
    · intro h b
      exact (show (Fin.elim0 : Fin 0 → M) = b from Subsingleton.elim _ _) ▸ h
    · intro h
      exact h Fin.elim0
  | succ n ih =>
    rw [universalClosure, ih]
    constructor
    · intro h b
      have ht := (weakEval_all Q φ _).mp (h (fun i ↦ b i.succ)) (b 0)
      have he : b 0 :> (fun i ↦ b i.succ) = b := by
        funext i
        cases i using Fin.cases <;> rfl
      exact he ▸ ht
    · intro h b
      exact (weakEval_all Q φ b).mpr fun x ↦ h (x :> b)

end Formula

namespace FragmentClosure
variable {L : Language} [L.Encodable] {S : Set (TaggedFormula L)}

theorem fo_closed {n} (φ : Semisentence L n) : ⟨n, Formula.fo φ⟩ ∈ carrier S :=
  firstOrder_subset_carrier S (Or.inl ⟨⟨n, φ⟩, rfl⟩)

theorem qTwoPoints_closed [L.Eq] {n} (i j : Fin n) :
    ⟨n, Formula.qTwoPoints (L := L) i j⟩ ∈ carrier S :=
  neg_closed (q_closed (or_closed (fo_closed _) (fo_closed _)))

theorem qFiniteUnion_closed {n} {φ ψ : Formula L (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ carrier S) (hψ : ⟨n + 1, ψ⟩ ∈ carrier S) :
    ⟨n, Formula.qFiniteUnion φ ψ⟩ ∈ carrier S :=
  imp_closed (q_closed (or_closed hφ hψ)) (or_closed (q_closed hφ) (q_closed hψ))

theorem qCountableUnion_closed {n} {f : ℕ → Formula L (n + 1)}
    (hf : ⟨n + 1, Formula.conj f⟩ ∈ carrier (SequenceClosure.carrier S)) :
    ⟨n, Formula.qCountableUnion f⟩ ∈ carrier (SequenceClosure.carrier S) := by
  have hh := hf
  rw [SequenceClosure.base_carrier_eq] at hh
  have hd : ⟨n + 1, Formula.disj f⟩ ∈ carrier (SequenceClosure.carrier S) := by
    rw [SequenceClosure.base_carrier_eq]
    exact SequenceClosure.conj_disj_closed hh
  have hq : ⟨n, Formula.disj (fun i ↦ .q (f i))⟩ ∈ carrier (SequenceClosure.carrier S) := by
    rw [SequenceClosure.base_carrier_eq]
    exact SequenceClosure.conj_disj_closed (SequenceClosure.conj_q_closed hh)
  exact imp_closed (q_closed hd) hq

theorem universalClosure_closed {n} {φ : Formula L n} (hφ : ⟨n, φ⟩ ∈ carrier S) :
    ⟨0, Formula.universalClosure φ⟩ ∈ carrier S := by
  induction n with
  | zero => exact hφ
  | succ n ih => exact ih (all_closed hφ)

end FragmentClosure

namespace WeakElementaryMap
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  {M : WeakModel.{u,v} L} {N : WeakModel.{u,w} L}

/-- Universal closure transfers validity to every target parameter tuple, including
tuples whose entries are outside the embedding's range. -/
theorem valid_transfer (e : WeakElementaryMap (FragmentClosure.carrier S) M N)
    {n} {φ : Formula L n} (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S)
    (hm : ∀ b : Fin n → M.Domain, Formula.WeakEval M.Q φ b) :
    ∀ b : Fin n → N.Domain, Formula.WeakEval N.Q φ b := by
  have hclosed := (Formula.weakEval_universalClosure M.Q φ).mpr hm
  have hn := (e.elementary (Formula.universalClosure φ)
    (FragmentClosure.universalClosure_closed hφ) Fin.elim0).mpr hclosed
  have he : e ∘ (Fin.elim0 : Fin 0 → M.Domain) = (Fin.elim0 : Fin 0 → N.Domain) :=
    Subsingleton.elim _ _
  exact (Formula.weakEval_universalClosure N.Q φ).mp (he ▸ hn)

end WeakElementaryMap

namespace WeakModel

/-- The semantic Q schemas needed for the generic successor construction.
The countable-union field applies only to a represented family in the fragment. -/
structure Adequate {L : Language.{u}} [L.Eq] [L.Encodable]
    (M : WeakModel.{u,v} L) (S : Set (TaggedFormula L)) : Prop where
  twoPoints : ∀ {n} (i j : Fin n) (b : Fin n → M.Domain),
    Formula.WeakEval M.Q (Formula.qTwoPoints (L := L) i j) b
  finiteUnion : ∀ {n} (φ ψ : Formula L (n + 1)),
    ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
    ⟨n + 1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
    ∀ b : Fin n → M.Domain, Formula.WeakEval M.Q (Formula.qFiniteUnion φ ψ) b
  countableUnion : ∀ {n} (f : ℕ → Formula L (n + 1)),
    ⟨n + 1, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
    ∀ b : Fin n → M.Domain, Formula.WeakEval M.Q (Formula.qCountableUnion f) b
  interchange : ∀ {n} (φ : Formula L (n + 1 + 1)),
    ⟨n + 1 + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
    ∀ b : Fin n → M.Domain, Formula.WeakEval M.Q (Formula.qInterchange φ) b

namespace Adequate
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  {M : WeakModel.{u,v} L} {N : WeakModel.{u,w} L}

theorem of_elementary (hM : M.Adequate S)
    (e : WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) M N) :
    N.Adequate S where
  twoPoints i j := e.valid_transfer (FragmentClosure.qTwoPoints_closed i j) (hM.twoPoints i j)
  finiteUnion φ ψ hφ hψ := e.valid_transfer (FragmentClosure.qFiniteUnion_closed hφ hψ)
    (hM.finiteUnion φ ψ hφ hψ)
  countableUnion f hf := e.valid_transfer (FragmentClosure.qCountableUnion_closed hf)
    (hM.countableUnion f hf)
  interchange φ hφ := e.valid_transfer (FragmentClosure.qInterchange_closed hφ) (hM.interchange φ hφ)

theorem not_twoPoints (hM : M.Adequate S) (a b : M.Domain) : ¬M.Q {a, b} := by
  have ht := hM.twoPoints (0 : Fin 2) 1 ![a, b]
  change ¬M.Q {x | Formula.WeakEval M.Q
    ((Formula.equal (L := L) (0 : Fin 3) 1).or (Formula.equal 0 2)) (x :> ![a, b])} at ht
  have he : {x | Formula.WeakEval M.Q
      ((Formula.equal (L := L) (0 : Fin 3) 1).or (Formula.equal 0 2)) (x :> ![a, b])} =
      ({a, b} : Set M.Domain) := by
    ext x
    simp
  exact he ▸ ht

theorem not_empty (hM : M.Adequate S) : ¬M.Q ∅ := by
  obtain ⟨a⟩ := M.nonempty
  exact fun hq ↦ hM.not_twoPoints a a (M.mono (Set.empty_subset _) hq)

theorem nonempty_of_Q (hM : M.Adequate S) {A : Set M.Domain} (hq : M.Q A) : A.Nonempty := by
  by_contra hn
  exact hM.not_empty ((Set.not_nonempty_iff_eq_empty.mp hn) ▸ hq)

end Adequate
end WeakModel
end ZFVP.Infinitary
