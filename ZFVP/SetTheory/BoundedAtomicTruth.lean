import ZFVP.SetTheory.AtomicTruthTables
import ZFVP.SetTheory.BoundedCodingPrimitives
import ZFVP.SetTheory.FiniteCodingClosure

/-! The equations for an atomic equality table are bounded in a transitive support. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedTripleMemberFormula : SetTheorySemisentence 4 :=
  “H x y p. ∃ z ∈ H, ∃ s ∈ z, ∃ a ∈ s,
    !boundedKpairFormula z a p ∧ !boundedKpairFormula a x y”

theorem boundedTripleMemberFormula_bounded : IsBoundedSetFormula boundedTripleMemberFormula :=
  .exs (.bvar 0) (.exs (.bvar 0) (.exs (.bvar 0)
    (.and (boundedKpairFormula_bounded.subst _) (boundedKpairFormula_bounded.subst _))))

def boundedEqualityLeftFormula : SetTheorySemisentence 7 :=
  “T P R H σ τ p. ∀ u ∈ T, ∀ s ∈ T, !boundedPairMemberFormula σ u s →
    ∀ q ∈ P, !boundedPairMemberFormula R q p → !boundedPairMemberFormula R q s →
      ∃ r ∈ P, !boundedPairMemberFormula R r q ∧ ∃ v ∈ T, ∃ t ∈ T,
        !boundedPairMemberFormula τ v t ∧ !boundedPairMemberFormula R r t ∧
          !boundedTripleMemberFormula H u v r”

def boundedEqualityRightFormula : SetTheorySemisentence 7 :=
  “T P R H σ τ p. ∀ v ∈ T, ∀ t ∈ T, !boundedPairMemberFormula τ v t →
    ∀ q ∈ P, !boundedPairMemberFormula R q p → !boundedPairMemberFormula R q t →
      ∃ r ∈ P, !boundedPairMemberFormula R r q ∧ ∃ u ∈ T, ∃ s ∈ T,
        !boundedPairMemberFormula σ u s ∧ !boundedPairMemberFormula R r s ∧
          !boundedTripleMemberFormula H u v r”

def boundedAtomicTestFormula : SetTheorySemisentence 7 :=
  boundedEqualityLeftFormula.and boundedEqualityRightFormula

def boundedAtomicTruthTableFormula : SetTheorySemisentence 4 :=
  “T P R H. ∀ σ ∈ T, ∀ τ ∈ T, ∀ p ∈ P,
    !boundedTripleMemberFormula H σ τ p ↔ !boundedAtomicTestFormula T P R H σ τ p”

theorem boundedEqualityLeftFormula_bounded : IsBoundedSetFormula boundedEqualityLeftFormula := by
  repeat' first
    | exact boundedPairMemberFormula_bounded.subst _
    | exact (boundedPairMemberFormula_bounded.subst _).neg
    | exact boundedTripleMemberFormula_bounded.subst _
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

theorem boundedEqualityRightFormula_bounded : IsBoundedSetFormula boundedEqualityRightFormula := by
  repeat' first
    | exact boundedPairMemberFormula_bounded.subst _
    | exact (boundedPairMemberFormula_bounded.subst _).neg
    | exact boundedTripleMemberFormula_bounded.subst _
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

theorem boundedAtomicTestFormula_bounded : IsBoundedSetFormula boundedAtomicTestFormula :=
  .and boundedEqualityLeftFormula_bounded boundedEqualityRightFormula_bounded

theorem boundedAtomicTruthTableFormula_bounded : IsBoundedSetFormula boundedAtomicTruthTableFormula :=
  .all (.bvar 0) (.all (.bvar 1) (.all (.bvar 3)
    (.and (.or (boundedTripleMemberFormula_bounded.subst _).neg (boundedAtomicTestFormula_bounded.subst _))
      (.or (boundedAtomicTestFormula_bounded.subst _).neg (boundedTripleMemberFormula_bounded.subst _)))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedTripleMemberFormula_defined :
    ℒₛₑₜ-relation₄[V] (fun H x y p ↦ ⟨⟨x, y⟩ₖ, p⟩ₖ ∈ H) via boundedTripleMemberFormula :=
  ⟨fun v ↦ by
    simp [boundedTripleMemberFormula]
    intro _
    exact ⟨{⟨v 1, v 2⟩ₖ}, by simp [kpair], by simp⟩⟩

theorem subname_pair_components_mem_transitive {T x u p : V} [hT : IsTransitive T]
    (hx : x ∈ T) (h : ⟨u, p⟩ₖ ∈ x) : u ∈ T ∧ p ∈ T := by
  exact kpair_components_mem_transitive (hT.mem_trans h hx)

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

theorem eval_boundedAtomicTestFormula {T : V} [IsTransitive T] (P R H σ τ p : V)
    (hσ : σ ∈ T) (hτ : τ ∈ T) :
    boundedAtomicTestFormula.Evalb ![T, P, R, H, σ, τ, p] ↔
      AtomicEqualityTest P R (atomicTruthSet P H) σ τ p := by
  simp [boundedAtomicTestFormula, eval_and, boundedEqualityLeftFormula, boundedEqualityRightFormula,
    AtomicEqualityTest, mem_atomicTruthSet_iff]
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · intro u s hs q hq hqp hqs
      obtain ⟨huT, hsT⟩ := subname_pair_components_mem_transitive hσ hs
      obtain ⟨r, hr, hrq, v, _, t, _, ht, hrt, hh⟩ := hl u huT s hsT hs q hq hqp hqs
      exact ⟨r, hr, hrq, v, t, ht, hrt, hr, hh⟩
    · intro v t ht q hq hqp hqt
      obtain ⟨hvT, htT⟩ := subname_pair_components_mem_transitive hτ ht
      obtain ⟨r, hr, hrq, u, _, s, _, hs, hrs, hh⟩ := hr v hvT t htT ht q hq hqp hqt
      exact ⟨r, hr, hrq, u, s, hs, hrs, hr, hh⟩
  · rintro ⟨hl, hr⟩
    constructor
    · intro u _ s _ hs q hq hqp hqs
      obtain ⟨r, hr, hrq, v, t, ht, hrt, _, hh⟩ := hl u s hs q hq hqp hqs
      obtain ⟨hvT, htT⟩ := subname_pair_components_mem_transitive hτ ht
      exact ⟨r, hr, hrq, v, hvT, t, htT, ht, hrt, hh⟩
    · intro v _ t _ ht q hq hqp hqt
      obtain ⟨r, hr, hrq, u, s, hs, hrs, _, hh⟩ := hr v t ht q hq hqp hqt
      obtain ⟨huT, hsT⟩ := subname_pair_components_mem_transitive hσ hs
      exact ⟨r, hr, hrq, u, huT, s, hsT, hs, hrs, hh⟩

theorem eval_boundedAtomicTruthTableFormula {T : V} [IsTransitive T] (P R H : V) :
    boundedAtomicTruthTableFormula.Evalb ![T, P, R, H] ↔ IsAtomicTruthTable P R T H := by
  simp (config := { contextual := true }) [boundedAtomicTruthTableFormula, IsAtomicTruthTable,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, eval_boundedAtomicTestFormula]

end ZFVP
