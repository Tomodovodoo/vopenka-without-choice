import ZFVP.ModelTheory.InfinitaryHenkinWeakTruth

namespace ZFVP.Infinitary
open LO LO.FirstOrder

namespace Formula
variable {L : Language} {M : Type*} [Structure L M] (Q : Set M → Prop)

theorem disj_two {n} (φ ψ : Formula L n) :
    disj (fun i : ℕ ↦ if i = 0 then φ else ψ) = φ.or ψ := by
  apply congrArg Formula.neg
  apply congrArg Formula.conj
  funext i
  by_cases hi : i = 0 <;> simp [hi]

@[simp] theorem weakEval_and {n} (φ ψ : Formula L n) (b : Fin n → M) :
    WeakEval Q (φ.and ψ) b ↔ WeakEval Q φ b ∧ WeakEval Q ψ b := by
  change (∀ i : ℕ, WeakEval Q (if i = 0 then φ else ψ) b) ↔ _
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨hp, hq⟩ i
    split_ifs <;> assumption

@[simp] theorem weakEval_or {n} (φ ψ : Formula L n) (b : Fin n → M) :
    WeakEval Q (φ.or ψ) b ↔ WeakEval Q φ b ∨ WeakEval Q ψ b := by
  classical
  change (¬WeakEval Q ((Formula.neg φ).and (Formula.neg ψ)) b) ↔ _
  rw [weakEval_and]
  change (¬(¬WeakEval Q φ b ∧ ¬WeakEval Q ψ b)) ↔ _
  tauto

@[simp] theorem weakEval_imp {n} (φ ψ : Formula L n) (b : Fin n → M) :
    WeakEval Q (φ.imp ψ) b ↔ (WeakEval Q φ b → WeakEval Q ψ b) := by
  classical
  rw [Formula.imp, weakEval_or]
  change (¬WeakEval Q φ b ∨ WeakEval Q ψ b) ↔ _
  tauto

@[simp] theorem weakEval_all {n} (φ : Formula L (n + 1)) (b : Fin n → M) :
    WeakEval Q (Formula.all φ) b ↔ ∀ x, WeakEval Q φ (x :> b) := by
  classical
  change (¬∃ x, ¬WeakEval Q φ (x :> b)) ↔ _
  simp

@[simp] theorem weakEval_equal [L.Eq] [Structure.Eq L M] {n}
    (i j : Fin n) (b : Fin n → M) : WeakEval Q (equal (L := L) i j) b ↔ b i = b j := by
  change Eval (equal (L := L) i j) b ↔ _
  exact eval_equal i j b

end Formula

namespace KeislerDerivation
variable {L : Language} [L.Eq] {Γ : Set (Sentence L)}

theorem qBinaryUnion {n} (φ ψ : Formula L (n + 1)) :
    KeislerDerivation Γ ((Formula.q (φ.or ψ)).imp ((Formula.q φ).or (Formula.q ψ))) := by
  have h := KeislerDerivation.boolean (Γ := Γ)
    (BooleanDerivation.qUnion (fun i : ℕ ↦ if i = 0 then φ else ψ))
  have he : (fun i : ℕ ↦ Formula.q (if i = 0 then φ else ψ)) =
      (fun i : ℕ ↦ if i = 0 then Formula.q φ else Formula.q ψ) := by
    funext i
    split_ifs <;> rfl
  simpa only [Formula.qCountableUnion, Formula.disj_two, he] using h

end KeislerDerivation

namespace HenkinConstruction.FragmentExtension
open HenkinLanguage KeislerDerivation FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ (FragmentClosure.carrier S))

/-- Every theorem belonging to the fragment is true under every assignment in
the quotient model with its weak quantifier. -/
theorem weakEval_theorem {n} (φ : Formula (limit L) n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S) (d : KeislerDerivation ∅ φ)
    (b : Fin n → H.Domain) : Formula.WeakEval H.weakQuantifier φ b := by
  have hm := H.of_theorem (subst_closed hφ (fun i ↦ (b i).out))
    (d.substitution (fun i ↦ (b i).out))
  have ht := (H.weak_truth φ hφ (fun i ↦ (b i).out)).mpr hm
  have he : (fun i ↦ H.classOf (b i).out) = b := by
    funext i
    exact Quotient.out_eq (b i)
  simpa only [he] using ht

theorem qTwoPoints_in_fragment {n} (i j : Fin n) :
    ⟨n, Formula.qTwoPoints (L := limit L) i j⟩ ∈ FragmentClosure.carrier S :=
  neg_closed (q_closed (or_closed (fo_in_fragment _) (fo_in_fragment _)))

/-- The actual two-point axiom rules out every set consisting of at most two points. -/
theorem weakQuantifier_not_twoPoints (a b : H.Domain) :
    ¬H.weakQuantifier {a, b} := by
  have ht := H.weakEval_theorem (Formula.qTwoPoints (L := limit L) (0 : Fin 2) 1)
    (qTwoPoints_in_fragment 0 1) (.qSmall 0 1) ![a, b]
  change ¬H.weakQuantifier
    {x | Formula.WeakEval H.weakQuantifier
      ((Formula.equal (L := limit L) (0 : Fin 3) 1).or (Formula.equal 0 2)) (x :> ![a, b])} at ht
  have he : {x | Formula.WeakEval H.weakQuantifier
      ((Formula.equal (L := limit L) (0 : Fin 3) 1).or (Formula.equal 0 2)) (x :> ![a, b])} =
      ({a, b} : Set H.Domain) := by
    ext x
    simp
  rwa [he] at ht

theorem weakQuantifier_not_subset_twoPoints {A : Set H.Domain} (a b : H.Domain)
    (hA : A ⊆ {a, b}) : ¬H.weakQuantifier A :=
  fun hq ↦ H.weakQuantifier_not_twoPoints a b (H.weakQuantifier_mono hA hq)

theorem weakQuantifier_not_empty : ¬H.weakQuantifier ∅ := by
  obtain ⟨a⟩ := H.domain_nonempty
  exact H.weakQuantifier_not_subset_twoPoints a a (Set.empty_subset _)

theorem weakQuantifier_nonempty {A : Set H.Domain} (hA : H.weakQuantifier A) :
    A.Nonempty := by
  by_contra hn
  exact H.weakQuantifier_not_empty ((Set.not_nonempty_iff_eq_empty.mp hn) ▸ hA)

theorem q_mem_fiber_nonempty {φ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hq : .q φ ∈ H.carrier) :
    (H.fiber φ).Nonempty :=
  H.weakQuantifier_nonempty ((H.weakQuantifier_fiber hφ).mpr hq)

theorem empty_is_fiber : ∃ φ : Formula (limit L) 1,
    ⟨1, φ⟩ ∈ FragmentClosure.carrier S ∧ H.fiber φ = ∅ := by
  refine ⟨.fo .falsum, fo_in_fragment _, ?_⟩
  ext x
  exact (H.firstOrder_truth (.falsum : Semisentence (limit L) 1)
    (Fin.cases x.out Semiterm.bvar)).symm

theorem singleton_is_fiber (a : H.Domain) : ∃ φ : Formula (limit L) 1,
    ⟨1, φ⟩ ∈ FragmentClosure.carrier S ∧ H.fiber φ = {a} := by
  let φ : Formula (limit L) 1 :=
    Formula.termEqual (.bvar 0) ((Rew.map Fin.elim0 id) a.out)
  refine ⟨φ, fo_in_fragment _, ?_⟩
  ext x
  change φ.substFirst x.out ∈ H.carrier ↔ x = a
  simp only [φ, Formula.substFirst_termEqual, Rew.subst_bvar, Fin.cases_zero,
    Formula.term_subst_closed]
  change H.termRel x.out a.out ↔ x = a
  have hx : H.classOf x.out = x := Quotient.out_eq x
  have ha : H.classOf a.out = a := Quotient.out_eq a
  rw [← H.classOf_eq_iff, hx, ha]

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary
