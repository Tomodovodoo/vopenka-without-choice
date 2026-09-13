import ZFVP.ModelTheory.InfinitaryEqualityDerivation

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage KeislerDerivation FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ (FragmentClosure.carrier S))

theorem fo_in_fragment {n} (φ : Semisentence (limit L) n) : ⟨n, .fo φ⟩ ∈ FragmentClosure.carrier S :=
  firstOrder_subset_carrier S (Or.inl ⟨⟨n, φ⟩, rfl⟩)

theorem termEqual_in_fragment (s t : Semiterm (limit L) Empty 0) :
    ⟨0, Formula.termEqual s t⟩ ∈ FragmentClosure.carrier S := fo_in_fragment _

/-- The equivalence relation on closed terms read from the Henkin theory. -/
def termRel (s t : Semiterm (limit L) Empty 0) : Prop := Formula.termEqual s t ∈ H.carrier

theorem termRel_refl (s : Semiterm (limit L) Empty 0) : H.termRel s s :=
  H.of_theorem (termEqual_in_fragment s s) (.eqRefl s)

theorem termRel_symm {s t : Semiterm (limit L) Empty 0} (h : H.termRel s t) :
    H.termRel t s := by
  classical
  apply H.of_finite_proof {Formula.termEqual s t} (by simpa [termRel] using h) (termEqual_in_fragment t s)
  exact (of_mem (by simp)).equality_symm

theorem termRel_trans {r s t : Semiterm (limit L) Empty 0}
    (h : H.termRel r s) (g : H.termRel s t) : H.termRel r t := by
  classical
  refine H.of_finite_proof {Formula.termEqual r s, Formula.termEqual s t} ?_
    (termEqual_in_fragment r t) ?_
  · intro φ hφ
    rcases Finset.mem_insert.mp hφ with rfl | hφ
    · exact h
    · have he := Finset.mem_singleton.mp hφ
      subst φ
      exact g
  · exact (of_mem (φ := Formula.termEqual r s) (by simp)).equality_trans (of_mem (by simp))

def termSetoid : Setoid (Semiterm (limit L) Empty 0) where
  r := H.termRel
  iseqv := ⟨H.termRel_refl, H.termRel_symm, H.termRel_trans⟩

theorem substFirst_mem_congr (φ : Formula (limit L) 1)
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) {s t : Semiterm (limit L) Empty 0}
    (h : H.termRel s t) : φ.substFirst s ∈ H.carrier ↔ φ.substFirst t ∈ H.carrier := by
  classical
  have forward {s t : Semiterm (limit L) Empty 0} (he : H.termRel s t)
      (hp : φ.substFirst s ∈ H.carrier) : φ.substFirst t ∈ H.carrier := by
    refine H.of_finite_proof {Formula.termEqual s t, φ.substFirst s} ?_
      (subst_closed hφ _) ?_
    · intro ψ hψ
      rcases Finset.mem_insert.mp hψ with rfl | hψ
      · exact he
      · have heq := Finset.mem_singleton.mp hψ
        subst ψ
        exact hp
    · exact .mp (KeislerDerivation.mp (.eqSubst φ s t) (of_mem (by simp))).iff_left
        (of_mem (by simp))
  exact ⟨forward h, forward (H.termRel_symm h)⟩

theorem subst_update_mem_congr {n} (φ : Formula (limit L) n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S)
    (σ : Fin n → Semiterm (limit L) Empty 0) (i : Fin n)
    {s t : Semiterm (limit L) Empty 0} (h : H.termRel s t) :
    φ.subst (Function.update σ i s) ∈ H.carrier ↔
      φ.subst (Function.update σ i t) ∈ H.carrier := by
  simpa only [Formula.substFirst_oneVariable] using
    H.substFirst_mem_congr (φ.subst (oneVariableSubstitution σ i)) (subst_closed hφ _) h

theorem subst_mem_congr {n} (φ : Formula (limit L) n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S)
    (σ τ : Fin n → Semiterm (limit L) Empty 0) (h : ∀ i, H.termRel (σ i) (τ i)) :
    φ.subst σ ∈ H.carrier ↔ φ.subst τ ∈ H.carrier := by
  classical
  have hmix (A : Finset (Fin n)) :
      φ.subst (fun i ↦ if i ∈ A then τ i else σ i) ∈ H.carrier ↔ φ.subst σ ∈ H.carrier := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert i A hi ih =>
      let v : Fin n → Semiterm (limit L) Empty 0 := fun j ↦ if j ∈ A then τ j else σ j
      have hv : v i = σ i := by simp [v, hi]
      have hs := H.subst_update_mem_congr φ hφ v i (s := v i) (t := τ i) (by simpa only [hv] using h i)
      rw [Function.update_eq_self] at hs
      have he : (fun j ↦ if j ∈ insert i A then τ j else σ j) = Function.update v i (τ i) := by
        funext j
        by_cases hj : j = i
        · subst j; simp
        · simp [Finset.mem_insert, hj, Function.update_of_ne hj, v]
      rw [he]
      exact hs.symm.trans ih
  have he := hmix Finset.univ
  simpa only [Finset.mem_univ, ite_true] using he.symm

theorem func_termRel {n} (f : (limit L).Func n)
    (σ τ : Fin n → Semiterm (limit L) Empty 0) (h : ∀ i, H.termRel (σ i) (τ i)) :
    H.termRel (.func f σ) (.func f τ) := by
  let φ : Formula (limit L) n := Formula.termEqual (.func f Semiterm.bvar)
    ((Rew.map Fin.elim0 id) (.func f σ))
  have he := H.subst_mem_congr φ (fo_in_fragment _) σ τ h
  simp only [φ, Formula.subst_termEqual, Formula.term_subst_closed] at he
  simp only [Rew.func, Function.comp_def, Rew.subst_bvar] at he
  exact H.termRel_symm (he.mp (H.termRel_refl (.func f σ)))

theorem rel_mem_congr {n} (r : (limit L).Rel n)
    (σ τ : Fin n → Semiterm (limit L) Empty 0) (h : ∀ i, H.termRel (σ i) (τ i)) :
    Formula.fo (.rel r σ) ∈ H.carrier ↔ Formula.fo (.rel r τ) ∈ H.carrier := by
  have he := H.subst_mem_congr (.fo (.rel r Semiterm.bvar)) (fo_in_fragment _) σ τ h
  exact he

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary




