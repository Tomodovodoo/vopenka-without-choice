import ZFVP.ModelTheory.FiniteParameterElementarity
import ZFVP.SetTheory.ElementaryMap

/-! A bijection preserving and reflecting membership is an isomorphism of set structures, hence
elementary: it preserves the truth of every formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {M M' : Type*} [SetStructure M] [SetStructure M']

/-- An `∈`-isomorphism preserves the truth of every formula. -/
theorem evalb_of_memEquiv (e : M ≃ M') (he : ∀ x y, e x ∈ e y ↔ x ∈ y) {n : ℕ}
    (φ : SetTheorySemisentence n) (b : Fin n → M) :
    φ.Evalb b ↔ φ.Evalb (fun i ↦ e (b i)) := by
  apply Structure.ElementaryEquiv.eval_iff_of_equiv (f₁ := Empty.elim) (f₂ := Empty.elim) e
    (fun x ↦ x.elim) (fun _ ↦ rfl)
  · intro k R v₁ v₂ hv
    cases R with
    | eq =>
      change v₁ 0 = v₁ 1 ↔ v₂ 0 = v₂ 1
      rw [← hv 0, ← hv 1]
      exact e.injective.eq_iff.symm
    | mem =>
      change v₁ 0 ∈ v₁ 1 ↔ v₂ 0 ∈ v₂ 1
      rw [← hv 0, ← hv 1, he]
  · intro k f
    exact f.elim

/-- The elementary map of an `∈`-isomorphism. -/
noncomputable def ElementaryMap.ofMemEquiv [Nonempty M] (e : M ≃ M') (he : ∀ x y, e x ∈ e y ↔ x ∈ y) :
    ElementaryMap M M' where
  toFun := e
  elementary φ b f := elementary_of_semisentences e (fun φ b ↦ evalb_of_memEquiv e he φ b) φ b f

theorem ElementaryMap.ofMemEquiv_apply [Nonempty M] (e : M ≃ M') (he : ∀ x y, e x ∈ e y ↔ x ∈ y) (x : M) :
    ElementaryMap.ofMemEquiv e he x = e x := rfl

end ZFVP
