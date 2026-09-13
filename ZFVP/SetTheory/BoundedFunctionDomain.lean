import ZFVP.SetTheory.BoundedCodingPrimitives
import ZFVP.SetTheory.FunctionValue

/-! A bounded definition of being a function with a specified domain, without a codomain parameter. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedFunctionDomainFormula : SetTheorySemisentence 2 :=
  “f X. (∀ p ∈ f, ∃ x ∈ X, ∃ d ∈ p, ∃ y ∈ d, !boundedKpairFormula p x y) ∧
    ∀ x ∈ X, ∃ p ∈ f, ∃ d ∈ p, ∃ y ∈ d, !boundedKpairFormula p x y ∧
      ∀ q ∈ f, ∀ e ∈ q, ∀ z ∈ e, !boundedKpairFormula q x z → z = y”

theorem boundedFunctionDomainFormula_bounded : IsBoundedSetFormula boundedFunctionDomainFormula :=
  .and (.all (.bvar 0) (.exs (.bvar 2) (.exs (.bvar 1) (.exs (.bvar 0)
    (boundedKpairFormula_bounded.subst _)))))
    (.all (.bvar 1) (.exs (.bvar 1) (.exs (.bvar 0) (.exs (.bvar 0)
      (.and (boundedKpairFormula_bounded.subst _)
        (.all (.bvar 4) (.all (.bvar 0) (.all (.bvar 0)
          (.or (boundedKpairFormula_bounded.subst _).neg (.rel _ _))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedFunctionDomainFormula (f X : V) :
    boundedFunctionDomainFormula.Evalb ![f, X] ↔ IsFunction f ∧ domain f = X := by
  simp [boundedFunctionDomainFormula]
  constructor
  · rintro ⟨hshape, htotal⟩
    have hf : f ∈ range f ^ X := by
      apply mem_function.intro
      · intro p hp
        obtain ⟨x, hx, _, _, y, _, rfl⟩ := hshape p hp
        exact kpair_mem_iff.mpr ⟨hx, mem_range_of_kpair_mem hp⟩
      · intro x hx
        obtain ⟨d, y, hp, hd, hy, huniq⟩ := htotal x hx
        refine ⟨y, hp, ?_⟩
        intro z hz
        exact huniq ⟨x, z⟩ₖ hz {x, z} (by simp [kpair]) z (by simp) rfl
    exact ⟨IsFunction.of_mem hf, domain_eq_of_mem_function hf⟩
  · rintro ⟨hf, hdom⟩
    let := hf
    constructor
    · intro p hp
      obtain ⟨x, hx, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function (IsFunction.mem_function f) p hp)
      exact ⟨x, hdom ▸ hx, {x, y}, by simp [kpair], y, by simp, rfl⟩
    · intro x hx
      have hxy : ⟨x, f ‘ x⟩ₖ ∈ f := kpair_value_mem (hdom.symm ▸ hx)
      refine ⟨{x, f ‘ x}, f ‘ x, hxy, by simp [kpair], by simp, ?_⟩
      intro q hq e he z hz heq
      exact IsFunction.unique (heq ▸ hq) hxy

instance boundedFunctionDomainFormula_defined :
    ℒₛₑₜ-relation[V] (fun f X : V ↦ IsFunction f ∧ domain f = X) via boundedFunctionDomainFormula :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    change boundedFunctionDomainFormula.Evalb v ↔ IsFunction (v 0) ∧ domain (v 0) = v 1
    rw [← hv]
    exact eval_boundedFunctionDomainFormula _ _⟩

end ZFVP
