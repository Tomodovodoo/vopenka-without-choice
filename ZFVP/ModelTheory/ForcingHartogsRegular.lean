import ZFVP.ModelTheory.ForcingHartogsName
import ZFVP.SetTheory.HartogsLimitRegular
import ZFVP.SetTheory.ChoiceDictionary

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_or {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.or ψ).Evalb v ↔ φ.Evalb v ∨ ψ.Evalb v := Iff.rfl

theorem hartogsNumberName_forces_regular {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (τ : ForcingName P)
    (hτ : p ∈ forcingFormula P R (regularCardinalFormula.or limitOfRegularCardinalsFormula)
      (standardTuple ![τ.val]))
    (hDC : p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![τ.val])) :
    p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R τ.val]) := by
  let κ : ForcingName P := ⟨hartogsNumberName P R τ.val, hartogsNumberName_isName _ _ _⟩
  let φ : SetTheorySemisentence 2 := hartogsNumberFormula.and
    (((regularCardinalFormula.or limitOfRegularCardinalsFormula).subst
      (fun i ↦ .bvar ((![1] : Fin 1 → Fin 2) i))).and
      (dependentChoiceAtFormula.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 2) i))))
  let ψ : SetTheorySemisentence 2 := regularCardinalFormula.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![κ.val, τ.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_rename, forcingFormula_rename]
    exact ⟨hartogsNumberName_forces hR htop hp τ, hτ, hDC⟩
  have hh := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change hartogsNumberFormula.Evalb v ∧
      ((regularCardinalFormula.or limitOfRegularCardinalsFormula).subst
        (fun i ↦ .bvar ((![1] : Fin 1 → Fin 2) i))).Evalb v ∧
      (dependentChoiceAtFormula.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 2) i))).Evalb v at hv
    have hs : v 0 = hartogsNumber (v 1) ∧
        (IsRegularCardinal (v 1) ∨ IsLimitOfRegularCardinals (v 1)) ∧
        InternalDependentChoiceAt (v 1) := by
      simpa [Semiformula.eval_substs, eval_or] using hv
    have hr : IsRegularCardinal (v 0) := by
      rw [hs.1]
      rcases hs.2.1 with hreg | hlim
      · exact hartogsNumber_regular_of_regular hreg hs.2.2
      · exact hartogsNumber_regular_of_limit_regulars hlim hs.2.2
    simpa [ψ, Semiformula.eval_substs] using hr) hR htop hp ![κ, τ] hφ
  change p ∈ forcingFormula P R (regularCardinalFormula.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))) (standardTuple ![κ.val, τ.val]) at hh
  rw [forcingFormula_rename] at hh
  exact hh

end ZFVP
