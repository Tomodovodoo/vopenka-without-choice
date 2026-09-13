import ZFVP.SetTheory.LevyRecursionCertificates
import ZFVP.SetTheory.FunctionUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem restrict_eq_definableGraph_of_values (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {f A : V} [IsFunction f] (hA : A ⊆ domain f) (hv : ∀ x ∈ A, f ‘ x = F x) :
    f ↾ A = definableGraph A F hF := by
  have hd : domain (f ↾ A) = A := by
    rw [domain_restrict_eq, inter_eq_right_of_subset hA]
  apply functions_eq_of_domain_values
  · rw [hd, domain_definableGraph]
  · intro x hx
    rw [hd] at hx
    rw [value_restrict (hA x hx) hx, hv x hx, value_definableGraph _ _ _ hx]

theorem eval_sigmaRecursionAttemptFormula_relation (φ : SetTheorySemisentence 2) (α f : V) :
    (sigmaRecursionAttemptFormula φ).Evalb ![α, f] ↔
      IsOrdinal α ∧ IsFunction f ∧ domain f = α ∧
        ∀ β ∈ α, φ.Evalb ![f ‘ β, f ↾ β] := by
  simp [sigmaRecursionAttemptFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, and_assoc]

/-- Correctness on the intended prefixes suffices for uniqueness of an arbitrary
certified attempt. The induction is internal ordinal induction on a definable predicate. -/
theorem eval_sigmaRecursionAttemptFormula_of_prefix_definitions
    (φ : SetTheorySemisentence 2) (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (α f : V) [IsOrdinal α]
    (he : ∀ β ∈ α, ∀ y : V, φ.Evalb ![y, definableGraph β F hF] ↔ y = F β) :
    (sigmaRecursionAttemptFormula φ).Evalb ![α, f] ↔ f = definableGraph α F hF := by
  rw [eval_sigmaRecursionAttemptFormula_relation]
  constructor
  · rintro ⟨_, hf, hd, hs⟩
    let := hf
    have hv : ∀ β : Ordinal V, (β : V) ∈ α → f ‘ (β : V) = F β := by
      apply transfinite_induction (P := fun β : V ↦ β ∈ α → f ‘ β = F β) (by definability)
      intro β ih hβ
      have hsub : (β : V) ⊆ α := IsOrdinal.toIsTransitive.transitive _ hβ
      have hr : f ↾ (β : V) = definableGraph (β : V) F hF := by
        apply restrict_eq_definableGraph_of_values F hF (hd.symm ▸ hsub)
        intro x hx
        let := IsOrdinal.of_mem hx
        exact ih (IsOrdinal.toOrdinal x) hx (hsub x hx)
      have hh := hs β hβ
      rw [hr] at hh
      exact (he β hβ _).mp hh
    have hr := restrict_eq_definableGraph_of_values F hF (f := f)
      (A := α) (subset_of_eq hd.symm) (fun x hx ↦ by
        let := IsOrdinal.of_mem hx
        exact hv (IsOrdinal.toOrdinal x) hx)
    rwa [IsFunction.restrict_eq_self f α (subset_of_eq hd)] at hr
  · rintro rfl
    refine ⟨inferInstance, inferInstance, domain_definableGraph _ _ _, ?_⟩
    intro β hβ
    have hsub : β ⊆ α := IsOrdinal.toIsTransitive.transitive _ hβ
    have hr : (definableGraph α F hF) ↾ β = definableGraph β F hF :=
      restrict_eq_definableGraph_of_values F hF (by simpa only [domain_definableGraph] using hsub)
        (fun x hx ↦ value_definableGraph _ _ _ (hsub x hx))
    rw [hr, value_definableGraph _ _ _ hβ]
    exact (he β hβ _).mpr rfl

/-- Evaluation of the recursion formula needs the prefix condition through the
current ordinal, but imposes no correctness requirement on unrelated histories. -/
theorem eval_sigmaTransfiniteRecFormula_of_prefix_definitions
    (φ : SetTheorySemisentence 2) (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (α y : V) [IsOrdinal α]
    (he : ∀ β ∈ succ α, ∀ z : V, φ.Evalb ![z, definableGraph β F hF] ↔ z = F β) :
    (sigmaTransfiniteRecFormula φ).Evalb ![y, α] ↔ y = F α := by
  have ha := fun f ↦ eval_sigmaRecursionAttemptFormula_of_prefix_definitions φ F hF α f
    (fun β hβ ↦ he β (mem_succ_iff.mpr (Or.inr hβ)))
  have hs := he α (mem_succ_self α)
  simp only [Semiformula.Evalb] at ha hs
  simp [sigmaTransfiniteRecFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, ha, hs, show IsOrdinal α from inferInstance]

end ZFVP
