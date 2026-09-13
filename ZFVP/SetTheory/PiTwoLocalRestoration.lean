import ZFVP.SetTheory.SigmaTwoWoodinCollapse
import ZFVP.SetTheory.PiTwoForcingDependentChoice
import ZFVP.SetTheory.WoodinPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def piTwoLocalRestorationBody (Ψ : SetTheorySemisentence 5) : SetTheorySemisentence 2 :=
  “κ δ. !IsOrdinal.dfn δ ∧ ∀ P R one,
    !sigmaTwoWoodinCollapseFormula P κ δ → !piOneReverseInclusionOrderFormula R P →
    !boundedEmptyFormula one → ∀ p ∈ P, !Ψ P R one p δ”

theorem piTwoLocalRestorationBody_piTwo {Ψ : SetTheorySemisentence 5} (hΨ : IsPiFormula 2 Ψ) :
    IsPiFormula 2 (piTwoLocalRestorationBody Ψ) :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.all (.all (.or (sigmaTwoWoodinCollapseFormula_sigmaTwo.subst _).neg
      (.or (.raise (piOneReverseInclusionOrderFormula_piOne.subst _).neg)
        (.or (.bounded (boundedEmptyFormula_bounded.subst _).neg)
          (.boundedAll (.bvar 2) (hΨ.subst _))))))))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_piTwoLocalRestorationBody (Ψ : SetTheorySemisentence 5) (κ δ : V) :
    (piTwoLocalRestorationBody Ψ).Evalb ![κ, δ] ↔
      IsOrdinal δ ∧ ∀ p ∈ woodinCollapse κ δ,
        Ψ.Evalb ![woodinCollapse κ δ, woodinCollapseOrder κ δ, ∅, p, δ] := by
  have he : (piTwoLocalRestorationBody Ψ).Evalb ![κ, δ] ↔
      IsOrdinal δ ∧ ∀ P R one : V, (IsOrdinal δ ∧ P = woodinCollapse κ δ) →
        R = reverseInclusionOrder P → one = ∅ → ∀ p ∈ P, Ψ.Evalb ![P, R, one, p, δ] := by
    simp [piTwoLocalRestorationBody, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, eval_sigmaTwoWoodinCollapseFormula,
      eval_piOneReverseInclusionOrderFormula, Semiformula.Evalb]
  rw [he]
  constructor
  · rintro ⟨hd, h⟩
    exact ⟨hd, h _ _ _ ⟨hd, rfl⟩ rfl rfl⟩
  · rintro ⟨hd, h⟩
    refine ⟨hd, ?_⟩
    rintro P R one ⟨_, rfl⟩ rfl rfl
    exact h

theorem woodinLocalRestoration_piTwo_uniform :
    ∃ Φ : SetTheorySemisentence 2, IsPiFormula 2 Φ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ κ δ : V, (∅ : V) ∈ κ →
          (Φ.Evalb ![κ, δ] ↔ IsWoodinLocalRestoration κ δ) := by
  obtain ⟨Ψ, hΨ, he⟩ := forcing_dependentChoiceBelow_piTwo_uniform.{u}
  refine ⟨piTwoLocalRestorationBody Ψ, piTwoLocalRestorationBody_piTwo hΨ, ?_⟩
  intro V _ _ _ κ δ hk
  rw [eval_piTwoLocalRestorationBody]
  unfold IsWoodinLocalRestoration
  apply and_congr_right
  intro hd
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  exact he V _ _ _ p δ (woodinCollapse_poset κ δ).1 (woodinCollapse_top hk δ) hp hd

end ZFVP
