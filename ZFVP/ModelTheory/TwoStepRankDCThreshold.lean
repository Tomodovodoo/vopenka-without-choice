import ZFVP.ModelTheory.ForcingRankDCThreshold
import ZFVP.ModelTheory.TwoStepCheckedSemantics

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem uniform_twoStep_rankDCThreshold {δ γ P R Q S t one : V}
    (hδ : IsWoodinSupercompact δ) (hC : twoStepConditions P R Q t ∈ hierarchy δ)
    (hγ : γ ∈ δ) (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      ∀ (H : Set A.Model) (hH : IsExternalForcingGeneric (A.ofName ⟨Q, h.posetName⟩)
          (A.ofName ⟨S, h.orderName⟩) H),
        IsRankDCThreshold ((TwoStepModel.iterandContext A h hH).check (A.check γ))
          ((TwoStepModel.iterandContext A h hH).check (A.check β)) := by
  obtain ⟨β, hβ, hγβ, hall⟩ := uniform_rankDCThreshold_all_generics hδ hC hγ
    (twoStep_preorder hR ht h) (twoStep_top hR ht h)
  refine ⟨β, hβ, hγβ, ?_⟩
  intro G hG
  dsimp only
  intro H hH
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  let C := TwoStepModel.combinedContext A h hH
  have hc : IsRankDCThreshold (C.check γ) (C.check β) := hall C.G C.generic
  have he := TwoStepModel.combined_check_eval A h hH rankDCThresholdFormula ![γ, β]
  have hv (f : V → C.Model) : (fun i ↦ f (![γ, β] i)) = ![f γ, f β] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [hv] at he
  have hw : (fun i ↦ (TwoStepModel.iterandContext A h hH).check (A.check (![γ, β] i))) =
      ![(TwoStepModel.iterandContext A h hH).check (A.check γ),
        (TwoStepModel.iterandContext A h hH).check (A.check β)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [hw] at he
  exact (show rankDCThresholdFormula.Evalb _ ↔ _ from by simp [A]).mp
    (he.mp ((show rankDCThresholdFormula.Evalb _ ↔ _ from by simp [A, C]).mpr hc))

end ZFVP
