import ZFVP.ModelTheory.TwoStepQuotient

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem ElementaryMap.evalb_iff {W : Type*} [SetStructure W] (j : ElementaryMap V W)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) :
    φ.Evalb v ↔ φ.Evalb (fun i ↦ j (v i)) := by
  have hf : j ∘ (Empty.elim : Empty → V) = (Empty.elim : Empty → W) := by
    funext x
    exact Empty.elim x
  have he := j.elementary φ v Empty.elim
  rw [hf] at he
  exact he

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)
  {H : Set A.Model}
  (hH : IsExternalForcingGeneric (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) H)

theorem combined_check_eval {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) :
    φ.Evalb (fun i ↦ (combinedContext A h hH).check (v i)) ↔
      φ.Evalb (fun i ↦ (iterandContext A h hH).check (A.check (v i))) := by
  have he := (combinedElementaryMap A h hH).evalb_iff φ
    (fun i ↦ (combinedContext A h hH).check (v i))
  have hv : (fun i ↦ combinedElementaryMap A h hH ((combinedContext A h hH).check (v i))) =
      (fun i ↦ (iterandContext A h hH).check (A.check (v i))) := by
    funext i
    exact combinedEquiv_check A h hH (v i)
  rw [hv] at he
  exact he

end TwoStepModel

theorem twoStep_check_eval {P R Q S t one : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t) {G : Set V}
    (hG : IsExternalForcingGeneric (twoStepConditions P R Q t) (twoStepOrder P R Q S t) G)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) :
    φ.Evalb (fun i ↦ (twoStepTotalContext hR htop h hG).check (v i)) ↔
      φ.Evalb (fun i ↦ (twoStepSecondContext hR htop h hG).check
        ((twoStepFirstContext hR htop h hG).check (v i))) := by
  have he := (twoStepQuotientElementaryMap hR htop h hG).evalb_iff φ
    (fun i ↦ (twoStepTotalContext hR htop h hG).check (v i))
  have hv : (fun i ↦ twoStepQuotientElementaryMap hR htop h hG
      ((twoStepTotalContext hR htop h hG).check (v i))) =
      (fun i ↦ (twoStepSecondContext hR htop h hG).check
        ((twoStepFirstContext hR htop h hG).check (v i))) := by
    funext i
    exact twoStepQuotientEquiv_check hR htop h hG (v i)
  rw [hv] at he
  exact he

theorem twoStep_all_checked_iff_successive {P R Q S t one : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) :
    (∀ (G : Set V) (hG : IsExternalForcingGeneric (twoStepConditions P R Q t)
        (twoStepOrder P R Q S t) G),
      φ.Evalb (fun i ↦ (twoStepTotalContext hR htop h hG).check (v i))) ↔
    (∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
      ∀ (H : Set A.Model) (hH : IsExternalForcingGeneric (A.ofName ⟨Q, h.posetName⟩)
          (A.ofName ⟨S, h.orderName⟩) H),
        φ.Evalb (fun i ↦ (TwoStepModel.iterandContext A h hH).check (A.check (v i)))) := by
  constructor
  · intro hall G hG
    dsimp only
    intro H hH
    let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    apply (TwoStepModel.combined_check_eval A h hH φ v).mp
    exact hall _ (TwoStepModel.combined_generic A h hH)
  · intro hall G hG
    let A := twoStepFirstContext hR htop h hG
    apply (twoStep_check_eval hR htop h hG φ v).mpr
    exact hall A.G A.generic _ (TwoStepModel.second_generic A h hG rfl)

end ZFVP
