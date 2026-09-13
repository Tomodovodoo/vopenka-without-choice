import ZFVP.ModelTheory.ForcingFunctionValues

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingFormula_of_all_generics [Countable V] {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName P)
    (htruth : ∀ G : Set V, ∀ hG : IsExternalForcingGeneric P R G, p ∈ G →
      φ.Evalb (fun i ↦ (ForcingContext.mk P R one G hR htop hG).ofName (v i))) :
    p ∈ forcingFormula P R φ (standardTuple (fun i ↦ (v i).val)) := by
  apply (forcingFormula_regular hR φ _).2.2 p hp
  intro q hq hqp
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  have hpG := hG.1.2.2.1 q hqG p hp hqp
  let S : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  obtain ⟨r, hrG, hr⟩ := (S.formula_truth φ v).mp (htruth G hG hpG)
  obtain ⟨s, hsG, hsr, hsq⟩ := hG.1.2.2.2 r hrG q hqG
  exact ⟨s, (forcingFormula_regular hR φ _).2.1 r hr s (hG.1.1 s hsG) hsr, hsq⟩

theorem forcingFormula_iff_all_generics [Countable V] {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName P) :
    p ∈ forcingFormula P R φ (standardTuple (fun i ↦ (v i).val)) ↔
      ∀ G : Set V, ∀ hG : IsExternalForcingGeneric P R G, p ∈ G →
        φ.Evalb (fun i ↦ (ForcingContext.mk P R one G hR htop hG).ofName (v i)) := by
  constructor
  · intro h G hG hpG
    exact ((ForcingContext.mk P R one G hR htop hG).formula_truth φ v).mpr ⟨p, hpG, h⟩
  · exact forcingFormula_of_all_generics hR htop hp φ v

end ZFVP
