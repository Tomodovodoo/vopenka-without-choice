import ZFVP.ModelTheory.ForcingEntailment

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingFormula_iff_under {n : ℕ} (φ ψ χ : SetTheorySemisentence n)
    (hvalid : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ v : Fin n → W, φ.Evalb v → (ψ.Evalb v ↔ χ.Evalb v))
    {P R one p : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hp : p ∈ P) (v : Fin n → ForcingName P)
    (hφ : p ∈ forcingFormula P R φ (standardTuple (fun i ↦ (v i).val))) :
    p ∈ forcingFormula P R ψ (standardTuple (fun i ↦ (v i).val)) ↔
      p ∈ forcingFormula P R χ (standardTuple (fun i ↦ (v i).val)) := by
  constructor
  · intro hψ
    apply forcingFormula_entailment (φ.and ψ) χ (by
      intro W _ _ _ b hb
      change φ.Evalb b ∧ ψ.Evalb b at hb
      exact (hvalid W b hb.1).mp hb.2) hR htop hp v
    rw [forcingFormula_and, mem_inter_iff]
    exact ⟨hφ, hψ⟩
  · intro hχ
    apply forcingFormula_entailment (φ.and χ) ψ (by
      intro W _ _ _ b hb
      change φ.Evalb b ∧ χ.Evalb b at hb
      exact (hvalid W b hb.1).mpr hb.2) hR htop hp v
    rw [forcingFormula_and, mem_inter_iff]
    exact ⟨hφ, hχ⟩

end ZFVP
