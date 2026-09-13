import ZFVP.SetTheory.LevySubstitution

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaUnaryComposition (φ ψ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “y x. ∃ z, !ψ z x ∧ !φ y z”

def piUnaryComposition (φ ψ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “y x. ∀ z, !ψ z x → !φ y z”

theorem sigmaUnaryComposition_sigmaOne {φ ψ : SetTheorySemisentence 2}
    (hf : IsSigmaFormula 1 φ) (hg : IsSigmaFormula 1 ψ) :
    IsSigmaFormula 1 (sigmaUnaryComposition φ ψ) := .exs (.and (hg.subst _) (hf.subst _))

theorem piUnaryComposition_piOne {φ ψ : SetTheorySemisentence 2}
    (hf : IsPiFormula 1 φ) (hg : IsSigmaFormula 1 ψ) :
    IsPiFormula 1 (piUnaryComposition φ ψ) := .all (.or (hg.subst _).neg (hf.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaUnaryComposition_defined (F G : V → V) (φ ψ : SetTheorySemisentence 2)
    [ℒₛₑₜ-function₁ F via φ] [ℒₛₑₜ-function₁ G via ψ] :
    ℒₛₑₜ-function₁ (fun x ↦ F (G x)) via sigmaUnaryComposition φ ψ :=
  ⟨fun v ↦ by simp [sigmaUnaryComposition]⟩

instance piUnaryComposition_defined (F G : V → V) (φ ψ : SetTheorySemisentence 2)
    [ℒₛₑₜ-function₁ F via φ] [ℒₛₑₜ-function₁ G via ψ] :
    ℒₛₑₜ-function₁ (fun x ↦ F (G x)) via piUnaryComposition φ ψ :=
  ⟨fun v ↦ by simp [piUnaryComposition]⟩

end ZFVP
