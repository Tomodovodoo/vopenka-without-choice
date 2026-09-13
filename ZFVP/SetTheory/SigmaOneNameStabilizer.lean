import ZFVP.SetTheory.DeltaOneNameAction
import ZFVP.SetTheory.SymmetricSystems

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneNameStabilizerFormula : SetTheorySemisentence 4 :=
  “P Γ τ H. !isSubsetOf H Γ ∧ ∀ π ∈ Γ,
    (π ∈ H ∧ !(sigmaOneNameActionFormula true) P π τ τ) ∨
    (π ∉ H ∧ !(sigmaOneNameActionFormula false) P π τ τ)”

theorem sigmaOneNameStabilizerFormula_sigmaOne : IsSigmaFormula 1 sigmaOneNameStabilizerFormula :=
  .and (.bounded (isSubsetOf_bounded.subst _)) (.boundedAll (.bvar 1)
    (.or (.and (.bounded (.rel _ _)) ((sigmaOneNameActionFormula_sigmaOne true).subst _))
      (.and (.bounded (.nrel _ _)) ((sigmaOneNameActionFormula_sigmaOne false).subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneNameStabilizerFormula {P Γ τ : V}
    (hΓ : ∀ π ∈ Γ, π ∈ P ^ P) (hτ : IsForcingName P τ) (H : V) :
    sigmaOneNameStabilizerFormula.Evalb ![P, Γ, τ, H] ↔ H = nameStabilizer Γ τ := by
  have he (π : V) (hπ : π ∈ Γ) (a : Bool) := eval_sigmaOneNameActionFormula (hΓ π hπ) hτ a τ
  simp only [sigmaOneNameStabilizerFormula]
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  simp +contextual only [he, TruthAnswer, Bool.false_eq_true, reduceIte]
  constructor
  · rintro ⟨hsub, h⟩
    apply mem_ext
    intro π
    simp only [nameStabilizer, mem_sep_iff]
    constructor
    · intro hπ
      have hπΓ := hsub π hπ
      exact ⟨hπΓ, ((h π hπΓ).resolve_right (fun hh ↦ hh.1 hπ)).2.symm⟩
    · rintro ⟨hπΓ, heq⟩
      exact ((h π hπΓ).resolve_right (fun hh ↦ hh.2 heq.symm)).1
  · rintro rfl
    constructor
    · intro π hπ
      exact (mem_sep_iff.mp hπ).1
    · intro π hπ
      by_cases heq : τ = nameAction π τ
      · exact Or.inl ⟨mem_sep_iff.mpr ⟨hπ, heq.symm⟩, heq⟩
      · exact Or.inr ⟨fun h ↦ heq (mem_sep_iff.mp h).2.symm, heq⟩

end ZFVP
