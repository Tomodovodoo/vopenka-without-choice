import ZFVP.SetTheory.FiniteDictionaryReflection
import ZFVP.SetTheory.SourceQuantifierBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Maximum ell over a finite list of expanded formulas. For the empty list
the source convention uses zero. Subformulas and negations do not increase q. -/
def sourceDictionaryEll : List (SetTheorySemisentence 6) → ℕ
  | [] => 0
  | φ :: D => max (sourceQuantifierCount φ + 1) (sourceDictionaryEll D)

def sourceDictionaryLevel (D : List (SetTheorySemisentence 6)) : ℕ :=
  2 + sourceDictionaryEll D

def sourceReflectionLevel (D : List (SetTheorySemisentence 6)) : ℕ :=
  2 + max (sourceDictionaryLevel D)
    (sourceQuantifierCount (reflectionFormula (sourceDictionaryLevel D) D) + 1)

theorem sourceDictionaryEll_mem {D : List (SetTheorySemisentence 6)} {φ : SetTheorySemisentence 6}
    (hφ : φ ∈ D) : sourceQuantifierCount φ + 1 ≤ sourceDictionaryEll D := by
  induction D with
  | nil => exact (List.not_mem_nil hφ).elim
  | cons ψ D ih =>
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact Nat.le_max_left _ _
    · exact (ih hφ).trans (Nat.le_max_right _ _)

theorem sourceDictionaryLevel_positive (D : List (SetTheorySemisentence 6)) :
    2 ≤ sourceDictionaryLevel D := by unfold sourceDictionaryLevel; omega

theorem sourceDictionary_formula_complexity {D : List (SetTheorySemisentence 6)}
    {φ : SetTheorySemisentence 6} (hφ : φ ∈ D) (p : LevyPolarity) :
    IsLevyFormula p (sourceDictionaryLevel D) φ :=
  (isLevyFormula_sourceQuantifierCount φ p).mono
    ((sourceDictionaryEll_mem hφ).trans (by unfold sourceDictionaryLevel; omega))

theorem sourceReflectionLevel_positive (D : List (SetTheorySemisentence 6)) :
    2 ≤ sourceReflectionLevel D := by unfold sourceReflectionLevel; omega

theorem sourceReflection_formula_complexity (D : List (SetTheorySemisentence 6)) (p : LevyPolarity) :
    IsLevyFormula p (sourceReflectionLevel D) (reflectionFormula (sourceDictionaryLevel D) D) :=
  (isLevyFormula_sourceQuantifierCount _ p).mono (by unfold sourceReflectionLevel; omega)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem finite_reflection_source (D : List (SetTheorySemisentence 6)) {S : ℕ}
    (hS : sourceReflectionLevel D ≤ S) {η δ θ ρ α x : V}
    (hδ : IsCnExtendible S δ) (hρ : Cn (sourceDictionaryLevel D) ρ)
    (hηδ : η ∈ δ) (hδθ : δ ∈ θ) (hθρ : ordinalAdd θ (ω : V) ∈ ρ)
    (hαθ : α ∈ θ) (hx : x ∈ hierarchy ρ)
    (hDtrue : ∀ e ∈ D, e.Evalb ![η, δ, θ, ρ, α, x]) :
    Reflects (sourceDictionaryLevel D) D ![η, δ, θ, ρ, α, x] := by
  have hp := Nat.le_trans (sourceReflectionLevel_positive D) hS
  obtain ⟨k, rfl⟩ : ∃ k, S = k + 1 := ⟨S - 1, by omega⟩
  exact finite_reflection_of_complexity D ((sourceReflection_formula_complexity D .sigma).mono hS)
    hδ hρ hηδ hδθ hθρ hαθ hx hDtrue

end ZFVP
