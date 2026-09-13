import ZFVP.SetTheory.SymmetryDictionary
import ZFVP.SetTheory.UniformFunctionOperations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def symmetricConverseFormula : SetTheorySemisentence 2 :=
  f“g f. ∀ p, p ∈ g ↔ p ∈ !prod.dfn (!range.dfn f) (!domain.dfn f) ∧
    !kpair.dfn (!kpair.π₂.dfn p) (!kpair.π₁.dfn p) ∈ f”

def symmetricAutomorphismFormula : SetTheorySemisentence 3 :=
  f“P R π. π ∈ !function.dfn P P ∧ !Injective.dfn π ∧ !range.dfn π = P ∧
    ∀ p ∈ P, ∀ q ∈ P, !kpair.dfn p q ∈ R ↔ !kpair.dfn (!value.dfn π p) (!value.dfn π q) ∈ R”

def symmetricGroupFormula : SetTheorySemisentence 3 :=
  f“P R Γ. (∀ π ∈ Γ, !symmetricAutomorphismFormula P R π) ∧ !identity.dfn P ∈ Γ ∧
    (∀ π ∈ Γ, ∀ ρ ∈ Γ, !composeFormula π ρ ∈ Γ) ∧ ∀ π ∈ Γ, !symmetricConverseFormula π ∈ Γ”

def symmetricSubgroupFormula : SetTheorySemisentence 3 :=
  f“P Γ H. H ⊆ Γ ∧ !identity.dfn P ∈ H ∧
    (∀ π ∈ H, ∀ ρ ∈ H, !composeFormula π ρ ∈ H) ∧ ∀ π ∈ H, !symmetricConverseFormula π ∈ H”

def symmetricConjugateFormula : SetTheorySemisentence 3 :=
  f“C π H. ∀ θ, θ ∈ C ↔ ∃ ρ ∈ H,
    θ = !composeFormula (!composeFormula (!symmetricConverseFormula π) ρ) π”

def symmetricNormalFilterFormula : SetTheorySemisentence 3 :=
  f“P Γ F. (∀ H ∈ F, !symmetricSubgroupFormula P Γ H) ∧ Γ ∈ F ∧
    (∀ H ∈ F, ∀ K, !symmetricSubgroupFormula P Γ K → H ⊆ K → K ∈ F) ∧
    (∀ H ∈ F, ∀ K ∈ F, !inter.dfn H K ∈ F) ∧
    ∀ π ∈ Γ, ∀ H ∈ F, !symmetricConjugateFormula π H ∈ F”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance symmetricConverseFormula_defined : ℒₛₑₜ-function₁[V] converseGraph via symmetricConverseFormula :=
  ⟨fun v ↦ by
    change symmetricConverseFormula.Evalb v ↔ v 0 = converseGraph (v 1)
    rw [mem_ext_iff]
    simp [symmetricConverseFormula, converseGraph]⟩
instance symmetricAutomorphismFormula_defined :
    ℒₛₑₜ-relation₃[V] IsForcingAutomorphism via symmetricAutomorphismFormula :=
  ⟨fun v ↦ by simp [symmetricAutomorphismFormula, IsForcingAutomorphism]⟩
instance symmetricGroupFormula_defined :
    ℒₛₑₜ-relation₃[V] IsForcingAutomorphismGroup via symmetricGroupFormula :=
  ⟨fun v ↦ by simp [symmetricGroupFormula, IsForcingAutomorphismGroup]⟩
instance symmetricSubgroupFormula_defined :
    ℒₛₑₜ-relation₃[V] IsForcingSubgroup via symmetricSubgroupFormula :=
  ⟨fun v ↦ by simp [symmetricSubgroupFormula, IsForcingSubgroup]⟩
instance symmetricConjugateFormula_defined :
    ℒₛₑₜ-function₂[V] conjugateSubgroup via symmetricConjugateFormula :=
  ⟨fun v ↦ by
    change symmetricConjugateFormula.Evalb v ↔ v 0 = conjugateSubgroup (v 1) (v 2)
    rw [mem_ext_iff]
    simp [symmetricConjugateFormula, conjugateSubgroup, repl_spec]⟩
instance symmetricNormalFilterFormula_defined :
    ℒₛₑₜ-relation₃[V] IsNormalSubgroupFilter via symmetricNormalFilterFormula :=
  ⟨fun v ↦ by simp [symmetricNormalFilterFormula, IsNormalSubgroupFilter]⟩

end ZFVP
