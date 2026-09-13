import ZFVP.SetTheory.DeltaOneThreadSplice
import ZFVP.SetTheory.DeltaOnePairProjections
import ZFVP.SetTheory.BoundedProduct
import ZFVP.SetTheory.ForcingLimitColumnDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneSplicePairRow : SetTheorySemisentence 6 :=
  “y a θ π L i. ∃ f, !sigmaOnePairFirstFormula f a ∧ ∃ b, !sigmaOnePairSecondFormula b a ∧
    !sigmaOneThreadSpliceFormula y θ π L f i b”

def piOneSplicePairRow : SetTheorySemisentence 6 :=
  “y a θ π L i. ∀ f, !sigmaOnePairFirstFormula f a → ∀ b, !sigmaOnePairSecondFormula b a →
    !piOneThreadSpliceFormula y θ π L f i b”

theorem sigmaOneSplicePairRow_sigmaOne : IsSigmaFormula 1 sigmaOneSplicePairRow :=
  .exs (.and (sigmaOnePairFirstFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOnePairSecondFormula_sigmaOne.subst _) (sigmaOneThreadSpliceFormula_sigmaOne.subst _))))

theorem piOneSplicePairRow_piOne : IsPiFormula 1 piOneSplicePairRow :=
  .all (.or (sigmaOnePairFirstFormula_sigmaOne.subst _).neg
    (.all (.or (sigmaOnePairSecondFormula_sigmaOne.subst _).neg (piOneThreadSpliceFormula_piOne.subst _))))

def sigmaOneLimitLiftFormula : SetTheorySemisentence 7 :=
  “G C A θ π L i. ∃ B, !boundedProductFormula B C A ∧
    !(graphAssemblyFormula sigmaOneSplicePairRow) G B θ π L i”

def piOneLimitLiftFormula : SetTheorySemisentence 7 :=
  “G C A θ π L i. ∀ B, !boundedProductFormula B C A →
    !(graphAssemblyFormula piOneSplicePairRow) G B θ π L i”

theorem sigmaOneLimitLiftFormula_sigmaOne : IsSigmaFormula 1 sigmaOneLimitLiftFormula :=
  .exs (.and (.bounded (boundedProductFormula_bounded.subst _))
    ((graphAssemblyFormula_levy sigmaOneSplicePairRow_sigmaOne).subst _))

theorem piOneLimitLiftFormula_piOne : IsPiFormula 1 piOneLimitLiftFormula :=
  .all (.or (.bounded (boundedProductFormula_bounded.subst _).neg)
    ((graphAssemblyFormula_levy piOneSplicePairRow_piOne).subst _))

def sigmaOneLimitLiftRow : SetTheorySemisentence 7 :=
  “y i C θ P π L. ∃ A, !boundedValueFormula A P i ∧ !sigmaOneLimitLiftFormula y C A θ π L i”

def piOneLimitLiftRow : SetTheorySemisentence 7 :=
  “y i C θ P π L. ∀ A, !boundedValueFormula A P i → !piOneLimitLiftFormula y C A θ π L i”

theorem sigmaOneLimitLiftRow_sigmaOne : IsSigmaFormula 1 sigmaOneLimitLiftRow :=
  .exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (sigmaOneLimitLiftFormula_sigmaOne.subst _))

theorem piOneLimitLiftRow_piOne : IsPiFormula 1 piOneLimitLiftRow :=
  .all (.or (.bounded (boundedValueFormula_bounded.subst _).neg) (piOneLimitLiftFormula_piOne.subst _))

def sigmaOneLimitLiftColumnFormula : SetTheorySemisentence 6 :=
  “G C θ P π L. !(graphAssemblyFormula sigmaOneLimitLiftRow) G θ C θ P π L”

def piOneLimitLiftColumnFormula : SetTheorySemisentence 6 :=
  “G C θ P π L. !(graphAssemblyFormula piOneLimitLiftRow) G θ C θ P π L”

theorem sigmaOneLimitLiftColumnFormula_sigmaOne : IsSigmaFormula 1 sigmaOneLimitLiftColumnFormula :=
  (graphAssemblyFormula_levy sigmaOneLimitLiftRow_sigmaOne).subst _

theorem piOneLimitLiftColumnFormula_piOne : IsPiFormula 1 piOneLimitLiftColumnFormula :=
  (graphAssemblyFormula_levy piOneLimitLiftRow_piOne).subst _

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneSplicePairRow_defined : Defined
    (fun v : Fin 6 → V ↦ v 0 = forcingThreadSplicePair (v 2) (v 3) (v 4) (v 5) (v 1))
    sigmaOneSplicePairRow :=
  ⟨fun v ↦ by simp [sigmaOneSplicePairRow, forcingThreadSplicePair]⟩

instance piOneSplicePairRow_defined : Defined
    (fun v : Fin 6 → V ↦ v 0 = forcingThreadSplicePair (v 2) (v 3) (v 4) (v 5) (v 1))
    piOneSplicePairRow :=
  ⟨fun v ↦ by simp [piOneSplicePairRow, forcingThreadSplicePair]⟩

theorem eval_splicePairRow_graph {φ : SetTheorySemisentence 6}
    [Defined (fun v : Fin 6 → V ↦ v 0 = forcingThreadSplicePair (v 2) (v 3) (v 4) (v 5) (v 1)) φ]
    (G C A θ π L i : V) :
    (graphAssemblyFormula φ).Evalb ![G, C ×ˢ A, θ, π, L, i] ↔ G = forcingLimitLift C A θ π L i := by
  exact eval_graphAssemblyFormula φ G (C ×ˢ A) ![θ, π, L, i]
    (fun z ↦ forcingThreadSplice θ π L (kpair.π₁ z) i (kpair.π₂ z)) _
    (fun a _ y ↦ by simp [forcingThreadSplicePair])

instance sigmaOneLimitLiftFormula_defined : Defined
    (fun v : Fin 7 → V ↦ v 0 = forcingLimitLift (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    sigmaOneLimitLiftFormula :=
  ⟨fun v ↦ by
    have he := eval_splicePairRow_graph (φ := sigmaOneSplicePairRow)
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
    simp only [Semiformula.Evalb] at he
    simpa [sigmaOneLimitLiftFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def] using he⟩

instance piOneLimitLiftFormula_defined : Defined
    (fun v : Fin 7 → V ↦ v 0 = forcingLimitLift (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    piOneLimitLiftFormula :=
  ⟨fun v ↦ by
    have he := eval_splicePairRow_graph (φ := piOneSplicePairRow)
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
    simp only [Semiformula.Evalb] at he
    simpa [piOneLimitLiftFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def] using he⟩

instance sigmaOneLimitLiftRow_defined : Defined
    (fun v : Fin 7 → V ↦ v 0 = forcingLimitLift (v 2) ((v 4) ‘ (v 1)) (v 3) (v 5) (v 6) (v 1))
    sigmaOneLimitLiftRow := ⟨fun v ↦ by simp [sigmaOneLimitLiftRow]⟩

instance piOneLimitLiftRow_defined : Defined
    (fun v : Fin 7 → V ↦ v 0 = forcingLimitLift (v 2) ((v 4) ‘ (v 1)) (v 3) (v 5) (v 6) (v 1))
    piOneLimitLiftRow := ⟨fun v ↦ by simp [piOneLimitLiftRow]⟩

theorem eval_limitLiftRow_graph {φ : SetTheorySemisentence 7}
    [Defined (fun v : Fin 7 → V ↦ v 0 = forcingLimitLift (v 2) ((v 4) ‘ (v 1)) (v 3) (v 5) (v 6) (v 1)) φ]
    (G C θ P π L : V) :
    (graphAssemblyFormula φ).Evalb ![G, θ, C, θ, P, π, L] ↔ G = forcingLimitLiftColumn C θ P π L := by
  exact eval_graphAssemblyFormula φ G θ ![C, θ, P, π, L]
    (fun i ↦ forcingLimitLift C (P ‘ i) θ π L i) _ (fun i _ y ↦ by simp)

instance sigmaOneLimitLiftColumnFormula_defined :
    ℒₛₑₜ-function₅[V] forcingLimitLiftColumn via sigmaOneLimitLiftColumnFormula :=
  ⟨fun v ↦ by
    have he := eval_limitLiftRow_graph (φ := sigmaOneLimitLiftRow)
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
    simp only [Semiformula.Evalb] at he
    simpa [sigmaOneLimitLiftColumnFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def] using he⟩

instance piOneLimitLiftColumnFormula_defined :
    ℒₛₑₜ-function₅[V] forcingLimitLiftColumn via piOneLimitLiftColumnFormula :=
  ⟨fun v ↦ by
    have he := eval_limitLiftRow_graph (φ := piOneLimitLiftRow)
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
    simp only [Semiformula.Evalb] at he
    simpa [piOneLimitLiftColumnFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def] using he⟩

end ZFVP
