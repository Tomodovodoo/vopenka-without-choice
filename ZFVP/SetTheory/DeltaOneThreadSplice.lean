import ZFVP.SetTheory.LevyGraphAssembly
import ZFVP.SetTheory.BoundedValue
import ZFVP.SetTheory.ForcingThreadSplice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def spliceValueTestFormula : SetTheorySemisentence 7 :=
  “y j i b q c d. (j ∈ i ∧ !boundedValueFormula y c b) ∨
    (j ∉ i ∧ !boundedValueFormula y d q)”

theorem spliceValueTestFormula_bounded : IsBoundedSetFormula spliceValueTestFormula :=
  .or (.and (.rel _ _) (boundedValueFormula_bounded.subst _))
    (.and (.nrel _ _) (boundedValueFormula_bounded.subst _))

def sigmaOneSpliceValueFormula : SetTheorySemisentence 7 :=
  “y j π L f i b. ∃ a, !boundedKpairFormula a j i ∧
    ∃ t, !boundedKpairFormula t i j ∧
    ∃ c, !boundedValueFormula c π a ∧
    ∃ d, !boundedValueFormula d L t ∧
    ∃ e, !boundedValueFormula e f j ∧
    ∃ q, !boundedKpairFormula q e b ∧
    !spliceValueTestFormula y j i b q c d”

theorem sigmaOneSpliceValueFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSpliceValueFormula :=
  (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
    (.bounded (spliceValueTestFormula_bounded.subst _))))))))))))))

def sigmaOneThreadSpliceFormula : SetTheorySemisentence 7 := graphAssemblyFormula sigmaOneSpliceValueFormula

theorem sigmaOneThreadSpliceFormula_sigmaOne : IsSigmaFormula 1 sigmaOneThreadSpliceFormula :=
  graphAssemblyFormula_levy sigmaOneSpliceValueFormula_sigmaOne

def piOneSpliceValueFormula : SetTheorySemisentence 7 :=
  “y j π L f i b. ∀ a, !boundedKpairFormula a j i →
    ∀ t, !boundedKpairFormula t i j →
    ∀ c, !boundedValueFormula c π a →
    ∀ d, !boundedValueFormula d L t →
    ∀ e, !boundedValueFormula e f j →
    ∀ q, !boundedKpairFormula q e b →
    !spliceValueTestFormula y j i b q c d”

theorem piOneSpliceValueFormula_piOne : IsPiFormula 1 piOneSpliceValueFormula :=
  (.all (.or (.bounded (boundedKpairFormula_bounded.subst _).neg)
    (.all (.or (.bounded (boundedKpairFormula_bounded.subst _).neg)
    (.all (.or (.bounded (boundedValueFormula_bounded.subst _).neg)
    (.all (.or (.bounded (boundedValueFormula_bounded.subst _).neg)
    (.all (.or (.bounded (boundedValueFormula_bounded.subst _).neg)
    (.all (.or (.bounded (boundedKpairFormula_bounded.subst _).neg)
    (.bounded (spliceValueTestFormula_bounded.subst _))))))))))))))

def piOneThreadSpliceFormula : SetTheorySemisentence 7 := graphAssemblyFormula piOneSpliceValueFormula

theorem piOneThreadSpliceFormula_piOne : IsPiFormula 1 piOneThreadSpliceFormula :=
  graphAssemblyFormula_levy piOneSpliceValueFormula_piOne

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneSpliceValueFormula_defined : Defined
    (fun v : Fin 7 → V ↦ v 0 = forcingSpliceValue (v 2) (v 3) (v 4) (v 5) (v 6) (v 1))
    sigmaOneSpliceValueFormula :=
  ⟨fun v ↦ by
    classical
    by_cases h : v 1 ∈ v 5 <;>
      simp [sigmaOneSpliceValueFormula, spliceValueTestFormula, forcingSpliceValue, h]⟩

theorem eval_sigmaOneThreadSpliceFormula (G θ π L f i b : V) :
    sigmaOneThreadSpliceFormula.Evalb ![G, θ, π, L, f, i, b] ↔ G = forcingThreadSplice θ π L f i b := by
  exact eval_graphAssemblyFormula sigmaOneSpliceValueFormula G θ ![π, L, f, i, b]
    (forcingSpliceValue π L f i b) _ (fun j _ y ↦ by simp)

instance sigmaOneThreadSpliceFormula_defined : Defined
    (fun v : Fin 7 → V ↦ v 0 = forcingThreadSplice (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    sigmaOneThreadSpliceFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ sigmaOneThreadSpliceFormula.Evalb w) hv)).trans
      (eval_sigmaOneThreadSpliceFormula (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))⟩

instance piOneSpliceValueFormula_defined : Defined
    (fun v : Fin 7 → V ↦ v 0 = forcingSpliceValue (v 2) (v 3) (v 4) (v 5) (v 6) (v 1))
    piOneSpliceValueFormula :=
  ⟨fun v ↦ by
    classical
    by_cases h : v 1 ∈ v 5 <;>
      simp [piOneSpliceValueFormula, spliceValueTestFormula, forcingSpliceValue, h]⟩

theorem eval_piOneThreadSpliceFormula (G θ π L f i b : V) :
    piOneThreadSpliceFormula.Evalb ![G, θ, π, L, f, i, b] ↔ G = forcingThreadSplice θ π L f i b := by
  exact eval_graphAssemblyFormula piOneSpliceValueFormula G θ ![π, L, f, i, b]
    (forcingSpliceValue π L f i b) _ (fun j _ y ↦ by simp)

instance piOneThreadSpliceFormula_defined : Defined
    (fun v : Fin 7 → V ↦ v 0 = forcingThreadSplice (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    piOneThreadSpliceFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ piOneThreadSpliceFormula.Evalb w) hv)).trans
      (eval_piOneThreadSpliceFormula (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))⟩

end ZFVP
