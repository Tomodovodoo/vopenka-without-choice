import ZFVP.SetTheory.ChoicelessExtendible
import ZFVP.SetTheory.CnDeltaTwo

/-! A Sigma(n+1) formula for a single positive-level extendibility witness.
At n=1 the Sigma-two definition of C(1) is used explicitly. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def positiveCnWitnessFormula : ℕ → SetTheorySemisentence 1
  | 0 => sigmaTwoCnOneFormula
  | k + 1 => cnFormula (k + 2)

theorem positiveCnWitnessFormula_sigma (k : ℕ) :
    IsSigmaFormula (k + 2) (positiveCnWitnessFormula k) := by
  cases k with
  | zero => exact sigmaTwoCnOneFormula_sigmaTwo
  | succ k => exact (cnFormula_pi (k := k + 2) (by omega)).raise

def choicelessExtendibleWitnessBody (C : SetTheorySemisentence 1) : SetTheorySemisentence 3 :=
  “α γ μ. ∃ ν A B e κ y, !C ν ∧ !piOneHierarchyFormula A μ ∧ !piOneHierarchyFormula B ν ∧
    !piOneMembershipEmbeddingFormula A B e ∧ !boundedCriticalPointFormula A e κ ∧
    α ∈ κ ∧ !boundedPairMemberFormula e γ y ∧ μ ∈ y”

def positiveChoicelessExtendibleWitnessFormula (k : ℕ) : SetTheorySemisentence 3 :=
  choicelessExtendibleWitnessBody (positiveCnWitnessFormula k)

theorem positiveChoicelessExtendibleWitnessFormula_sigma (k : ℕ) :
    IsSigmaFormula (k + 2) (positiveChoicelessExtendibleWitnessFormula k) := by
  unfold positiveChoicelessExtendibleWitnessFormula choicelessExtendibleWitnessBody
  repeat' apply IsLevyFormula.exs
  exact .and ((positiveCnWitnessFormula_sigma k).subst _)
    (.and ((piOneHierarchyFormula_piOne.raise.mono (by omega)).subst _)
      (.and ((piOneHierarchyFormula_piOne.raise.mono (by omega)).subst _)
        (.and ((piOneMembershipEmbeddingFormula_piOne.raise.mono (by omega)).subst _)
          (.and (.bounded (boundedCriticalPointFormula_bounded.subst _))
            (.and (.bounded (.rel _ _))
              (.and (.bounded (boundedPairMemberFormula_bounded.subst _)) (.bounded (.rel _ _))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_positiveCnWitnessFormula (k : ℕ) (ν : V) :
    (positiveCnWitnessFormula k).Evalb ![ν] ↔ Cn (k + 1) ν := by
  cases k with
  | zero => exact eval_sigmaTwoCnOneFormula ν
  | succ k => exact eval_cnFormula (k + 2) ν

instance positiveCnWitnessFormula_defined (k : ℕ) :
    ℒₛₑₜ-predicate[V] (Cn (k + 1)) via positiveCnWitnessFormula k :=
  ⟨fun v ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change (positiveCnWitnessFormula k).Evalb v ↔ Cn (k + 1) (v 0)
    rw [← hv]
    exact eval_positiveCnWitnessFormula _ _⟩

def ChoicelessExtendibleWitness (n : ℕ) (α γ μ : V) : Prop :=
  IsOrdinal μ ∧ γ ∈ hierarchy μ ∧ ∃ ν e κ, Cn n ν ∧
    IsCodedMembershipEmbedding (hierarchy μ) (hierarchy ν) e ∧
    IsCriticalPoint (hierarchy μ) e κ ∧ α ∈ κ ∧ μ ∈ e ‘ γ

theorem eval_positiveChoicelessExtendibleWitnessFormula (k : ℕ) (α γ μ : V) :
    (positiveChoicelessExtendibleWitnessFormula k).Evalb ![α, γ, μ] ↔
      ChoicelessExtendibleWitness (k + 1) α γ μ := by
  simp [positiveChoicelessExtendibleWitnessFormula, choicelessExtendibleWitnessBody,
    ChoicelessExtendibleWitness]
  constructor
  · rintro ⟨ν, hν, A, ⟨hμ, rfl⟩, B, ⟨_, rfl⟩, e, he, κ, hc, hακ, y, hp, hμy⟩
    let := hμ
    let := hierarchy_transitive μ
    let := IsFunction.of_mem he.function
    refine ⟨hμ, (mem_of_mem_functions he.function hp).1, ν, hν, e, he, κ,
      (criticalPoint_iff_graphSpec he.function).mpr hc, hακ, ?_⟩
    rwa [value_eq_of_kpair_mem hp]
  · rintro ⟨hμ, hγ, ν, hν, e, he, κ, hc, hακ, hm⟩
    let := hμ
    let := hierarchy_transitive μ
    let := IsFunction.of_mem he.function
    refine ⟨ν, hν, hierarchy μ, ⟨hμ, rfl⟩, hierarchy ν, ⟨hν.ordinal, rfl⟩,
      e, he, κ, (criticalPoint_iff_graphSpec he.function).mp hc, hακ, e ‘ γ, ?_, hm⟩
    exact kpair_value_mem (by rw [domain_eq_of_mem_function he.function]; exact hγ)

instance positiveChoicelessExtendibleWitnessFormula_defined (k : ℕ) :
    ℒₛₑₜ-relation₃[V] (ChoicelessExtendibleWitness (k + 1)) via positiveChoicelessExtendibleWitnessFormula k :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) l) j) i
    change (positiveChoicelessExtendibleWitnessFormula k).Evalb v ↔
      ChoicelessExtendibleWitness (k + 1) (v 0) (v 1) (v 2)
    rw [← hv]
    exact eval_positiveChoicelessExtendibleWitnessFormula _ _ _ _⟩

theorem IsAlphaChoicelessExtendible.witness {n : ℕ} {α γ : V}
    (h : IsAlphaChoicelessExtendible n α γ) {μ : V} (hμ : Cn n μ) (hγμ : γ ∈ μ) :
    ChoicelessExtendibleWitness n α γ μ := by
  let := hμ.ordinal
  exact ⟨hμ.ordinal, ordinal_subset_hierarchy μ γ hγμ, h.2.2 μ hμ hγμ⟩

end ZFVP
