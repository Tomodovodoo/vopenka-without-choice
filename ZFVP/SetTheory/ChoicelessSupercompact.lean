import ZFVP.SetTheory.ChoicelessExtendible
import ZFVP.SetTheory.CnSandwich

/-! The alpha-relative choiceless supercompactness witnesses of
Mohammd's Definition 2.3. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def choicelessSupercompactWitnessFormula (n : ℕ) : SetTheorySemisentence 4 :=
  “α γ μ a. ∃ ν A B x e κ,
    ν ∈ γ ∧ !(cnFormula n) ν ∧ !piOneHierarchyFormula A ν ∧ !piOneHierarchyFormula B μ ∧
    x ∈ A ∧ !piOneMembershipEmbeddingFormula A B e ∧ !boundedCriticalPointFormula A e κ ∧
    α ∈ κ ∧ !boundedPairMemberFormula e x a”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ChoicelessSupercompactWitness (n : ℕ) (α γ μ a : V) : Prop :=
  IsOrdinal μ ∧ ∃ ν x e κ, ν ∈ γ ∧ Cn n ν ∧ x ∈ hierarchy ν ∧
    IsCodedMembershipEmbedding (hierarchy ν) (hierarchy μ) e ∧
    IsCriticalPoint (hierarchy ν) e κ ∧ α ∈ κ ∧ e ‘ x = a

theorem eval_choicelessSupercompactWitnessFormula (n : ℕ) (α γ μ a : V) :
    (choicelessSupercompactWitnessFormula n).Evalb ![α, γ, μ, a] ↔
      ChoicelessSupercompactWitness n α γ μ a := by
  simp [choicelessSupercompactWitnessFormula, ChoicelessSupercompactWitness]
  constructor
  · rintro ⟨ν, hνγ, hν, A, ⟨hνo, rfl⟩, B, ⟨hμ, rfl⟩, x, hx, e, he, κ, hκ, hακ, hp⟩
    let := hνo
    let := hierarchy_transitive ν
    let := IsFunction.of_mem he.function
    exact ⟨hμ, ν, hνγ, hν, x, hx, e, he, κ,
      (criticalPoint_iff_graphSpec he.function).mpr hκ, hακ, value_eq_of_kpair_mem hp⟩
  · rintro ⟨hμ, ν, hνγ, hν, x, hx, e, he, κ, hκ, hακ, hv⟩
    let := hν.ordinal
    let := hierarchy_transitive ν
    let := IsFunction.of_mem he.function
    refine ⟨ν, hνγ, hν, hierarchy ν, ⟨hν.ordinal, rfl⟩,
      hierarchy μ, ⟨hμ, rfl⟩, x, hx, e, he, κ,
      (criticalPoint_iff_graphSpec he.function).mp hκ, hακ, ?_⟩
    apply kpair_mem_iff_value.mpr
    exact ⟨by rw [domain_eq_of_mem_function he.function]; exact hx, hv⟩

instance choicelessSupercompactWitnessFormula_defined (n : ℕ) :
    ℒₛₑₜ-relation₄[V] (ChoicelessSupercompactWitness n) via choicelessSupercompactWitnessFormula n :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1, v 2, v 3] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
        (fun l ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) l) k) j) i
    change (choicelessSupercompactWitnessFormula n).Evalb v ↔
      ChoicelessSupercompactWitness n (v 0) (v 1) (v 2) (v 3)
    rw [← hv]
    exact eval_choicelessSupercompactWitnessFormula _ _ _ _ _⟩

instance choicelessSupercompactWitness_definable (n : ℕ) :
    ℒₛₑₜ-relation₄[V] (ChoicelessSupercompactWitness n) :=
  (choicelessSupercompactWitnessFormula_defined n).to_definable

def alphaChoicelessSupercompactFormula (n : ℕ) : SetTheorySemisentence 2 :=
  f“α γ. !IsOrdinal.dfn γ ∧ α ∈ γ ∧ ∀ μ, !(cnFormula n) μ → γ ∈ μ →
    ∀ a ∈ !hierarchyFormula μ, !(choicelessSupercompactWitnessFormula n) α γ μ a”

def IsAlphaChoicelessSupercompact (n : ℕ) (α γ : V) : Prop :=
  IsOrdinal γ ∧ α ∈ γ ∧ ∀ μ, Cn n μ → γ ∈ μ → ∀ a ∈ hierarchy μ,
    ChoicelessSupercompactWitness n α γ μ a

theorem eval_alphaChoicelessSupercompactFormula (n : ℕ) (α γ : V) :
    (alphaChoicelessSupercompactFormula n).Evalb ![α, γ] ↔ IsAlphaChoicelessSupercompact n α γ := by
  simp [alphaChoicelessSupercompactFormula, IsAlphaChoicelessSupercompact]

instance alphaChoicelessSupercompactFormula_defined (n : ℕ) :
    ℒₛₑₜ-relation[V] (IsAlphaChoicelessSupercompact n) via alphaChoicelessSupercompactFormula n :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    change (alphaChoicelessSupercompactFormula n).Evalb v ↔ IsAlphaChoicelessSupercompact n (v 0) (v 1)
    rw [← hv]
    exact eval_alphaChoicelessSupercompactFormula _ _ _⟩

instance alphaChoicelessSupercompact_definable (n : ℕ) :
    ℒₛₑₜ-relation[V] (IsAlphaChoicelessSupercompact n) :=
  (alphaChoicelessSupercompactFormula_defined n).to_definable

end ZFVP
