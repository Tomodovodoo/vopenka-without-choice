import ZFVP.SetTheory.ChoicelessSupercompactInterpolation
import ZFVP.SetTheory.ChoicelessSupercompactAbsoluteness

/-! Reading bounded choiceless supercompactness in correct rank stages. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def choicelessSupercompactBelowFormula (n : ℕ) : SetTheorySemisentence 3 :=
  “α κ δ. ∀ μ, !(cnFormula n) μ → κ ∈ μ → μ ∈ δ →
    ∀ A, !piOneHierarchyFormula A μ → ∀ a ∈ A,
      !(choicelessSupercompactWitnessFormula n) α κ μ a”

theorem eval_choicelessSupercompactBelow_components {W : Type*} [SetStructure W]
    (n : ℕ) (α κ δ : W) :
    (choicelessSupercompactBelowFormula n).Evalb ![α, κ, δ] ↔
      ∀ μ : W, (cnFormula n).Evalb ![μ] → κ ∈ μ → μ ∈ δ →
        ∀ A : W, piOneHierarchyFormula.Evalb ![A, μ] → ∀ a ∈ A,
          (choicelessSupercompactWitnessFormula n).Evalb ![α, κ, μ, a] := by
  simp [choicelessSupercompactBelowFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_choicelessSupercompactBelowFormula (n : ℕ) (α κ δ : V) :
    (choicelessSupercompactBelowFormula n).Evalb ![α, κ, δ] ↔
      ChoicelessSupercompactBelow n α κ δ := by
  rw [eval_choicelessSupercompactBelow_components]
  simp only [eval_cnFormula, eval_piOneHierarchyFormula,
    eval_choicelessSupercompactWitnessFormula]
  constructor
  · intro h μ hμ hκμ hμδ a ha
    exact h μ hμ hκμ hμδ (hierarchy μ) ⟨hμ.ordinal, rfl⟩ a ha
  · intro h μ hμ hκμ hμδ A hA a ha
    exact h μ hμ hκμ hμδ a (hA.2 ▸ ha)

instance choicelessSupercompactBelowFormula_defined (n : ℕ) :
    ℒₛₑₜ-relation₃[V] (ChoicelessSupercompactBelow n) via choicelessSupercompactBelowFormula n :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl
        (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
    change (choicelessSupercompactBelowFormula n).Evalb v ↔
      ChoicelessSupercompactBelow n (v 0) (v 1) (v 2)
    rw [← hv]
    exact eval_choicelessSupercompactBelowFormula _ _ _ _⟩

instance choicelessSupercompactBelow_definable (n : ℕ) :
    ℒₛₑₜ-relation₃[V] (ChoicelessSupercompactBelow n) :=
  (choicelessSupercompactBelowFormula_defined n).to_definable

theorem Cn.supercompactBelow_of_eval {n : ℕ} {θ : V} (hθ : Cn (n + 1) θ)
    (α κ δ : SetDomain (hierarchy θ))
    (h : (choicelessSupercompactBelowFormula (n + 2)).Evalb ![α, κ, δ]) :
    ChoicelessSupercompactBelow (n + 2) α.val κ.val δ.val := by
  let := hθ.ordinal
  let := hierarchy_transitive θ
  intro μ hμ hκμ hμδ a ha
  let := hμ.ordinal
  have hμV := (hierarchy_transitive θ).mem_trans hμδ δ.property
  have hA := hθ.hierarchy_closed hμ.ordinal hμV
  have haV := (hierarchy_transitive θ).mem_trans ha hA
  let m : SetDomain (hierarchy θ) := ⟨μ, hμV⟩
  let A : SetDomain (hierarchy θ) := ⟨hierarchy μ, hA⟩
  let aa : SetDomain (hierarchy θ) := ⟨a, haV⟩
  have he := ((eval_choicelessSupercompactBelow_components _ α κ δ).mp h) m
    (hμ.into_lower_rank hθ (ordinal_mem_hierarchy_iff.mp hμV)) hκμ hμδ A
    ((hθ.hierarchy_formula_correct A m).mpr ⟨hμ.ordinal, rfl⟩) aa ha
  exact (hθ.choicelessSupercompactWitness_absolute α κ m aa hμ hκμ).mp he

theorem Cn.supercompactBelow_into_rank {n : ℕ} {θ : V} (hθ : Cn (n + 2) θ)
    (α κ δ : SetDomain (hierarchy θ))
    (h : ChoicelessSupercompactBelow (n + 2) α.val κ.val δ.val) :
    (choicelessSupercompactBelowFormula (n + 2)).Evalb ![α, κ, δ] := by
  apply (eval_choicelessSupercompactBelow_components _ α κ δ).mpr
  intro μ hμ hκμ hμδ A hA a ha
  have hμ' := (hθ.formula_absolute (by omega : max 2 (n + 2) ≤ n + 2) μ).mp hμ
  have hA' := (hθ.hierarchy_formula_correct A μ).mp hA
  have ha' : a.val ∈ hierarchy μ.val := hA'.2 ▸ ha
  exact ((hθ.of_le (by omega : n + 1 ≤ n + 2)).choicelessSupercompactWitness_absolute
    α κ μ a hμ' hκμ).mpr (h μ.val hμ' hκμ hμδ a.val ha')

theorem Cn.supercompactBelow_absolute {n : ℕ} {θ : V} (hθ : Cn (n + 2) θ)
    (α κ δ : SetDomain (hierarchy θ)) :
    (choicelessSupercompactBelowFormula (n + 2)).Evalb ![α, κ, δ] ↔
      ChoicelessSupercompactBelow (n + 2) α.val κ.val δ.val :=
  ⟨(hθ.of_le (by omega : n + 1 ≤ n + 2)).supercompactBelow_of_eval α κ δ,
    hθ.supercompactBelow_into_rank α κ δ⟩

theorem rankEmbedding_supercompactBelow {n : ℕ} {θ η f α κ δ : V}
    (hθ : Cn (n + 2) θ) (hη : Cn (n + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hα : α ∈ hierarchy θ) (hκ : κ ∈ hierarchy θ) (hδ : δ ∈ hierarchy θ)
    (h : ChoicelessSupercompactBelow (n + 2) α κ δ) :
    ChoicelessSupercompactBelow (n + 2) (f ‘ α) (f ‘ κ) (f ‘ δ) := by
  let aa : SetDomain (hierarchy θ) := ⟨α, hα⟩
  let kk : SetDomain (hierarchy θ) := ⟨κ, hκ⟩
  let dd : SetDomain (hierarchy θ) := ⟨δ, hδ⟩
  have hs := hθ.supercompactBelow_into_rank aa kk dd h
  have ht := (hf.eval_semisentence (choicelessSupercompactBelowFormula (n + 2)) ![aa, kk, dd]).mp hs
  have hv : hf.toFunction ∘ ![aa, kk, dd] = ![hf.toFunction aa, hf.toFunction kk, hf.toFunction dd] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl
      (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
  rw [hv] at ht
  exact hη.supercompactBelow_of_eval _ _ _ ht

end ZFVP
