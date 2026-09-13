import ZFVP.SetTheory.CnSandwich
import ZFVP.ModelTheory.CodedMembershipEmbedding

/-! Correct heights cofinal below an ordinal, and their rank interpretation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def cnCofinalFormula (n : ℕ) : SetTheorySemisentence 1 :=
  “θ. ∀ β ∈ θ, ∃ δ ∈ θ, β ∈ δ ∧ !(cnFormula n) δ”

theorem eval_cnCofinal_components {W : Type*} [SetStructure W] (n : ℕ) (θ : W) :
    (cnCofinalFormula n).Evalb ![θ] ↔
      ∀ β ∈ θ, ∃ δ ∈ θ, β ∈ δ ∧ (cnFormula n).Evalb ![δ] := by
  simp [cnCofinalFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def CnCofinal (n : ℕ) (θ : V) : Prop := ∀ β ∈ θ, ∃ δ ∈ θ, β ∈ δ ∧ Cn n δ

instance cnCofinalFormula_defined (n : ℕ) : ℒₛₑₜ-predicate[V] (CnCofinal n) via cnCofinalFormula n :=
  ⟨fun v ↦ by simp [cnCofinalFormula, CnCofinal]⟩

instance cnCofinal_definable (n : ℕ) : ℒₛₑₜ-predicate[V] (CnCofinal n) :=
  (cnCofinalFormula_defined n).to_definable

theorem Cn.cnCofinal_into_rank {n : ℕ} {θ : V} (hθ : Cn (n + 1) θ)
    (γ : SetDomain (hierarchy θ)) (h : CnCofinal (n + 2) γ.val) :
    (cnCofinalFormula (n + 2)).Evalb ![γ] := by
  let := hθ.ordinal
  let := hierarchy_transitive θ
  apply (eval_cnCofinal_components _ γ).mpr
  intro β hβ
  obtain ⟨δ, hδγ, hβδ, hδ⟩ := h β.val hβ
  let := hδ.ordinal
  have hδV := (hierarchy_transitive θ).mem_trans hδγ γ.property
  exact ⟨⟨δ, hδV⟩, hδγ, hβδ,
    hδ.into_lower_rank hθ (ordinal_mem_hierarchy_iff.mp hδV)⟩

theorem Cn.cnCofinal_of_eval {n : ℕ} {θ β : V} (hθ : Cn (n + 1) θ)
    (γ : SetDomain (hierarchy θ)) (hβ : Cn (n + 2) β) (hγβ : γ.val ⊆ β) (hβθ : β ∈ θ)
    (h : (cnCofinalFormula (n + 2)).Evalb ![γ]) : CnCofinal (n + 2) γ.val := by
  let := hθ.ordinal
  let := hierarchy_transitive θ
  intro ξ hξ
  let x : SetDomain (hierarchy θ) := ⟨ξ, (hierarchy_transitive θ).mem_trans hξ γ.property⟩
  obtain ⟨δ, hδγ, hξδ, hδ⟩ := (eval_cnCofinal_components _ γ).mp h x hξ
  exact ⟨δ.val, hδγ, hξδ, cn_sandwich hθ hβ (hγβ _ hδγ) hβθ hδ⟩

theorem rankEmbedding_cnCofinal_image_eval {n : ℕ} {θ η f γ : V}
    (hθ : Cn (n + 1) θ)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hγ : γ ∈ hierarchy θ) (h : CnCofinal (n + 2) γ) :
    (cnCofinalFormula (n + 2)).Evalb ![hf.toFunction ⟨γ, hγ⟩] := by
  have hs := hθ.cnCofinal_into_rank ⟨γ, hγ⟩ h
  have ht := (hf.eval_semisentence (cnCofinalFormula (n + 2)) ![⟨γ, hγ⟩]).mp hs
  have hv : hf.toFunction ∘ ![⟨γ, hγ⟩] = ![hf.toFunction ⟨γ, hγ⟩] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rwa [hv] at ht

end ZFVP
