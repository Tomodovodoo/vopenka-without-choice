import ZFVP.ModelTheory.TransitiveZFEmbedding

/-! The paper's C(n)-extendibility predicate and its uniform first-order dictionary. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def cnExtendibleFormula (n : ℕ) : SetTheorySemisentence 1 :=
  f“κ. !initialOrdinalFormula κ ∧ ∀ μ, !(cnFormula n) μ → κ ∈ μ →
    ∃ ν e, μ ∈ ν ∧ !(cnFormula n) ν ∧
      !piOneMembershipEmbeddingFormula (!hierarchyFormula μ) (!hierarchyFormula ν) e ∧
      !boundedCriticalPointFormula (!hierarchyFormula μ) e κ ∧ μ ∈ !value.dfn e κ”

def unboundedExtendibilitySentence (n : ℕ) : SetTheorySentence :=
  “∀ α, !IsOrdinal.dfn α → ∃ κ, α ∈ κ ∧ !(cnExtendibleFormula n) κ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCnExtendible (n : ℕ) (κ : V) : Prop :=
  IsInitialOrdinal κ ∧ ∀ μ, Cn n μ → κ ∈ μ → ∃ ν e, μ ∈ ν ∧ Cn n ν ∧
    IsCodedMembershipEmbedding (hierarchy μ) (hierarchy ν) e ∧
    IsCriticalPoint (hierarchy μ) e κ ∧ μ ∈ e ‘ κ

theorem eval_cnExtendibleFormula (n : ℕ) (κ : V) :
    (cnExtendibleFormula n).Evalb ![κ] ↔ IsCnExtendible n κ := by
  simp [cnExtendibleFormula, IsCnExtendible]
  intro hinit
  apply forall_congr'
  intro μ
  apply imp_congr_right
  intro hμ
  apply imp_congr_right
  intro _
  apply exists_congr
  intro ν
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply exists_congr
  intro e
  apply and_congr_right
  intro he
  let := hμ.ordinal
  let := hierarchy_transitive μ
  exact and_congr (criticalPoint_iff_graphSpec he.function).symm Iff.rfl

instance cnExtendibleFormula_defined (n : ℕ) :
    ℒₛₑₜ-predicate[V] (IsCnExtendible n) via cnExtendibleFormula n :=
  ⟨fun v ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change (cnExtendibleFormula n).Evalb v ↔ IsCnExtendible n (v 0)
    rw [← hv]
    exact eval_cnExtendibleFormula n (v 0)⟩

instance cnExtendible_definable (n : ℕ) : ℒₛₑₜ-predicate[V] (IsCnExtendible n) :=
  (cnExtendibleFormula_defined n).to_definable

theorem eval_unboundedExtendibilitySentence (n : ℕ) :
    V↓[ℒₛₑₜ] ⊧ unboundedExtendibilitySentence n ↔ ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsCnExtendible n κ := by
  change (unboundedExtendibilitySentence n).Evalb (![] : Fin 0 → V) ↔ _
  simp [unboundedExtendibilitySentence]

end ZFVP
