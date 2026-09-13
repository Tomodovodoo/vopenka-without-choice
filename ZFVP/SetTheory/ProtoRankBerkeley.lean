import ZFVP.SetTheory.CnExtendible

/-! Proto rank-Berkeley cardinals, with the prescribed bound explicitly below the cardinal. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def protoRankBerkeleyFormula : SetTheorySemisentence 2 :=
  f“ζ δ. !initialOrdinalFormula δ ∧ ζ ∈ δ ∧ ∀ Θ, !IsOrdinal.dfn Θ → δ ∈ Θ →
    ∃ f κ, !piOneMembershipEmbeddingFormula (!hierarchyFormula Θ) (!hierarchyFormula Θ) f ∧
      !boundedCriticalPointFormula (!hierarchyFormula Θ) f κ ∧ ζ ∈ κ ∧ κ ∈ δ ∧ !value.dfn f δ = δ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsProtoRankBerkeley (ζ δ : V) : Prop :=
  IsInitialOrdinal δ ∧ ζ ∈ δ ∧ ∀ Θ, IsOrdinal Θ → δ ∈ Θ → ∃ f κ,
    IsCodedMembershipEmbedding (hierarchy Θ) (hierarchy Θ) f ∧
    IsCriticalPoint (hierarchy Θ) f κ ∧ ζ ∈ κ ∧ κ ∈ δ ∧ f ‘ δ = δ

theorem eval_protoRankBerkeleyFormula (ζ δ : V) :
    protoRankBerkeleyFormula.Evalb ![ζ, δ] ↔ IsProtoRankBerkeley ζ δ := by
  simp [protoRankBerkeleyFormula, IsProtoRankBerkeley]
  intro hinit hζ
  apply forall_congr'
  intro Θ
  apply imp_congr_right
  intro hΘ
  apply imp_congr_right
  intro _
  apply exists_congr
  intro f
  apply and_congr_right
  intro hf
  apply exists_congr
  intro κ
  let := hΘ
  let := hierarchy_transitive Θ
  exact and_congr (criticalPoint_iff_graphSpec hf.function).symm Iff.rfl

instance protoRankBerkeleyFormula_defined :
    ℒₛₑₜ-relation[V] IsProtoRankBerkeley via protoRankBerkeleyFormula :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    change protoRankBerkeleyFormula.Evalb v ↔ IsProtoRankBerkeley (v 0) (v 1)
    rw [← hv]
    exact eval_protoRankBerkeleyFormula _ _⟩

instance protoRankBerkeley_definable : ℒₛₑₜ-relation[V] IsProtoRankBerkeley :=
  protoRankBerkeleyFormula_defined.to_definable

end ZFVP
