import ZFVP.SetTheory.CnExtendible
import ZFVP.ModelTheory.RankEmbeddingAction

/-! One extra correctness level transfers lower positive C(n) membership. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_cn_iff {n : ℕ} {δ ε f α : V}
    (hδ : Cn (n + 2) δ) (hε : Cn (n + 2) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f) (hα : α ∈ hierarchy δ) :
    Cn (n + 1) α ↔ Cn (n + 1) (f ‘ α) := by
  let a : SetDomain (hierarchy δ) := ⟨α, hα⟩
  have hb : IsPiFormula (n + 2) (cnFormula (n + 1)) :=
    (cnFormula_pi_bound (n + 1)).mono (by omega)
  have hs := hδ.defined_correct hb (fun v ↦ Cn (n + 1) (v 0)) ![a]
  have ht := hε.defined_correct hb (fun v ↦ Cn (n + 1) (v 0)) (h.toFunction ∘ ![a])
  exact hs.symm.trans ((h.eval_semisentence (cnFormula (n + 1)) ![a]).trans ht)

theorem rankEmbedding_cn_same_iff {n : ℕ} {δ ε f α : V}
    (hδ : Cn (n + 2) δ) (hε : Cn (n + 2) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f) (hα : α ∈ hierarchy δ) :
    Cn (n + 2) α ↔ Cn (n + 2) (f ‘ α) := by
  let a : SetDomain (hierarchy δ) := ⟨α, hα⟩
  have hb := cnFormula_pi (by omega : 2 ≤ n + 2)
  have hs := hδ.defined_correct hb (fun v ↦ Cn (n + 2) (v 0)) ![a]
  have ht := hε.defined_correct hb (fun v ↦ Cn (n + 2) (v 0)) (h.toFunction ∘ ![a])
  exact hs.symm.trans ((h.eval_semisentence (cnFormula (n + 2)) ![a]).trans ht)

end ZFVP
