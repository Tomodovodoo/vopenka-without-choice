import ZFVP.ModelTheory.CriticalLimitExtendibility
import ZFVP.SetTheory.UEImpliesVopenka

/-! Every parameterized Vopenka instance holds in the fixed critical limit model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem limit_vopenka (hlim : criticalLimit f κ ∈ hierarchy δ) (φ : SetTheorySemisentence 2) :
    SetSentenceTrue (vopenkaSentence φ) (hierarchy (criticalLimit f κ)) := by
  let := limit_ordinal hδ h hκ
  let := hierarchy_transitive (criticalLimit f κ)
  let := rankDomain_nonempty (omega_mem_limit hδ h hκ)
  let := limit_models_zf hδ h hκ
  apply (setSentenceTrue_iff_models _ _).mpr
  apply (eval_vopenkaSentence φ).mpr
  apply unboundedExtendibility_implies_vopenka
  intro n
  exact (eval_unboundedExtendibilitySentence (n + 1)).mp
    ((setSentenceTrue_iff_models _ _).mp (limit_unbounded_extendibility hδ h hκ hlim n))

end CriticalSequence

end ZFVP
