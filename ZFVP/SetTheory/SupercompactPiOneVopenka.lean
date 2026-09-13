import ZFVP.SetTheory.InaccessibleCnOne
import ZFVP.SetTheory.SupercompactMagidorHighCritical
import ZFVP.SetTheory.MagidorSupercompactMeasure

/-! The measure-supercompactness characterization of the Pi-one Vopenka scheme. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsSupercompact.zfHighCritical (hAC : InternalChoice V)
    (hSC : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsSupercompact κ)
    {κ : V} (hκ : IsSupercompact κ) : IsZFHighCriticalMagidorSupercompact κ := by
  refine ⟨hκ.isOrdinal, hκ.2.1, ?_⟩
  intro ρ hρ hκρ η hη
  obtain ⟨γ, hργ, hγSC⟩ := hSC ρ hρ
  have hγ := hγSC.inaccessible hAC
  let := hγ.1
  obtain ⟨β, hβκ, hβ, α, hαβ, hηα, e, he, hc, heα⟩ :=
    hκ.highCritical_inaccessible_target hAC hSC hγ
      (IsOrdinal.toIsTransitive.mem_trans hκρ hργ) hη
  exact ⟨γ, hργ, hγ.cn_one hAC, hγ.isZFRank,
    β, hβκ, hβ.cn_one hAC, hβ.isZFRank, α, hαβ, hηα, e, he, hc, heα⟩

theorem supercompact_unbounded_implies_pi_one_vopenka (hAC : InternalChoice V)
    (hSC : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsSupercompact κ)
    (φ : SetTheorySemisentence 2) (hφ : IsPiFormula 1 φ) : VopenkaInstance (V := V) φ := by
  apply magidorSupercompact_unbounded_implies_pi_one_vopenka_zf _ φ hφ
  intro α hα
  obtain ⟨κ, hακ, hκ⟩ := hSC α hα
  exact ⟨κ, hακ, hκ.zfHighCritical hAC hSC⟩

theorem pi_one_vopenka_iff_unbounded_supercompact_measure (hAC : InternalChoice V) :
    (∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ) ↔
      (∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsSupercompact κ) :=
  ⟨supercompact_unbounded_of_pi_one_vopenka hAC,
    fun hSC φ hφ ↦ supercompact_unbounded_implies_pi_one_vopenka hAC hSC φ hφ⟩

end ZFVP
