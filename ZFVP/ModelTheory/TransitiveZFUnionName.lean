import ZFVP.ModelTheory.TransitiveZFNames
import ZFVP.ModelTheory.TransitiveZFForcingOrders
import ZFVP.SetTheory.ForcingUnionName

/-! The canonical forcing union name is absolute to transitive ZF sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingUnionName_val (P R τ : SetDomain U) :
    (forcingUnionName P R τ).val = forcingUnionName P.val R.val τ.val := by
  unfold forcingUnionName
  rw [← nameClosure_val U τ, ← prod_val U]
  apply sep_val U
  intro z hz
  obtain ⟨ν, _, q, _, rfl⟩ := mem_prod_iff.mp hz
  simp only [kpair_val U, kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · rintro ⟨σ, s, t, hσ, ht, hsR, htR⟩
    refine ⟨σ.val, s.val, t.val, ?_, ?_, ?_, ?_⟩
    · exact kpair_val U σ s ▸ hσ
    · exact kpair_val U ν t ▸ ht
    · exact kpair_val U q s ▸ hsR
    · exact kpair_val U q t ▸ htR
  · rintro ⟨σ, s, t, hσ, ht, hsR, htR⟩
    have hσs := kpair_components_mem_transitive
      ((inferInstance : IsTransitive U).mem_trans hσ τ.property)
    have htt := kpair_components_mem_transitive
      ((inferInstance : IsTransitive U).mem_trans ht hσs.1)
    let σ' : SetDomain U := ⟨σ, hσs.1⟩
    let s' : SetDomain U := ⟨s, hσs.2⟩
    let t' : SetDomain U := ⟨t, htt.2⟩
    refine ⟨σ', s', t', ?_, ?_, ?_, ?_⟩
    · change (⟨σ', s'⟩ₖ : SetDomain U).val ∈ τ.val
      rw [kpair_val U]
      exact hσ
    · change (⟨ν, t'⟩ₖ : SetDomain U).val ∈ σ'.val
      rw [kpair_val U]
      exact ht
    · change (⟨q, s'⟩ₖ : SetDomain U).val ∈ R.val
      rw [kpair_val U]
      exact hsR
    · change (⟨q, t'⟩ₖ : SetDomain U).val ∈ R.val
      rw [kpair_val U]
      exact htR

end TransitiveZF
end ZFVP
