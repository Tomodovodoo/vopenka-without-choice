import ZFVP.ModelTheory.TransitiveZFNames
import ZFVP.SetTheory.SymmetricSystems

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameStabilizer_val (P Γ τ : SetDomain U) (hτ : IsForcingName P τ) :
    (nameStabilizer Γ τ).val = nameStabilizer Γ.val τ.val := by
  unfold nameStabilizer
  apply sep_val U
  intro π _
  rw [← nameAction_val U P π τ hτ]
  exact Subtype.ext_iff

theorem symmetricName_iff (P Γ F τ : SetDomain U) :
    IsSymmetricName P Γ F τ ↔ IsSymmetricName P.val Γ.val F.val τ.val := by
  constructor
  · rintro ⟨hτ, hs⟩
    refine ⟨(forcingName_iff U P τ).mp hτ, ?_⟩
    change (nameStabilizer Γ τ).val ∈ F.val at hs
    simpa only [nameStabilizer_val U P Γ τ hτ] using hs
  · rintro ⟨hτ, hs⟩
    have hn := (forcingName_iff U P τ).mpr hτ
    refine ⟨hn, ?_⟩
    change (nameStabilizer Γ τ).val ∈ F.val
    simpa only [nameStabilizer_val U P Γ τ hn] using hs

theorem hereditarilySymmetricName_iff (P Γ F τ : SetDomain U) :
    IsHereditarilySymmetricName P Γ F τ ↔ IsHereditarilySymmetricName P.val Γ.val F.val τ.val := by
  constructor
  · rintro ⟨hτ, hs⟩
    refine ⟨(forcingName_iff U P τ).mp hτ, ?_⟩
    intro σ hσ
    have hm : σ ∈ (nameClosure τ).val := nameClosure_val U τ ▸ hσ
    let σ' : SetDomain U := ⟨σ, (inferInstance : IsTransitive U).mem_trans hm (nameClosure τ).property⟩
    have h := hs σ' hm
    change (nameStabilizer Γ σ').val ∈ F.val at h
    simpa only [nameStabilizer_val U P Γ σ' (forcingName_mem_closure hτ hm)] using h
  · rintro ⟨hτ, hs⟩
    have hn := (forcingName_iff U P τ).mpr hτ
    refine ⟨hn, ?_⟩
    intro σ hσ
    have hm : σ.val ∈ nameClosure τ.val := nameClosure_val U τ ▸ hσ
    change (nameStabilizer Γ σ).val ∈ F.val
    simpa only [nameStabilizer_val U P Γ σ (forcingName_mem_closure hn hσ)] using hs σ.val hm

end TransitiveZF
end ZFVP
