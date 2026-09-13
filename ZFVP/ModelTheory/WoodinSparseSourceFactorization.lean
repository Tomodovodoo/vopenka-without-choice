import ZFVP.ModelTheory.WoodinSparseSourceHomogeneity
import ZFVP.ModelTheory.ProjectionFactorization

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ j : V} [IsOrdinal θ]
local notation "c" => woodinSparseSourceStageCode θ
local notation "π" => (forcingCodeπ c) ‘ ⟨j,woodinSourceIndex θ⟩ₖ
local notation "e" => (forcingCodeE c) ‘ ⟨j,woodinSourceIndex θ⟩ₖ

namespace ForcingContext

theorem woodinSparseSource_split (A B : ForcingContext V)
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hj : j ∈ succ (woodinSourceIndex θ))
    (hAP : A.P = (forcingCodeP c) ‘ j) (hAR : A.R = (forcingCodeR c) ‘ j)
    (hBP : B.P = (forcingCodeP c) ‘ (woodinSourceIndex θ))
    (hBR : B.R = (forcingCodeR c) ‘ (woodinSourceIndex θ)) :
    IsForcingSplitProjection A.P A.R B.P B.R π e := by
  let := IsOrdinal.of_mem hj
  rw [hAP,hAR,hBP,hBR]
  exact (woodinSparseSourceStageCode_valid hΩ hAC hθ).system.splitProjection hj (mem_succ_self _)
    (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hj))

theorem woodinSparseSource_factorization (A B : ForcingContext V)
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hj : j ∈ succ (woodinSourceIndex θ))
    (hAP : A.P = (forcingCodeP c) ‘ j) (hAR : A.R = (forcingCodeR c) ‘ j)
    (hBP : B.P = (forcingCodeP c) ‘ (woodinSourceIndex θ))
    (hBR : B.R = (forcingCodeR c) ‘ (woodinSourceIndex θ))
    (hG : forcingProjectionGeneric A.P A.R π B.G = A.G) :
    ∃ F : (A.projectionQuotientContext B
        (A.woodinSparseSource_split B hΩ hAC hθ hj hAP hAR hBP hBR) hG).Model ≃ B.Model,
      (∀ x y, F x ∈ F y ↔ x ∈ y) ∧
      ∀ x : V, F ((A.projectionQuotientContext B
        (A.woodinSparseSource_split B hΩ hAC hθ hj hAP hAR hBP hBR) hG).check (A.check x)) = B.check x := by
  let hs := A.woodinSparseSource_split B hΩ hAC hθ hj hAP hAR hBP hBR
  exact ⟨A.projectionFactorizationEquiv B hs hG,
    A.projectionFactorizationEquiv_mem_iff B hs hG, A.projectionFactorizationEquiv_ground B hs hG⟩

end ForcingContext
end ZFVP
