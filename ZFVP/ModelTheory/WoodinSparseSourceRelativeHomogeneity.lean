import ZFVP.ModelTheory.WoodinSparseRelativeHomogeneity
import ZFVP.ModelTheory.WoodinSparseSourceCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "P[" θ "]" => (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "R[" θ "]" => (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "π[" i "," θ "]" => (forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ

theorem woodinSparseSource_relative_homogeneous {Ω δ p q : V} [IsOrdinal δ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hδ : δ ⊆ Ω)
    (hp : p ∈ P[Ω]) (hq : q ∈ P[Ω]) (hle : ⟨π[δ,Ω] ‘ p,π[δ,Ω] ‘ q⟩ₖ ∈ R[δ]) :
    ∃ f, IsForcingAutomorphism P[Ω] R[Ω] f ∧
      (∀ z ∈ P[Ω], π[δ,Ω] ‘ (f ‘ z) = π[δ,Ω] ‘ z) ∧
      ForcingCompatible P[Ω] R[Ω] (f ‘ p) q := by
  let := hΩ.inaccessible.1
  have hδ' : δ ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hδ)
  have hrΩ := woodinSparseSourceStageCode_row (mem_succ_self Ω)
  have hrδ := woodinSparseSourceStageCode_row (mem_succ_self δ)
  have hπ := (woodinSparseSourceStageCode_matrices hδ' (mem_succ_self Ω)).1
  rw [hrΩ.1] at hp hq
  rw [hπ,hrδ.2] at hle
  rw [hrΩ.1,hrΩ.2,hπ]
  exact woodinSparseStage_relative_homogeneous hΩ hAC hδ hp hq hle

theorem woodinSparseSource_relative_homogeneity {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ δ ∈ Ω, IsWoodinSupercompact δ →
      ∀ t ∈ P[Ω], ∀ p ∈ P[Ω], ⟨π[δ,Ω] ‘ p,π[δ,Ω] ‘ t⟩ₖ ∈ R[δ] →
        ∃ f, IsForcingAutomorphism P[Ω] R[Ω] f ∧
          (∀ z ∈ P[Ω], π[δ,Ω] ‘ (f ‘ z) = π[δ,Ω] ‘ z) ∧
          ForcingCompatible P[Ω] R[Ω] (f ‘ p) t := by
  let := hΩ.inaccessible.1
  intro δ hδ hδSC t ht p hp hle
  let := hδSC.inaccessible.1
  exact woodinSparseSource_relative_homogeneous hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hδ) hp ht hle

end ZFVP
