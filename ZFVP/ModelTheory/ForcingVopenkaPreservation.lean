import ZFVP.ModelTheory.SymmetricVopenkaPreservation
import ZFVP.SetTheory.TrivialSymmetry
import ZFVP.SetTheory.VopenkaIsomorphism

/-! Ordinary set forcing is the specialization with the trivial symmetry group. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

noncomputable def trivialSymmetricContext (S : ForcingContext V) (hP : IsForcingPoset S.P S.R) :
    SymmetricContext V where
  toForcingContext := S
  Γ := {identity S.P}
  F := {{identity S.P}}
  poset := hP
  group := trivialAutomorphismGroup S.P S.R
  normal := trivialNormalFilter S.P S.R

theorem trivialSymmetricInclusion_surjective (S : ForcingContext V) (hP : IsForcingPoset S.P S.R) :
    Function.Surjective (S.trivialSymmetricContext hP).toOrdinary := by
  intro x
  obtain ⟨τ, rfl⟩ := S.ofName_surjective x
  refine ⟨(S.trivialSymmetricContext hP).ofName ⟨τ.val, ?_⟩, rfl⟩
  exact (trivialHereditarilySymmetric_iff S.P τ.val).mpr τ.property

noncomputable def trivialSymmetricEquiv (S : ForcingContext V) (hP : IsForcingPoset S.P S.R) :
    (S.trivialSymmetricContext hP).Model ≃ S.Model :=
  Equiv.ofBijective (S.trivialSymmetricContext hP).toOrdinary
    ⟨(S.trivialSymmetricContext hP).toOrdinary_injective, S.trivialSymmetricInclusion_surjective hP⟩

theorem vopenkaInstance (S : ForcingContext V) (hP : IsForcingPoset S.P S.R)
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (φ : SetTheorySemisentence 2) : VopenkaInstance (V := S.Model) φ := by
  exact @vopenkaInstance_of_membershipIso (S.trivialSymmetricContext hP).Model S.Model
    (SymmetricContext.modelSetStructure _) (ForcingContext.modelSetStructure S)
    (SymmetricContext.modelNonempty _) (ForcingContext.modelNonempty S)
    (SymmetricContext.modelZF _) (ForcingContext.modelZF S) (S.trivialSymmetricEquiv hP)
    (S.trivialSymmetricContext hP).toOrdinary_mem_iff φ ((S.trivialSymmetricContext hP).vopenkaInstance hVP φ)

end ForcingContext
end ZFVP
