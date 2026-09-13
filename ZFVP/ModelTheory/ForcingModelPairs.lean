import ZFVP.ModelTheory.ForcingModelChecks
import ZFVP.SetTheory.ForcingPairNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem of_pair (S : ForcingContext V) (σ τ : ForcingName S.P) :
    S.ofName (forcingPairName σ τ S.one S.top.1) = {S.ofName σ, S.ofName τ} := by
  apply SetTheory.mem_ext_iff.mpr
  intro x
  rw [mem_insert, mem_singleton_iff]
  exact forcingQuotient_pairName S.P S.R S.G S.order S.generic σ τ S.one
    (externalForcingFilter_top S.generic.1 S.top) x

theorem of_orderedPair (S : ForcingContext V) (σ τ : ForcingName S.P) :
    S.ofName ⟨orderedPairName S.one σ.val τ.val, orderedPairName_isName S.top.1 σ.property τ.property⟩ =
      ⟨S.ofName σ, S.ofName τ⟩ₖ := by
  change S.ofName (forcingPairName (forcingPairName σ σ S.one S.top.1)
    (forcingPairName σ τ S.one S.top.1) S.one S.top.1) = _
  rw [S.of_pair, S.of_pair, S.of_pair]
  simp [kpair]

end ForcingContext
end ZFVP
