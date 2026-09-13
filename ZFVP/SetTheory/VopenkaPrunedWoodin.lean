import ZFVP.SetTheory.CnExtendibleWoodinSupercompact
import ZFVP.SetTheory.VopenkaPruningUE

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem vopenka_bounded_rankBerkeley_woodinSupercompact_unbounded
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (β : V) [IsOrdinal β] (hno : ∀ μ : V, β ∈ μ → ¬IsNonzeroRankBerkeley μ)
    (ξ : V) [IsOrdinal ξ] : ∃ κ : V, ξ ∈ κ ∧ IsWoodinSupercompact κ := by
  obtain ⟨κ, hξκ, hκ⟩ := vopenka_bounded_rankBerkeley_unboundedExtendibility
    hVP β hno woodinSupercompactComplexity.val ξ
  exact ⟨κ, hξκ, hκ.woodinSupercompact⟩

end ZFVP
