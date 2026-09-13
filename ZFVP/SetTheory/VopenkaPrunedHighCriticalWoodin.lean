import ZFVP.SetTheory.CnExtendibleHighCriticalWoodin
import ZFVP.SetTheory.VopenkaPruningUE
import ZFVP.SetTheory.ChoicelessInaccessible

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem vopenka_bounded_rankBerkeley_highCriticalWoodin_unbounded
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (β : V) [IsOrdinal β] (hno : ∀ μ : V, β ∈ μ → ¬IsNonzeroRankBerkeley μ)
    (ξ : V) [IsOrdinal ξ] : ∃ κ : V, ξ ∈ κ ∧ HasHighCriticalWoodinWitnesses κ := by
  obtain ⟨κ, hξκ, hκ⟩ := vopenka_bounded_rankBerkeley_unboundedExtendibility
    hVP β hno highCriticalWoodinComplexity.val ξ
  exact ⟨κ, hξκ, hκ.highCriticalWoodin⟩

theorem vopenka_bounded_rankBerkeley_collapseTargets_unbounded
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (β : V) [IsOrdinal β] (hno : ∀ μ : V, β ∈ μ → ¬IsNonzeroRankBerkeley μ)
    (ξ : V) [IsOrdinal ξ] : ∃ κ : V, ξ ∈ κ ∧ IsChoicelessInaccessible κ ∧
      IsRegularCardinal κ ∧ HasHighCriticalWoodinWitnesses κ := by
  obtain ⟨κ, hξκ, hκ⟩ := vopenka_bounded_rankBerkeley_unboundedExtendibility
    hVP β hno highCriticalWoodinComplexity.val ξ
  exact ⟨κ, hξκ, hκ.inaccessible, hκ.regular, hκ.highCriticalWoodin⟩

end ZFVP
