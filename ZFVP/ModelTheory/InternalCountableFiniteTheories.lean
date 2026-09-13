import ZFVP.ModelTheory.InternalCountableTheories
import ZFVP.SetTheory.NaturalClosureCardinality
import ZFVP.SetTheory.SchroederBernstein
import ZFVP.SetTheory.MaximalAntichains

/-! Cardinal bounds for the actual finite-consistency poset. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem finiteConsistentOpenExtensions_countable (hAC : InternalChoice V) {T A : V}
    (hA : IsInternallyCountable A) : IsInternallyCountable (finiteConsistentOpenExtensions T A) := by
  have hs : IsInternallyCountable (finiteSequences A) :=
    finiteSequences_cardLE_of_cardLE_initial hAC
      ⟨IsOrdinal.ω, fun _ hn ↦ omega_not_cardLE_natural hn⟩ (subset_refl _) hA
  apply internallyCountable_subset (internallyCountable_repl range (by definability) hs)
  intro Γ hΓ
  obtain ⟨hΓA, hfin, _⟩ := (mem_finiteConsistentOpenExtensions_iff T A Γ).mp hΓ
  obtain ⟨n, hn, hΓn⟩ := hfin
  obtain ⟨e, he, _, her⟩ := exists_bijection_of_cardEQ (And.intro hΓn.2 hΓn.1)
  exact (repl_spec _).mpr ⟨e,
    (mem_finiteSequences_iff A e).mpr ⟨n, hn, mem_function_of_mem_function_of_subset he hΓA⟩,
    her.symm⟩

theorem finiteConsistentOpenExtensions_countable_antichains (hAC : InternalChoice V) {T A B : V}
    (hA : IsInternallyCountable A)
    (hB : IsForcingAntichain (finiteConsistentOpenExtensions T A)
      (reverseInclusionOrder (finiteConsistentOpenExtensions T A)) B) : IsInternallyCountable B :=
  internallyCountable_subset (finiteConsistentOpenExtensions_countable hAC hA) hB.1

end ZFVP
