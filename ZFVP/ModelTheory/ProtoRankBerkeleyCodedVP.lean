import ZFVP.ModelTheory.ProtoRankBerkeleyVopenka
import ZFVP.Syntax.VopenkaCodes

/-! Proto rank-Berkeley gives a rank model satisfying every internally coded VP instance. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsProtoRankBerkeley.exists_internalZF_codedVP {ζ δ : V} (hδ : IsProtoRankBerkeley ζ δ) :
    ∃ Λ : V, IsOrdinal Λ ∧ Λ ⊆ δ ∧ ζ ∈ Λ ∧ internalCofinality Λ = (ω : V) ∧
      IsInternalZFModel (hierarchy Λ) ∧
      ∀ φ : V, IsMembershipFormulaCode (2 : V) φ →
        MembershipSatisfies (hierarchy Λ) 0 (vopenkaCode φ) ∅ := by
  let := hδ.1.1
  obtain ⟨Θ, hδΘ, hΘ⟩ := cn_unbounded 1 δ
  let := hΘ.ordinal
  obtain ⟨f, κ, hf, hκ, hζκ, hκδ, hfix⟩ := hδ.2.2 Θ hΘ.ordinal hδΘ
  have hδV := ordinal_subset_hierarchy Θ δ hδΘ
  have hlim := CriticalSequence.limit_mem_of_fixed_bound hΘ hf hκ hδ.1.1 hδV hfix hκδ
  have hΛ := CriticalSequence.limit_ordinal hΘ hf hκ
  let := hΛ
  have hκΛ : κ ∈ criticalLimit f κ := by
    simpa using CriticalSequence.iterate_mem_limit hΘ hf hκ (by simp : (0 : V) ∈ ω)
  refine ⟨criticalLimit f κ, hΛ, CriticalSequence.limit_below_fixed hΘ hf hκ hδ.1.1 hδV hfix hκδ,
    IsOrdinal.toIsTransitive.mem_trans hζκ hκΛ, CriticalSequence.limit_cofinality hΘ hf hκ,
    CriticalSequence.limit_internalZFModel hΘ hf hκ, ?_⟩
  intro φ hφ
  exact CriticalSequence.limit_vopenkaCode hΘ hf hκ hlim hφ

end ZFVP
