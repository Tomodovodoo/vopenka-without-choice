import ZFVP.SetTheory.SymmetryAction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameAction_pair_mem_iff {P R π τ σ p : V} (hπ : IsForcingAutomorphism P R π)
    (hτ : IsForcingName P τ) (hσ : IsForcingName P σ) (hp : p ∈ P) :
    ⟨nameAction π σ, π ‘ p⟩ₖ ∈ nameAction π τ ↔ ⟨σ, p⟩ₖ ∈ τ := by
  constructor
  · intro h
    obtain ⟨ν, q, hq, he⟩ := (mem_nameAction_iff hτ π _).mp h
    obtain ⟨heσ, hep⟩ := kpair_iff.mp he
    have hσν := nameAction_injective hπ hσ (forcingName_subname hτ hq) heσ
    have hpq : p = q := by
      have hh := congrArg (fun r : V ↦ (converseGraph π) ‘ r) hep
      simpa only [converseGraph_value_value hπ.1 hπ.2.1 hp,
        converseGraph_value_value hπ.1 hπ.2.1 (forcingName_condition hτ hq)] using hh
    exact hσν.symm ▸ hpq.symm ▸ hq
  · intro h
    exact (mem_nameAction_iff hτ π _).mpr ⟨σ, p, h, rfl⟩

theorem nameAction_eq_of_pair_iff {P R π σ τ : V} (hπ : IsForcingAutomorphism P R π)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (he : ∀ ν, IsForcingName P ν → ∀ p ∈ P,
      ⟨nameAction π ν, π ‘ p⟩ₖ ∈ τ ↔ ⟨ν, p⟩ₖ ∈ σ) : nameAction π σ = τ := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  constructor
  · intro hz
    obtain ⟨ν, p, hp, rfl⟩ := (mem_nameAction_iff hσ π z).mp hz
    exact (he ν (forcingName_subname hσ hp) p (forcingName_condition hσ hp)).mpr hp
  · intro hz
    obtain ⟨ν, p, hp, rfl, hν⟩ := (forcingName_iff P τ).mp hτ z hz
    obtain ⟨q, hq, rfl⟩ := forcingAutomorphism_surjective hπ p hp
    let μ := nameAction (converseGraph π) ν
    have hμ : IsForcingName P μ := nameAction_isName (forcingAutomorphism_inverse hπ).1 hν
    have hcancel : nameAction π μ = ν := nameAction_cancel_inverse hπ hν
    have hm : ⟨μ, q⟩ₖ ∈ σ := (he μ hμ q hq).mp (by simpa only [hcancel] using hz)
    exact (mem_nameAction_iff hσ π _).mpr ⟨μ, q, hm, by rw [hcancel]⟩

end ZFVP
