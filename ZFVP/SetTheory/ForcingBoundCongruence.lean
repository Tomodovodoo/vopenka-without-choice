import ZFVP.SetTheory.ForcingBoundSectionCompatibility

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCoherentForcingBound.congr {θ P R π B P' R' π' B' i I : V}
    (h : IsCoherentForcingBound θ P R π B i I)
    (hPi : P ‘ i = P' ‘ i) (hRi : R ‘ i = R' ‘ i)
    (hP : ∀ j ∈ θ, P ‘ j = P' ‘ j) (hR : ∀ j ∈ θ, R ‘ j = R' ‘ j)
    (hπi : ∀ j ∈ θ, i ⊆ j → π ‘ ⟨i, j⟩ₖ = π' ‘ ⟨i, j⟩ₖ)
    (hπ : ∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k → π ‘ ⟨j, k⟩ₖ = π' ‘ ⟨j, k⟩ₖ)
    (hB : ∀ j ∈ θ, i ⊆ j → B ‘ j = B' ‘ j) :
    IsCoherentForcingBound θ P' R' π' B' i I := by
  constructor
  · intro j hj hij f hf p hp hb
    have hh := h.bound j hj hij
    rw [hP j hj, hR j hj, hPi, hRi, hπi j hj hij, hB j hj hij] at hh
    exact hh f hf p hp hb
  · intro j hj k hk hij hjk f hf p hp hb
    have hh := h.commute j hj k hk hij hjk
    rw [hP k hk, hR k hk, hPi, hRi, hπi k hk (subset_trans hij hjk),
      hπ j hj k hk hij hjk, hB k hk (subset_trans hij hjk), hB j hj hij] at hh
    exact hh f hf p hp hb

theorem IsSectionCompatibleForcingBound.congr {θ P R π E B P' R' π' E' B' i I : V}
    (h : IsSectionCompatibleForcingBound θ P R π E B i I)
    (hPi : P ‘ i = P' ‘ i) (hRi : R ‘ i = R' ‘ i)
    (hP : ∀ j ∈ θ, P ‘ j = P' ‘ j) (hR : ∀ j ∈ θ, R ‘ j = R' ‘ j)
    (hπi : ∀ j ∈ θ, i ⊆ j → π ‘ ⟨i, j⟩ₖ = π' ‘ ⟨i, j⟩ₖ)
    (hE : ∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k → E ‘ ⟨j, k⟩ₖ = E' ‘ ⟨j, k⟩ₖ)
    (hB : ∀ j ∈ θ, i ⊆ j → B ‘ j = B' ‘ j) :
    IsSectionCompatibleForcingBound θ P' R' π' E' B' i I := by
  constructor
  intro j hj k hk hij hjk f hf p hp hb
  have hh := h.compatible j hj k hk hij hjk
  rw [hP j hj, hR j hj, hPi, hRi, hπi j hj hij,
    hE j hj k hk hij hjk, hB k hk (subset_trans hij hjk), hB j hj hij] at hh
  exact hh f hf p hp hb

theorem coherentForcingBound_before_base {θ P R π B i I : V} (hθ : θ ⊆ i) :
    IsCoherentForcingBound θ P R π B i I := by
  constructor
  · intro j hj hij
    exact (mem_irrefl j (hij j (hθ j hj))).elim
  · intro j hj k hk hij
    exact (mem_irrefl j (hij j (hθ j hj))).elim

theorem sectionCompatibleForcingBound_before_base {θ P R π E B i I : V} (hθ : θ ⊆ i) :
    IsSectionCompatibleForcingBound θ P R π E B i I := by
  constructor
  intro j hj k hk hij
  exact (mem_irrefl j (hij j (hθ j hj))).elim

end ZFVP
