import ZFVP.ModelTheory.ForcingQuotientNames
import ZFVP.SetTheory.ForcingFoundationDecisions

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingQuotient_foundation (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (x : ForcingQuotient P R G hR hG.1)
    (hx : ∃ y, y ∈ x) : ∃ y, y ∈ x ∧ ∀ z, z ∈ x → z ∉ y := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
  obtain ⟨p, hpG, hpD⟩ := hG.2 _ (forcingFoundationDecisions_dense hR τ.val)
  rcases ((mem_forcingFoundationDecisions_iff _ _ _ _).mp hpD).2 with hnone | hmin
  · obtain ⟨y, hy⟩ := hx
    obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 y
    obtain ⟨q, hqG, hqM⟩ := (forcingQuotientMk_mem_iff P R G hR hG.1 σ τ).mp hy
    obtain ⟨r, hrG, hrp, hrq⟩ := hG.1.2.2.2 p hpG q hqG
    exact False.elim (hnone ⟨σ.val, σ.property, r, hG.1.1 r hrG, hrp,
      (atomicMembership_regular hR σ.val τ.val).2.1 q hqM r (hG.1.1 r hrG) hrq⟩)
  · obtain ⟨ν, hν, hpM, hmin⟩ := hmin
    let ν' : ForcingName P := ⟨ν, hν⟩
    refine ⟨forcingQuotientMk P R G hR hG.1 ν',
      (forcingQuotientMk_mem_iff P R G hR hG.1 ν' τ).mpr ⟨p, hpG, hpM⟩, ?_⟩
    intro z hzτ hzν
    obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 z
    obtain ⟨μ, s, _, hμs, he⟩ := (forcingQuotientMk_mem_subname_iff P R G hR hG σ ν').mp hzν
    rw [he] at hzτ
    obtain ⟨q, hqG, hqM⟩ := (forcingQuotientMk_mem_iff P R G hR hG.1 μ τ).mp hzτ
    obtain ⟨r, hrG, hrp, hrq⟩ := hG.1.2.2.2 p hpG q hqG
    exact hmin μ.val μ.property (rank_subname_lt hμs) r (hG.1.1 r hrG) hrp
      ((atomicMembership_regular hR μ.val τ.val).2.1 q hqM r (hG.1.1 r hrG) hrq)

end ZFVP
