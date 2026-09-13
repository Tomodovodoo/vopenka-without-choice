import ZFVP.SetTheory.AtomicEquality

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem atomicEquality_trans {P R : V} (hR : IsForcingPreorder P R) (σ τ υ p : V)
    (hστ : p ∈ atomicEquality P R σ τ) (hτυ : p ∈ atomicEquality P R τ υ) :
    p ∈ atomicEquality P R σ υ := by
  have h := projectedRank_induction (nameClosure σ) (fun x : V ↦ x) (by definability)
    (fun x ↦ ∀ y z q, q ∈ atomicEquality P R x y → q ∈ atomicEquality P R y z →
      q ∈ atomicEquality P R x z) (by definability) ?_
  · exact h σ (mem_nameClosure_self σ) τ υ p hστ hτυ
  intro x hx ih y z q hxy hyz
  obtain ⟨hqP, hxyL, hxyR⟩ := (mem_atomicEquality_iff _ _ _ _ _).mp hxy
  obtain ⟨_, hyzL, hyzR⟩ := (mem_atomicEquality_iff _ _ _ _ _).mp hyz
  apply (mem_atomicEquality_iff _ _ _ _ _).mpr
  refine ⟨hqP, ?_, ?_⟩
  · intro x' s hs r hr hrq hrs
    obtain ⟨v, hv, hvr, y', t, ht, hvt, hexy⟩ := hxyL x' s hs r hr hrq hrs
    obtain ⟨w, hw, hwv, z', u, hu, hwu, heyz⟩ := hyzL y' t ht v hv
      (hR.2.2 v hv r hr q hqP hvr hrq) hvt
    have hlow := ih x' (nameClosure_closed σ x hx x' (mem_domain_of_kpair_mem hs))
      (rank_subname_lt hs) y' z' w (atomicEquality_mono hR hexy hw hwv) heyz
    exact ⟨w, hw, hR.2.2 w hw v hv r hr hwv hvr, z', u, hu, hwu, hlow⟩
  · intro z' u hu r hr hrq hru
    obtain ⟨v, hv, hvr, y', t, ht, hvt, heyz⟩ := hyzR z' u hu r hr hrq hru
    obtain ⟨w, hw, hwv, x', s, hs, hws, hexy⟩ := hxyR y' t ht v hv
      (hR.2.2 v hv r hr q hqP hvr hrq) hvt
    have hlow := ih x' (nameClosure_closed σ x hx x' (mem_domain_of_kpair_mem hs))
      (rank_subname_lt hs) y' z' w hexy (atomicEquality_mono hR heyz hw hwv)
    exact ⟨w, hw, hR.2.2 w hw v hv r hr hwv hvr, x', s, hs, hws, hlow⟩

end ZFVP
