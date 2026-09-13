import ZFVP.ModelTheory.ProjectionQuotientAutomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem projectionQuotient_weak_homogeneous (A : ForcingContext V) {Q S π : V}
    (hS : IsForcingPreorder Q S) (hπ : IsForcingProjection A.P A.R Q S π)
    (hhom : ∀ p ∈ Q, ∀ q ∈ Q, ⟨π ‘ p, π ‘ q⟩ₖ ∈ A.R →
      ∃ f, IsForcingAutomorphism Q S f ∧ (∀ z ∈ Q, π ‘ (f ‘ z) = π ‘ z) ∧
        ∃ w ∈ Q, ⟨w,f ‘ p⟩ₖ ∈ S ∧ ⟨w,q⟩ₖ ∈ S ∧ π ‘ w = π ‘ p) :
    ∀ x ∈ A.projectionQuotient Q π, ∀ y ∈ A.projectionQuotient Q π,
      ∃ F, IsForcingAutomorphism (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) F ∧
        ForcingCompatible (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) (F ‘ x) y := by
  intro x hx y hy
  obtain ⟨p,hp,hpG,rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps x).mp hx
  obtain ⟨q,hq,hqG,rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps y).mp hy
  obtain ⟨u,huG,hup,huq⟩ := A.generic.1.2.2.2 _ hpG _ hqG
  obtain ⟨s,hs,hsp,hsu⟩ := hπ.lift p hp u (A.generic.1.1 u huG) hup
  obtain ⟨f,hf,hfix,w,hw,hwf,hwq,hws⟩ := hhom s hs q hq (by rwa [hsu])
  have hwG : π ‘ w ∈ A.G := by rwa [hws,hsu]
  have hfG : π ‘ (f ‘ p) ∈ A.G := by rwa [hfix p hp]
  have hwQ := (A.check_mem_projectionQuotient_iff hπ.maps).mpr ⟨hw,hwG⟩
  have hfQ := (A.check_mem_projectionQuotient_iff hπ.maps).mpr ⟨function_value_mem hf.1 hp,hfG⟩
  refine ⟨A.projectionQuotientAutomorphism Q π f,
    A.projectionQuotientAutomorphism_isomorphism hπ.maps hf hfix, A.check w, hwQ, ?_, ?_⟩
  · rw [A.projectionQuotientAutomorphism_check_value hπ.maps hf hp hpG]
    apply (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
    refine ⟨?_,hwQ,hfQ⟩
    rw [← A.check_kpair, A.check_mem_iff]
    exact hS.2.2 w hw _ (function_value_mem hf.1 hs) _ (function_value_mem hf.1 hp)
      hwf ((hf.2.2.2 s hs p hp).mp hsp)
  · apply (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
    refine ⟨?_,hwQ,hy⟩
    rwa [← A.check_kpair, A.check_mem_iff]

end ForcingContext
end ZFVP
