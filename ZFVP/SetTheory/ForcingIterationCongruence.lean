import ZFVP.SetTheory.ForcingIterationLocality

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingIterationSystem.congr {θ P R π E L t P' R' π' E' L' t' : V}
    (h : IsForcingIterationSystem θ P R π E L t)
    (hP : ∀ i ∈ θ, P ‘ i = P' ‘ i) (hR : ∀ i ∈ θ, R ‘ i = R' ‘ i)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, π ‘ ⟨i, j⟩ₖ = π' ‘ ⟨i, j⟩ₖ)
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, E ‘ ⟨i, j⟩ₖ = E' ‘ ⟨i, j⟩ₖ)
    (hL : ∀ i ∈ θ, ∀ j ∈ θ, L ‘ ⟨i, j⟩ₖ = L' ‘ ⟨i, j⟩ₖ)
    (ht : ∀ i ∈ θ, t ‘ i = t' ‘ i) :
    IsForcingIterationSystem θ P' R' π' E' L' t' := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_⟩⟩
  · intro i hi j hj hij
    simpa only [
      hP i hi, hP j hj, hR i hi, hR j hj,
      ht i hi, ht j hj, hπ i hi i hi, hπ i hi j hj,
      hπ j hj i hi, hπ j hj j hj, hE i hi i hi, hE i hi j hj,
      hE j hj i hi, hE j hj j hj, hL i hi i hi, hL i hi j hj,
      hL j hj i hi, hL j hj j hj] using h.split.projMaps i hi j hj hij
  · intro i hi j hj hij
    simpa only [
      hP i hi, hP j hj, hR i hi, hR j hj,
      ht i hi, ht j hj, hπ i hi i hi, hπ i hi j hj,
      hπ j hj i hi, hπ j hj j hj, hE i hi i hi, hE i hi j hj,
      hE j hj i hi, hE j hj j hj, hL i hi i hi, hL i hi j hj,
      hL j hj i hi, hL j hj j hj] using h.split.secMaps i hi j hj hij
  · intro i hi
    simpa only [
      hP i hi, hR i hi, ht i hi, hπ i hi i hi,
      hE i hi i hi, hL i hi i hi] using h.split.secId i hi
  · intro i hi j hj k hk hij hjk
    simpa only [
      hP i hi, hP j hj, hP k hk, hR i hi,
      hR j hj, hR k hk, ht i hi, ht j hj,
      ht k hk, hπ i hi i hi, hπ i hi j hj, hπ i hi k hk,
      hπ j hj i hi, hπ j hj j hj, hπ j hj k hk, hπ k hk i hi,
      hπ k hk j hj, hπ k hk k hk, hE i hi i hi, hE i hi j hj,
      hE i hi k hk, hE j hj i hi, hE j hj j hj, hE j hj k hk,
      hE k hk i hi, hE k hk j hj, hE k hk k hk, hL i hi i hi,
      hL i hi j hj, hL i hi k hk, hL j hj i hi, hL j hj j hj,
      hL j hj k hk, hL k hk i hi, hL k hk j hj, hL k hk k hk] using h.split.projComp i hi j hj k hk hij hjk
  · intro i hi j hj k hk hij hjk
    simpa only [
      hP i hi, hP j hj, hP k hk, hR i hi,
      hR j hj, hR k hk, ht i hi, ht j hj,
      ht k hk, hπ i hi i hi, hπ i hi j hj, hπ i hi k hk,
      hπ j hj i hi, hπ j hj j hj, hπ j hj k hk, hπ k hk i hi,
      hπ k hk j hj, hπ k hk k hk, hE i hi i hi, hE i hi j hj,
      hE i hi k hk, hE j hj i hi, hE j hj j hj, hE j hj k hk,
      hE k hk i hi, hE k hk j hj, hE k hk k hk, hL i hi i hi,
      hL i hi j hj, hL i hi k hk, hL j hj i hi, hL j hj j hj,
      hL j hj k hk, hL k hk i hi, hL k hk j hj, hL k hk k hk] using h.split.secComp i hi j hj k hk hij hjk
  · intro i hi j hj hij
    simpa only [
      hP i hi, hP j hj, hR i hi, hR j hj,
      ht i hi, ht j hj, hπ i hi i hi, hπ i hi j hj,
      hπ j hj i hi, hπ j hj j hj, hE i hi i hi, hE i hi j hj,
      hE j hj i hi, hE j hj j hj, hL i hi i hi, hL i hi j hj,
      hL j hj i hi, hL j hj j hj] using h.split.retraction i hi j hj hij
  · intro i hi
    simpa only [
      hP i hi, hR i hi, ht i hi, hπ i hi i hi,
      hE i hi i hi, hL i hi i hi] using h.order.preorder i hi
  · intro i hi j hj hij
    simpa only [
      hP i hi, hP j hj, hR i hi, hR j hj,
      ht i hi, ht j hj, hπ i hi i hi, hπ i hi j hj,
      hπ j hj i hi, hπ j hj j hj, hE i hi i hi, hE i hi j hj,
      hE j hj i hi, hE j hj j hj, hL i hi i hi, hL i hi j hj,
      hL j hj i hi, hL j hj j hj] using h.order.projMono i hi j hj hij
  · intro i hi j hj hij
    simpa only [
      hP i hi, hP j hj, hR i hi, hR j hj,
      ht i hi, ht j hj, hπ i hi i hi, hπ i hi j hj,
      hπ j hj i hi, hπ j hj j hj, hE i hi i hi, hE i hi j hj,
      hE j hj i hi, hE j hj j hj, hL i hi i hi, hL i hi j hj,
      hL j hj i hi, hL j hj j hj] using h.order.below i hi j hj hij
  · intro i hi j hj hij
    simpa only [
      hP i hi, hP j hj, hR i hi, hR j hj,
      ht i hi, ht j hj, hπ i hi i hi, hπ i hi j hj,
      hπ j hj i hi, hπ j hj j hj, hE i hi i hi, hE i hi j hj,
      hE j hj i hi, hE j hj j hj, hL i hi i hi, hL i hi j hj,
      hL j hj i hi, hL j hj j hj] using h.functions.projection i hi j hj hij
  · intro i hi j hj hij
    simpa only [
      hP i hi, hP j hj, hR i hi, hR j hj,
      ht i hi, ht j hj, hπ i hi i hi, hπ i hi j hj,
      hπ j hj i hi, hπ j hj j hj, hE i hi i hi, hE i hi j hj,
      hE j hj i hi, hE j hj j hj, hL i hi i hi, hL i hi j hj,
      hL j hj i hi, hL j hj j hj] using h.functions.sectionMap i hi j hj hij
  · intro i hi
    simpa only [
      hP i hi, hR i hi, ht i hi, hπ i hi i hi,
      hE i hi i hi, hL i hi i hi] using h.tops.top i hi
  · intro i hi j hj hij
    simpa only [
      hP i hi, hP j hj, hR i hi, hR j hj,
      ht i hi, ht j hj, hπ i hi i hi, hπ i hi j hj,
      hπ j hj i hi, hπ j hj j hj, hE i hi i hi, hE i hi j hj,
      hE j hj i hi, hE j hj j hj, hL i hi i hi, hL i hi j hj,
      hL j hj i hi, hL j hj j hj] using h.tops.projTop i hi j hj hij
  · intro i hi j hj hij
    simpa only [
      hP i hi, hP j hj, hR i hi, hR j hj,
      ht i hi, ht j hj, hπ i hi i hi, hπ i hi j hj,
      hπ j hj i hi, hπ j hj j hj, hE i hi i hi, hE i hi j hj,
      hE j hj i hi, hE j hj j hj, hL i hi i hi, hL i hi j hj,
      hL j hj i hi, hL j hj j hj] using h.tops.secTop i hi j hj hij
  · intro i hi j hj hij
    simpa only [
      hP i hi, hP j hj, hR i hi, hR j hj,
      ht i hi, ht j hj, hπ i hi i hi, hπ i hi j hj,
      hπ j hj i hi, hπ j hj j hj, hE i hi i hi, hE i hi j hj,
      hE j hj i hi, hE j hj j hj, hL i hi i hi, hL i hi j hj,
      hL j hj i hi, hL j hj j hj] using h.lifts.lift i hi j hj hij
  · intro i hi j hj k hk hij hjk
    simpa only [
      hP i hi, hP j hj, hP k hk, hR i hi,
      hR j hj, hR k hk, ht i hi, ht j hj,
      ht k hk, hπ i hi i hi, hπ i hi j hj, hπ i hi k hk,
      hπ j hj i hi, hπ j hj j hj, hπ j hj k hk, hπ k hk i hi,
      hπ k hk j hj, hπ k hk k hk, hE i hi i hi, hE i hi j hj,
      hE i hi k hk, hE j hj i hi, hE j hj j hj, hE j hj k hk,
      hE k hk i hi, hE k hk j hj, hE k hk k hk, hL i hi i hi,
      hL i hi j hj, hL i hi k hk, hL j hj i hi, hL j hj j hj,
      hL j hj k hk, hL k hk i hi, hL k hk j hj, hL k hk k hk] using h.lifts.commute i hi j hj k hk hij hjk
  · intro i hi k hk j hj hik hkj
    simpa only [
      hP i hi, hP k hk, hP j hj, hR i hi,
      hR k hk, hR j hj, ht i hi, ht k hk,
      ht j hj, hπ i hi i hi, hπ i hi k hk, hπ i hi j hj,
      hπ k hk i hi, hπ k hk k hk, hπ k hk j hj, hπ j hj i hi,
      hπ j hj k hk, hπ j hj j hj, hE i hi i hi, hE i hi k hk,
      hE i hi j hj, hE k hk i hi, hE k hk k hk, hE k hk j hj,
      hE j hj i hi, hE j hj k hk, hE j hj j hj, hL i hi i hi,
      hL i hi k hk, hL i hi j hj, hL k hk i hi, hL k hk k hk,
      hL k hk j hj, hL j hj i hi, hL j hj k hk, hL j hj j hj] using h.compatible.compatible i hi k hk j hj hik hkj

end ZFVP
