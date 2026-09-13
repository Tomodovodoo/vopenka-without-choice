import ZFVP.SetTheory.ForcingPullbackOrder
import ZFVP.ModelTheory.ForcingGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def forcingPullbackGeneric (Q π : V) (G : Set V) : Set V :=
  {q | q ∈ Q ∧ π ‘ q ∈ G}

theorem forcingPullbackGeneric_filter {P R Q π : V} {G : Set V}
    (hπ : π ∈ P ^ Q) (hs : ∀ p ∈ P, ∃ q ∈ Q, π ‘ q = p)
    (hG : IsExternalForcingFilter P R G) :
    IsExternalForcingFilter Q (forcingPullbackOrder Q R π) (forcingPullbackGeneric Q π G) := by
  refine ⟨fun _ h ↦ h.1, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hG.2.1
    obtain ⟨q, hq, he⟩ := hs p (hG.1 p hp)
    exact ⟨q, hq, he.symm ▸ hp⟩
  · intro p hp q hq hpq
    exact ⟨hq, hG.2.2.1 _ hp.2 _ (function_value_mem hπ hq)
      ((mem_forcingPullbackOrder_iff _ _ _ _ _).mp hpq).2.2⟩
  · intro p hp q hq
    obtain ⟨r, hr, hrp, hrq⟩ := hG.2.2.2 _ hp.2 _ hq.2
    obtain ⟨s, hsQ, he⟩ := hs r (hG.1 r hr)
    refine ⟨s, ⟨hsQ, he.symm ▸ hr⟩,
      (mem_forcingPullbackOrder_iff _ _ _ _ _).mpr ⟨hsQ, hp.1, ?_⟩,
      (mem_forcingPullbackOrder_iff _ _ _ _ _).mpr ⟨hsQ, hq.1, ?_⟩⟩ <;> rwa [he]

theorem forcingPullbackGeneric_generic {P R Q π : V} {G : Set V}
    (hπ : π ∈ P ^ Q) (hs : ∀ p ∈ P, ∃ q ∈ Q, π ‘ q = p)
    (hG : IsExternalForcingGeneric P R G) :
    IsExternalForcingGeneric Q (forcingPullbackOrder Q R π) (forcingPullbackGeneric Q π G) := by
  refine ⟨forcingPullbackGeneric_filter hπ hs hG.1, ?_⟩
  intro D hD
  let I := repl (fun q ↦ π ‘ q) (by definability) D
  have hI : ForcingDense P R I := by
    constructor
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := (repl_spec (by definability)).mp hp
      exact function_value_mem hπ (hD.1 q hq)
    · intro p hp
      obtain ⟨q, hq, he⟩ := hs p hp
      obtain ⟨r, hr, hrq⟩ := hD.2 q hq
      refine ⟨π ‘ r, (repl_spec (by definability)).mpr ⟨r, hr, rfl⟩, ?_⟩
      simpa only [he] using ((mem_forcingPullbackOrder_iff _ _ _ _ _).mp hrq).2.2
  obtain ⟨p, hpG, hpI⟩ := hG.2 I hI
  obtain ⟨q, hq, rfl⟩ := (repl_spec (by definability)).mp hpI
  exact ⟨q, ⟨hD.1 q hq, hpG⟩, hq⟩

end ZFVP
