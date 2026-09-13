import ZFVP.ModelTheory.GroundForcingGeneric
import ZFVP.ModelTheory.TransitiveZFAtomicForcing
import ZFVP.SetTheory.AtomicWitnesses

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem atomicMembershipWitnesses_val (P R σ τ : SetDomain U) :
    (atomicMembershipWitnesses P R σ τ).val =
      atomicMembershipWitnesses P.val R.val σ.val τ.val := by
  unfold atomicMembershipWitnesses
  apply sep_val U
  intro r _
  apply exists_pair_mem_val_iff U τ
  intro ν s
  rw [← atomicEquality_val U]
  simp only [← kpair_mem_val_iff U]
  rfl

theorem ground_atomicMembership_witness (P R σ τ : SetDomain U) {G p : V}
    (hR : IsForcingPreorder P.val R.val) (hG : IsGroundForcingGeneric U P.val R.val G)
    (hpG : p ∈ G) (hp : p ∈ atomicMembership P.val R.val σ.val τ.val) :
    ∃ r ∈ G, ∃ ν s, ⟨ν, s⟩ₖ ∈ τ.val ∧ s ∈ G ∧ r ∈ atomicEquality P.val R.val σ.val ν := by
  let p' : SetDomain U := ⟨p, (inferInstance : IsTransitive U).mem_trans (hG.1.1 p hpG) P.property⟩
  have hd : ForcingDenseBelow P.val R.val (atomicMembershipWitnesses P R σ τ).val p'.val := by
    rw [atomicMembershipWitnesses_val U]
    exact atomicMembershipWitnesses_dense hp
  obtain ⟨r, hrG, hrW⟩ := groundForcingGeneric_meets_denseBelow U P R hR hG
    (atomicMembershipWitnesses P R σ τ) p' hpG hd
  rw [atomicMembershipWitnesses_val U] at hrW
  obtain ⟨_, ν, s, hs, hrs, he⟩ := (mem_atomicMembershipWitnesses_iff _ _ _ _ _).mp hrW
  exact ⟨r, hrG, ν, s, hs, hG.1.2.2.1 r hrG s (forcingOrder_right_mem hR hrs) hrs, he⟩

end TransitiveZF
end ZFVP
