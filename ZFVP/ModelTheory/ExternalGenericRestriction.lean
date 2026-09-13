import ZFVP.ModelTheory.ForcingModel
import ZFVP.ModelTheory.ForcingQuotientValuation

/-! Restrict an external generic to a transitive ground model and compare its name quotient. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem externalForcingGeneric_restrict (P R : SetDomain U) {G : Set V}
    (hG : IsExternalForcingGeneric P.val R.val G) :
    IsExternalForcingGeneric P R {p : SetDomain U | p.val ∈ G} := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    exact hG.1.1 p.val hp
  · obtain ⟨p, hp⟩ := hG.1.2.1
    exact ⟨⟨p, (inferInstance : IsTransitive U).mem_trans (hG.1.1 p hp) P.property⟩, hp⟩
  · intro p hp q hq hpq
    exact hG.1.2.2.1 p.val hp q.val hq ((kpair_mem_val_iff U p q R).mp hpq)
  · intro p hp q hq
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p.val hp q.val hq
    let r' : SetDomain U := ⟨r, (inferInstance : IsTransitive U).mem_trans (hG.1.1 r hr) P.property⟩
    exact ⟨r', hr, (kpair_mem_val_iff U r' p R).mpr hrp, (kpair_mem_val_iff U r' q R).mpr hrq⟩
  · intro D hD
    obtain ⟨p, hpG, hpD⟩ := hG.2 D.val ((forcingDense_iff U P R D).mp hD)
    exact ⟨⟨p, (inferInstance : IsTransitive U).mem_trans (hG.1.1 p hpG) P.property⟩, hpG, hpD⟩

def externalForcingContext (P R one : SetDomain U) (G : Set V)
    (hR : IsForcingPreorder P.val R.val) (hone : IsForcingTop P.val R.val one.val)
    (hG : IsExternalForcingGeneric P.val R.val G) : ForcingContext (SetDomain U) where
  P := P
  R := R
  one := one
  G := {p : SetDomain U | p.val ∈ G}
  order := (forcingPreorder_iff U P R).mpr hR
  top := (forcingTop_iff U P R one).mpr hone
  generic := externalForcingGeneric_restrict U P R hG

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem genericMeets_restrict_iff (G : Set V) (A : SetDomain U) :
    GenericMeets {p : SetDomain U | p.val ∈ G} A ↔ GenericMeets G A.val := by
  constructor
  · rintro ⟨p, hpG, hpA⟩
    exact ⟨p.val, hpG, hpA⟩
  · rintro ⟨p, hpG, hpA⟩
    exact ⟨⟨p, (inferInstance : IsTransitive U).mem_trans hpA A.property⟩, hpG, hpA⟩

theorem genericMeets_atomicEquality_restrict_iff (P R σ τ : SetDomain U) (G : Set V) :
    GenericMeets {p : SetDomain U | p.val ∈ G} (atomicEquality P R σ τ) ↔
      GenericMeets G (atomicEquality P.val R.val σ.val τ.val) := by
  rw [genericMeets_restrict_iff U, atomicEquality_val U]

theorem genericMeets_atomicMembership_restrict_iff (P R σ τ : SetDomain U) (G : Set V) :
    GenericMeets {p : SetDomain U | p.val ∈ G} (atomicMembership P R σ τ) ↔
      GenericMeets G (atomicMembership P.val R.val σ.val τ.val) := by
  rw [genericMeets_restrict_iff U, atomicMembership_val U]

end TransitiveZF
end ZFVP
