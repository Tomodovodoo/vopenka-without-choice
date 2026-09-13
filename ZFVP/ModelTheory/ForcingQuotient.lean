import ZFVP.ModelTheory.GenericRegularForcing
import ZFVP.SetTheory.AtomicForcingSubstitution

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

abbrev ForcingName (P : V) := {τ : V // IsForcingName P τ}

theorem genericMeets_membership_subst_left {P R σ σ' τ : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hG : IsExternalForcingFilter P R G)
    (he : GenericMeets G (atomicEquality P R σ σ')) (hm : GenericMeets G (atomicMembership P R σ τ)) :
    GenericMeets G (atomicMembership P R σ' τ) := by
  obtain ⟨p, hpG, hpE⟩ := he
  obtain ⟨q, hqG, hqM⟩ := hm
  obtain ⟨r, hrG, hrp, hrq⟩ := hG.2.2.2 p hpG q hqG
  exact ⟨r, hrG, atomicMembership_subst_left hR
    (atomicEquality_mono hR hpE (hG.1 r hrG) hrp) (atomicMembership_mono hR hqM (hG.1 r hrG) hrq)⟩

theorem genericMeets_membership_subst_right {P R σ τ τ' : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hG : IsExternalForcingFilter P R G)
    (he : GenericMeets G (atomicEquality P R τ τ')) (hm : GenericMeets G (atomicMembership P R σ τ)) :
    GenericMeets G (atomicMembership P R σ τ') := by
  obtain ⟨p, hpG, hpE⟩ := he
  obtain ⟨q, hqG, hqM⟩ := hm
  obtain ⟨r, hrG, hrp, hrq⟩ := hG.2.2.2 p hpG q hqG
  exact ⟨r, hrG, atomicMembership_subst_right hR
    (atomicEquality_mono hR hpE (hG.1 r hrG) hrp) (atomicMembership_mono hR hqM (hG.1 r hrG) hrq)⟩

theorem genericMeets_membership_congr {P R σ σ' τ τ' : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hG : IsExternalForcingFilter P R G)
    (hσ : GenericMeets G (atomicEquality P R σ σ')) (hτ : GenericMeets G (atomicEquality P R τ τ')) :
    GenericMeets G (atomicMembership P R σ τ) ↔ GenericMeets G (atomicMembership P R σ' τ') := by
  constructor
  · intro hm
    exact genericMeets_membership_subst_right hR hG hτ (genericMeets_membership_subst_left hR hG hσ hm)
  · intro hm
    have hσ' : GenericMeets G (atomicEquality P R σ' σ) := atomicEquality_symm P R σ σ' ▸ hσ
    have hτ' : GenericMeets G (atomicEquality P R τ' τ) := atomicEquality_symm P R τ τ' ▸ hτ
    exact genericMeets_membership_subst_right hR hG hτ' (genericMeets_membership_subst_left hR hG hσ' hm)

def forcingNameSetoid (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) : Setoid (ForcingName P) where
  r σ τ := GenericMeets G (atomicEquality P R σ.val τ.val)
  iseqv := {
    refl := fun σ ↦ by
      obtain ⟨p, hpG⟩ := hG.2.1
      exact ⟨p, hpG, (atomicEquality_refl hR σ.val).symm ▸ hG.1 p hpG⟩
    symm := fun {σ τ} h ↦ atomicEquality_symm P R σ.val τ.val ▸ h
    trans := fun {σ τ υ} hστ hτυ ↦ by
      obtain ⟨p, hpG, hpE⟩ := hστ
      obtain ⟨q, hqG, hqE⟩ := hτυ
      obtain ⟨r, hrG, hrp, hrq⟩ := hG.2.2.2 p hpG q hqG
      exact ⟨r, hrG, atomicEquality_trans hR σ.val τ.val υ.val r
        (atomicEquality_mono hR hpE (hG.1 r hrG) hrp) (atomicEquality_mono hR hqE (hG.1 r hrG) hrq)⟩ }

def ForcingQuotient (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) := Quotient (forcingNameSetoid P R G hR hG)

def forcingQuotientMk (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) (σ : ForcingName P) : ForcingQuotient P R G hR hG :=
  Quotient.mk _ σ

instance forcingQuotient_nonempty (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) : Nonempty (ForcingQuotient P R G hR hG) :=
  ⟨forcingQuotientMk P R G hR hG ⟨∅, empty_forcingName P⟩⟩

instance forcingQuotient_setStructure (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) : SetStructure (ForcingQuotient P R G hR hG) where
  mem τ σ := Quotient.liftOn₂ σ τ (fun σ τ ↦ GenericMeets G (atomicMembership P R σ.val τ.val))
    (fun _ _ _ _ hσ hτ ↦ propext (genericMeets_membership_congr hR hG hσ hτ))

theorem forcingQuotientMk_eq_iff (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) (σ τ : ForcingName P) :
    forcingQuotientMk P R G hR hG σ = forcingQuotientMk P R G hR hG τ ↔
      GenericMeets G (atomicEquality P R σ.val τ.val) :=
  ⟨Quotient.exact, fun h ↦ Quotient.sound (s := forcingNameSetoid P R G hR hG) h⟩

theorem forcingQuotientMk_mem_iff (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) (σ τ : ForcingName P) :
    forcingQuotientMk P R G hR hG σ ∈ forcingQuotientMk P R G hR hG τ ↔
      GenericMeets G (atomicMembership P R σ.val τ.val) := Iff.rfl

theorem forcingQuotientMk_surjective (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) : Function.Surjective (forcingQuotientMk P R G hR hG) := by
  intro x
  exact Quotient.inductionOn x (fun σ ↦ ⟨σ, rfl⟩)

end ZFVP
