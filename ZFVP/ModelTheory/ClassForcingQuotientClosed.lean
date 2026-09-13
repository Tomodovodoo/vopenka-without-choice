import ZFVP.ModelTheory.ClassForcingQuotient
import ZFVP.ModelTheory.ForcingQuotientFoundation
import ZFVP.SetTheory.MembershipEndExtension

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ClassForcingQuotient

variable (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (N : V → Prop) (hnames : ∀ x, N x → IsForcingName P x)
    (hsub : ∀ τ, N τ → ∀ σ p, ⟨σ, p⟩ₖ ∈ τ → N σ)

include hsub

theorem mem_ofName_iff (τ : {x : V // N x}) (x : ClassForcingQuotient P R G hR hG.1 N hnames) :
    x ∈ ofName P R G hR hG.1 N hnames τ ↔
      ∃ σ : {x : V // N x}, ∃ p ∈ G, ⟨σ.val, p⟩ₖ ∈ τ.val ∧ x = ofName P R G hR hG.1 N hnames σ := by
  obtain ⟨υ, rfl⟩ := ofName_surjective P R G hR hG.1 N hnames x
  rw [ofName_mem_iff]
  constructor
  · intro hm
    obtain ⟨σ, p, hp, hpG, he⟩ := external_atomicMembership_witness hR hG hm
    exact ⟨⟨σ, hsub τ.val τ.property σ p hp⟩, p, hpG, hp,
      (ofName_eq_iff P R G hR hG.1 N hnames _ _).mpr he⟩
  · rintro ⟨σ, p, hpG, hp, he⟩
    have hE := (ofName_eq_iff P R G hR hG.1 N hnames _ _).mp he
    have hm : GenericMeets G (atomicMembership P R σ.val τ.val) :=
      ⟨p, hpG, atomicMembership_of_pair hR (hG.1.1 p hpG) hp⟩
    exact genericMeets_membership_subst_left hR hG.1 (atomicEquality_symm P R υ.val σ.val ▸ hE) hm

theorem endExtension (x : ClassForcingQuotient P R G hR hG.1 N hnames)
    (y : ForcingQuotient P R G hR hG.1) (hy : y ∈ x.val) :
    ∃ z, z ∈ x ∧ y = z.val := by
  obtain ⟨τ, rfl⟩ := ofName_surjective P R G hR hG.1 N hnames x
  obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 y
  obtain ⟨ν, p, hpG, hp, he⟩ :=
    (forcingQuotientMk_mem_subname_iff P R G hR hG σ ⟨τ.val, hnames τ.val τ.property⟩).mp hy
  let ν' : {x : V // N x} := ⟨ν.val, hsub τ.val τ.property ν.val p hp⟩
  refine ⟨ofName P R G hR hG.1 N hnames ν', ?_, he⟩
  exact (ofName_mem_iff P R G hR hG.1 N hnames _ _).mpr
    ⟨p, hpG, atomicMembership_of_pair hR (hG.1.1 p hpG) hp⟩

def inclusion : MembershipEndExtension (ClassForcingQuotient P R G hR hG.1 N hnames)
    (ForcingQuotient P R G hR hG.1) where
  toFun := Subtype.val
  injective := fun _ _ h ↦ Subtype.ext h
  mem_iff := fun _ _ ↦ Iff.rfl
  endExtension := endExtension P R G hR hG N hnames hsub

theorem extensionality (x y : ClassForcingQuotient P R G hR hG.1 N hnames)
    (he : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  apply Subtype.ext
  apply forcingQuotient_extensionality P R G hR hG
  intro z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := endExtension P R G hR hG N hnames hsub x z hz
    exact (he w).mp hw
  · intro hz
    obtain ⟨w, hw, rfl⟩ := endExtension P R G hR hG N hnames hsub y z hz
    exact (he w).mpr hw

theorem foundation (x : ClassForcingQuotient P R G hR hG.1 N hnames) (hx : ∃ y, y ∈ x) :
    ∃ y, y ∈ x ∧ ∀ z, z ∈ x → z ∉ y := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨y, hy, hmin⟩ := forcingQuotient_foundation P R G hR hG x.val ⟨a.val, ha⟩
  obtain ⟨z, hz, rfl⟩ := endExtension P R G hR hG N hnames hsub x y hy
  exact ⟨z, hz, fun w hw ↦ hmin w.val hw⟩

end ClassForcingQuotient
end ZFVP
