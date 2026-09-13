import ZFVP.ModelTheory.GroundAtomicWitnesses
import ZFVP.SetTheory.AtomicForcingSubstitution
import ZFVP.SetTheory.NameValue

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ground_atomicEquality_sound (P R σ τ : SetDomain U) {G p : V}
    (hR : IsForcingPreorder P.val R.val) (hG : IsGroundForcingGeneric U P.val R.val G)
    (hpG : p ∈ G) (hp : p ∈ atomicEquality P.val R.val σ.val τ.val) :
    nameValue G σ.val = nameValue G τ.val := by
  have h := projectedRank_induction (nameClosure σ.val) (fun x : V ↦ x) (by definability)
    (fun x ↦ x ∈ U → ∀ y ∈ U, ∀ q ∈ G, q ∈ atomicEquality P.val R.val x y →
      nameValue G x = nameValue G y) (by definability) ?_
  · exact h σ.val (mem_nameClosure_self σ.val) σ.property τ.val τ.property p hpG hp
  intro x hx ih hxU y hyU q hqG hqE
  let x' : SetDomain U := ⟨x, hxU⟩
  let y' : SetDomain U := ⟨y, hyU⟩
  apply SetTheory.mem_ext_iff.mpr
  intro z
  constructor
  · intro hz
    obtain ⟨υ, s, hsG, hυs, rfl⟩ := (mem_nameValue_iff _ _ _).mp hz
    have hυU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hυs hxU)).1
    let υ' : SetDomain U := ⟨υ, hυU⟩
    obtain ⟨r, hrG, hrq, hrs⟩ := hG.1.2.2.2 q hqG s hsG
    have hrP := hG.1.1 r hrG
    have hrE := atomicEquality_mono hR hqE hrP hrq
    have hrM := ((atomicEquality_iff_membership _ _ _ _ _ hR).mp hrE).2.1
      υ s hυs r hrP (hR.2.1 r hrP) hrs
    obtain ⟨v, hvG, ν, t, hνt, htG, he⟩ := ground_atomicMembership_witness U P R υ' y' hR hG hrG hrM
    have hνU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hνt hyU)).1
    have hv := ih υ (nameClosure_closed σ.val x hx υ (mem_domain_of_kpair_mem hυs))
      (rank_subname_lt hυs) hυU ν hνU v hvG he
    exact (mem_nameValue_iff _ _ _).mpr ⟨ν, t, htG, hνt, hv⟩
  · intro hz
    obtain ⟨ν, t, htG, hνt, rfl⟩ := (mem_nameValue_iff _ _ _).mp hz
    have hνU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hνt hyU)).1
    let ν' : SetDomain U := ⟨ν, hνU⟩
    obtain ⟨r, hrG, hrq, hrt⟩ := hG.1.2.2.2 q hqG t htG
    have hrP := hG.1.1 r hrG
    have hrE := atomicEquality_mono hR hqE hrP hrq
    have hrM := ((atomicEquality_iff_membership _ _ _ _ _ hR).mp hrE).2.2
      ν t hνt r hrP (hR.2.1 r hrP) hrt
    obtain ⟨v, hvG, υ, s, hυs, hsG, he⟩ := ground_atomicMembership_witness U P R ν' x' hR hG hrG hrM
    have hυU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hυs hxU)).1
    have hv := ih υ (nameClosure_closed σ.val x hx υ (mem_domain_of_kpair_mem hυs))
      (rank_subname_lt hυs) hυU ν hνU v hvG (atomicEquality_symm P.val R.val ν υ ▸ he)
    exact (mem_nameValue_iff _ _ _).mpr ⟨υ, s, hsG, hυs, hv.symm⟩

theorem ground_atomicMembership_sound (P R σ τ : SetDomain U) {G p : V}
    (hR : IsForcingPreorder P.val R.val) (hG : IsGroundForcingGeneric U P.val R.val G)
    (hpG : p ∈ G) (hp : p ∈ atomicMembership P.val R.val σ.val τ.val) :
    nameValue G σ.val ∈ nameValue G τ.val := by
  obtain ⟨r, hrG, ν, s, hνs, hsG, he⟩ := ground_atomicMembership_witness U P R σ τ hR hG hpG hp
  have hνU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hνs τ.property)).1
  let ν' : SetDomain U := ⟨ν, hνU⟩
  exact (mem_nameValue_iff _ _ _).mpr
    ⟨ν, s, hsG, hνs, ground_atomicEquality_sound U P R σ ν' hR hG hrG he⟩

end TransitiveZF
end ZFVP
