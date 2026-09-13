import ZFVP.ModelTheory.ProductGenericConverseEquiv

/-! Base change: a forcing context over a ground model transports along a membership isomorphism
of ground models, and the two extensions are isomorphic membership structures compatibly with
checks. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {M M' : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure M'] [Nonempty M'] [M'↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A membership isomorphism is a membership end extension. -/
def MembershipEndExtension.ofEquiv (e : M ≃ M') (he : ∀ x y, e x ∈ e y ↔ x ∈ y) :
    MembershipEndExtension M M' where
  toFun := e
  injective := e.injective
  mem_iff := he
  endExtension := fun x y hy ↦ ⟨e.symm y, (he _ _).mp (by rw [Equiv.apply_symm_apply]; exact hy),
    (e.apply_symm_apply y).symm⟩

theorem MembershipEndExtension.ofEquiv_apply (e : M ≃ M') (he : ∀ x y, e x ∈ e y ↔ x ∈ y) (x : M) :
    MembershipEndExtension.ofEquiv e he x = e x := rfl

namespace ForcingContext

variable (Q : ForcingContext M) (e : M ≃ M') (he : ∀ x y, e x ∈ e y ↔ x ∈ y)

/-- The transported generic. -/
def baseChangeGeneric : Set M' := {y | ∃ x ∈ Q.G, y = e x}

include he in
theorem baseChangeGeneric_generic :
    IsExternalForcingGeneric (e Q.P) (e Q.R) (Q.baseChangeGeneric e) := by
  let j := MembershipEndExtension.ofEquiv e he
  have hmem : ∀ x y : M, (e x ∈ e y ↔ x ∈ y) := he
  have hkp : ∀ x y : M, e ⟨x, y⟩ₖ = ⟨e x, e y⟩ₖ := fun x y ↦ j.map_kpair x y
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact (hmem _ _).mpr (Q.generic.1.1 x hx)
  · obtain ⟨x, hx⟩ := Q.generic.1.2.1
    exact ⟨e x, x, hx, rfl⟩
  · rintro y ⟨x, hx, rfl⟩ y' hy' hyy'
    obtain ⟨x', hx', rfl⟩ := j.endExtension _ y' hy'
    rw [MembershipEndExtension.ofEquiv_apply] at hyy' ⊢
    rw [← hkp, hmem] at hyy'
    exact ⟨x', Q.generic.1.2.2.1 x hx x' hx' hyy', rfl⟩
  · rintro y ⟨x, hx, rfl⟩ y' ⟨x', hx', rfl⟩
    obtain ⟨r, hr, hr1, hr2⟩ := Q.generic.1.2.2.2 x hx x' hx'
    exact ⟨e r, ⟨r, hr, rfl⟩, by rw [← hkp, hmem]; exact hr1, by rw [← hkp, hmem]; exact hr2⟩
  · intro D' hD'
    -- pull the dense set back
    let D : M := e.symm D'
    have hDD' : e D = D' := e.apply_symm_apply D'
    have hD : ForcingDense Q.P Q.R D := by
      refine ⟨fun z hz ↦ ?_, fun p hp ↦ ?_⟩
      · have : e z ∈ D' := by rw [← hDD']; exact (hmem _ _).mpr hz
        exact (hmem _ _).mp (hD'.1 _ this)
      · obtain ⟨d', hd', hdp⟩ := hD'.2 (e p) ((hmem _ _).mpr hp)
        obtain ⟨d, _, rfl⟩ := j.endExtension _ d' (hD'.1 d' hd')
        rw [MembershipEndExtension.ofEquiv_apply] at hd' hdp
        rw [← hkp, hmem] at hdp
        refine ⟨d, ?_, hdp⟩
        rw [← hDD'] at hd'
        exact (hmem _ _).mp hd'
    obtain ⟨p, hpG, hpD⟩ := Q.generic.2 D hD
    refine ⟨e p, ⟨p, hpG, rfl⟩, ?_⟩
    rw [← hDD']
    exact (hmem _ _).mpr hpD

/-- The transported context. -/
noncomputable def baseChange : ForcingContext M' where
  P := e Q.P
  R := e Q.R
  one := e Q.one
  G := Q.baseChangeGeneric e
  order := (MembershipEndExtension.ofEquiv e he).map_forcingPreorder Q.order
  top := by
    let j := MembershipEndExtension.ofEquiv e he
    refine ⟨(he _ _).mpr Q.top.1, fun y hy ↦ ?_⟩
    obtain ⟨x, hx, rfl⟩ := j.endExtension _ y hy
    have hkp : ∀ a b : M, e ⟨a, b⟩ₖ = ⟨e a, e b⟩ₖ := fun a b ↦ j.map_kpair a b
    rw [MembershipEndExtension.ofEquiv_apply, ← hkp]
    exact (he _ _).mpr (Q.top.2 x hx)
  generic := Q.baseChangeGeneric_generic e he

theorem baseChange_P : (Q.baseChange e he).P = e Q.P := rfl
theorem baseChange_R : (Q.baseChange e he).R = e Q.R := rfl
theorem baseChange_one : (Q.baseChange e he).one = e Q.one := rfl

/-- The original extension realized inside the transported extension. -/
noncomputable def baseChangeRealization : ForcingRealization Q (Q.baseChange e he).Model where
  ground := (MembershipEndExtension.ofEquiv e he).trans (Q.baseChange e he).checkEmbedding
  genericSet := (Q.baseChange e he).genericSet
  generic_subset := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := ((Q.baseChange e he).mem_genericSet_iff y).mp hy
    exact ((Q.baseChange e he).check_mem_iff _ _).mpr ((Q.baseChange e he).generic.1.1 p hp)
  generic_mem := by
    intro p
    change (Q.baseChange e he).check (e p) ∈ (Q.baseChange e he).genericSet ↔ p ∈ Q.G
    rw [(Q.baseChange e he).check_mem_genericSet_iff]
    constructor
    · rintro ⟨x, hx, hxe⟩
      rw [e.injective hxe]
      exact hx
    · intro hp
      exact ⟨p, hp, rfl⟩

theorem baseChangeRealization_surjective : Function.Surjective (Q.baseChangeRealization e he).value :=
  ForcingRealization.value_surjective_of_generators (Q.baseChange e he) (Q.baseChangeRealization e he)
    (fun y ↦ ⟨Q.check (e.symm y), by
      rw [ForcingRealization.value_check]
      change (Q.baseChange e he).check (e (e.symm y)) = _
      rw [Equiv.apply_symm_apply]⟩)
    ⟨Q.genericSet, ForcingRealization.value_genericSet _⟩

/-- Base change: the two extensions are isomorphic. -/
noncomputable def baseChangeEquiv : Q.Model ≃ (Q.baseChange e he).Model :=
  Equiv.ofBijective (Q.baseChangeRealization e he).value
    ⟨(Q.baseChangeRealization e he).value_injective, Q.baseChangeRealization_surjective e he⟩

theorem baseChangeEquiv_mem_iff (x y : Q.Model) :
    Q.baseChangeEquiv e he x ∈ Q.baseChangeEquiv e he y ↔ x ∈ y :=
  (Q.baseChangeRealization e he).value_mem_iff x y

theorem baseChangeEquiv_check (x : M) :
    Q.baseChangeEquiv e he (Q.check x) = (Q.baseChange e he).check (e x) :=
  (Q.baseChangeRealization e he).value_check x

end ForcingContext

end ZFVP
