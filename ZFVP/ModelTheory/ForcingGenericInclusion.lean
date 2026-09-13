import ZFVP.ModelTheory.ForcingRealizationGeneration
import ZFVP.SetTheory.ForcingRetraction
import ZFVP.SetTheory.DeltaOneForcingNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem MembershipEndExtension.forcingName_iff {W : Type*} [SetStructure W]
    [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (j : MembershipEndExtension V W) (P τ : V) :
    IsForcingName P τ ↔ IsForcingName (j P) (j τ) :=
  j.deltaOne_defined sigmaOneForcingNameFormula_sigmaOne piOneForcingNameFormula_piOne
    (fun v ↦ IsForcingName (v 0) (v 1)) (fun v ↦ IsForcingName (v 0) (v 1)) ![P, τ]

theorem nameValue_filter_congr {P G H τ : V} (hτ : IsForcingName P τ)
    (hGH : ∀ p ∈ P, p ∈ G ↔ p ∈ H) : nameValue G τ = nameValue H τ := by
  apply forcingName_induction P (fun τ ↦ nameValue G τ = nameValue H τ) (by definability) ?_ τ hτ
  intro σ hσ ih
  apply mem_ext
  intro z
  rw [mem_nameValue_iff, mem_nameValue_iff]
  constructor
  · rintro ⟨ν, p, hp, hνp, he⟩
    exact ⟨ν, p, (hGH p (forcingName_condition hσ hνp)).mp hp, hνp, he.trans (ih ν p hνp)⟩
  · rintro ⟨ν, p, hp, hνp, he⟩
    exact ⟨ν, p, (hGH p (forcingName_condition hσ hνp)).mpr hp, hνp, he.trans (ih ν p hνp).symm⟩

namespace ForcingContext
variable (A B : ForcingContext V)

theorem endExtension_ext {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (j k : MembershipEndExtension A.Model W) (hcheck : ∀ x : V, j (A.check x) = k (A.check x))
    (x : A.Model) : j x = k x := by
  have hgeneric : j A.genericSet = k A.genericSet := by
    apply mem_ext
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := j.endExtension A.genericSet y hy
      obtain ⟨p, hp, rfl⟩ := (A.mem_genericSet_iff z).mp hz
      rw [hcheck p]
      exact (k.mem_iff _ _).mpr ((A.check_mem_genericSet_iff p).mpr hp)
    · intro hy
      obtain ⟨z, hz, rfl⟩ := k.endExtension A.genericSet y hy
      obtain ⟨p, hp, rfl⟩ := (A.mem_genericSet_iff z).mp hz
      rw [← hcheck p]
      exact (j.mem_iff _ _).mpr ((A.check_mem_genericSet_iff p).mpr hp)
  obtain ⟨τ, rfl⟩ := A.ofName_surjective x
  rw [← A.nameValue_genericSet_check τ, j.map_nameValue, k.map_nameValue, hgeneric, hcheck τ.val]

noncomputable def restrictedGenericSet : B.Model := {p ∈ B.genericSet ; p ∈ B.check A.P}

theorem restrictedGenericSet_subset : A.restrictedGenericSet B ⊆ B.check A.P :=
  fun _ hp ↦ (mem_sep_iff.mp hp).2

theorem check_mem_restrictedGenericSet (p : V) :
    B.check p ∈ A.restrictedGenericSet B ↔ p ∈ B.G ∧ p ∈ A.P := by
  simp only [restrictedGenericSet, mem_sep_iff, B.check_mem_genericSet_iff, B.check_mem_iff]

noncomputable def restrictionRealization
    (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P) : ForcingRealization A B.Model where
  ground := B.checkEmbedding
  genericSet := A.restrictedGenericSet B
  generic_subset := A.restrictedGenericSet_subset B
  generic_mem := fun p ↦ (A.check_mem_restrictedGenericSet B p).trans (hG p).symm

noncomputable def genericInclusion
    (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P) : MembershipEndExtension A.Model B.Model :=
  (A.restrictionRealization B hG).embedding

theorem genericInclusion_check
    (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P) (x : V) :
    A.genericInclusion B hG (A.check x) = B.check x :=
  (A.restrictionRealization B hG).value_check x

theorem genericInclusion_ofName (hP : A.P ⊆ B.P)
    (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P) (τ : ForcingName A.P) :
    A.genericInclusion B hG (A.ofName τ) = B.ofName ⟨τ.val, τ.property.mono hP⟩ := by
  change nameValue (A.restrictedGenericSet B) (B.check τ.val) = _
  rw [← B.nameValue_genericSet_check ⟨τ.val, τ.property.mono hP⟩]
  apply nameValue_filter_congr ((B.checkEmbedding.forcingName_iff A.P τ.val).mp τ.property)
  intro p hp
  change p ∈ B.check A.P at hp
  change p ∈ {p ∈ B.genericSet ; p ∈ B.check A.P} ↔ p ∈ B.genericSet
  simp only [mem_sep_iff, hp, and_true]

theorem genericInclusion_genericSet
    (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P) :
    A.genericInclusion B hG A.genericSet = A.restrictedGenericSet B :=
  (A.restrictionRealization B hG).value_genericSet

end ForcingContext
end ZFVP
