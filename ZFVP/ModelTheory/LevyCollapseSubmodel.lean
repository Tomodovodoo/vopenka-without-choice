import ZFVP.ModelTheory.LevyCollapseSubgeneric
import ZFVP.ModelTheory.ForcingRealizationGeneration
import ZFVP.ModelTheory.ForcingModelNameValue
import ZFVP.SetTheory.ForcingRetraction

/-! The intermediate model `V[G_β]` inside `V[G]` for the Levy collapse: the subcollapse
context is realized in the full extension through the checks and the cut of the generic
set, so `V[G_β]` is the range of an end-extension embedding into `V[G]`, and the value of a
subcollapse name is its value as a name for the full collapse. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem MembershipEndExtension.nameClosure_subset (j : MembershipEndExtension V W) (τ : V) :
    nameClosure (j τ) ⊆ j (nameClosure τ) :=
  nameClosure_minimal (j.map_subnameClosed (nameClosure_closed τ))
    ((j.mem_iff _ _).mpr (mem_nameClosure_self τ))

theorem MembershipEndExtension.map_forcingName (j : MembershipEndExtension V W) {P τ : V}
    (hτ : IsForcingName P τ) : IsForcingName (j P) (j τ) := by
  intro σ hσ z hz
  obtain ⟨σ₀, hσ₀, rfl⟩ := j.endExtension _ σ (j.nameClosure_subset τ σ hσ)
  obtain ⟨z₀, hz₀, rfl⟩ := j.endExtension _ z hz
  obtain ⟨υ, p, hp, rfl⟩ := hτ σ₀ hσ₀ z₀ hz₀
  exact ⟨j υ, j p, (j.mem_iff _ _).mpr hp, j.map_kpair υ p⟩

/-- The value of a name over `C` does not see conditions outside `C`. -/
theorem nameValue_inter_of_name {G C τ : V} (hτ : IsForcingName C τ) :
    nameValue (G ∩ C) τ = nameValue G τ := by
  revert τ
  apply forcingName_induction C (fun τ ↦ nameValue (G ∩ C) τ = nameValue G τ) (by definability)
  intro τ hτ ih
  ext z
  rw [mem_nameValue_iff, mem_nameValue_iff]
  constructor
  · rintro ⟨σ, p, hp, hσp, rfl⟩
    exact ⟨σ, p, (mem_inter_iff.mp hp).1, hσp, ih σ p hσp⟩
  · rintro ⟨σ, p, hp, hσp, rfl⟩
    have hpC : p ∈ C := by
      obtain ⟨υ, q, hq, he⟩ := hτ τ (mem_nameClosure_self τ) _ hσp
      obtain ⟨_, rfl⟩ := kpair_iff.mp he
      exact hq
    exact ⟨σ, p, mem_inter_iff.mpr ⟨hp, hpC⟩, hσp, (ih σ p hσp).symm⟩

variable {κ : V} (β : V) [IsOrdinal β] (hβ : β ⊆ κ) {G : Set V}
  (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- `V[G_β]` realized inside `V[G]`. -/
noncomputable def levySubRealization :
    ForcingRealization (levySubContext β hβ hG) (levyContext κ hG).Model where
  ground := (levyContext κ hG).checkEmbedding
  genericSet := (levyContext κ hG).genericSet ∩ (levyContext κ hG).check (levyCollapse β)
  generic_subset := fun x hx ↦ (mem_inter_iff.mp hx).2
  generic_mem := fun p ↦ by
    change (levyContext κ hG).check p ∈ _ ↔ p ∈ levySubGeneric β G
    rw [mem_inter_iff, (levyContext κ hG).check_mem_genericSet_iff, (levyContext κ hG).check_mem_iff]
    exact Iff.rfl

theorem levySubRealization_genericSet :
    (levySubRealization β hβ hG).genericSet =
      (levyContext κ hG).genericSet ∩ (levyContext κ hG).check (levyCollapse β) := rfl

theorem levySubRealization_ground (x : V) :
    (levySubRealization β hβ hG).ground x = (levyContext κ hG).check x := rfl

theorem levySubRealization_value_ofName (τ : ForcingName (levySubContext β hβ hG).P) :
    (levySubRealization β hβ hG).value ((levySubContext β hβ hG).ofName τ) =
      (levyContext κ hG).ofName ⟨τ.val, τ.property.mono (levyCollapse_mono hβ)⟩ := by
  rw [ForcingRealization.value_ofName, levySubRealization_genericSet, levySubRealization_ground]
  have hn : IsForcingName ((levyContext κ hG).check (levyCollapse β)) ((levyContext κ hG).check τ.val) :=
    (levyContext κ hG).checkEmbedding.map_forcingName τ.property
  rw [nameValue_inter_of_name hn]
  exact (levyContext κ hG).nameValue_genericSet_check ⟨τ.val, τ.property.mono (levyCollapse_mono hβ)⟩

/-- Membership in the intermediate model `V[G_β]`. -/
def InLevySubmodel (x : (levyContext κ hG).Model) : Prop :=
  ∃ y, (levySubRealization β hβ hG).value y = x

theorem inLevySubmodel_ofName (τ : ForcingName (levySubContext β hβ hG).P) :
    InLevySubmodel β hβ hG ((levyContext κ hG).ofName ⟨τ.val, τ.property.mono (levyCollapse_mono hβ)⟩) :=
  ⟨_, levySubRealization_value_ofName β hβ hG τ⟩

theorem inLevySubmodel_iff (x : (levyContext κ hG).Model) :
    InLevySubmodel β hβ hG x ↔ ∃ τ : ForcingName (levySubContext β hβ hG).P,
      x = (levyContext κ hG).ofName ⟨τ.val, τ.property.mono (levyCollapse_mono hβ)⟩ := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨τ, rfl⟩ := (levySubContext β hβ hG).ofName_surjective y
    exact ⟨τ, levySubRealization_value_ofName β hβ hG τ⟩
  · rintro ⟨τ, rfl⟩
    exact inLevySubmodel_ofName β hβ hG τ

theorem inLevySubmodel_check (x : V) : InLevySubmodel β hβ hG ((levyContext κ hG).check x) :=
  ⟨(levySubContext β hβ hG).check x, (levySubRealization β hβ hG).value_check x⟩

end ZFVP
