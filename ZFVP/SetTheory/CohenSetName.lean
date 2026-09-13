import ZFVP.SetTheory.CohenRealNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def cohenSetName (I : V) : V :=
  repl (fun i ↦ ⟨cohenRealName I i, (∅ : V)⟩ₖ) (by definability) I

theorem mem_cohenSetName (I z : V) : z ∈ cohenSetName I ↔
    ∃ i ∈ I, z = ⟨cohenRealName I i, (∅ : V)⟩ₖ := repl_spec _

instance cohenSetName_definable : ℒₛₑₜ-function₁[V] cohenSetName := by
  have h : ℒₛₑₜ-relation[V] (fun A I ↦ ∀ z, z ∈ A ↔
      ∃ i ∈ I, z = ⟨cohenRealName I i, (∅ : V)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cohenSetName (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_cohenSetName]

theorem cohenSetName_isName (I : V) : IsForcingName (cohenConditions I) (cohenSetName I) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨i, hi, rfl⟩ := (mem_cohenSetName I z).mp hz
  exact ⟨cohenRealName I i, ∅, (cohen_top I).1, rfl, cohenRealName_isName I i⟩

theorem nameAction_cohenSetName {I π : V} (hπ : IsInternalPermutation I π) :
    nameAction (cohenPermutation I π) (cohenSetName I) = cohenSetName I := by
  have ha := cohenPermutation_automorphism hπ
  have htop := forcingAutomorphism_top (cohen_poset I) (cohen_top I) ha
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨σ, p, hσp, rfl⟩ := (mem_nameAction_iff (cohenSetName_isName I) _ z).mp hz
    obtain ⟨i, hi, he⟩ := (mem_cohenSetName I _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    rw [nameAction_cohenRealName hπ hi, htop]
    exact (mem_cohenSetName I _).mpr ⟨π ‘ i, function_value_mem hπ.1 hi, rfl⟩
  · intro hz
    obtain ⟨j, hj, rfl⟩ := (mem_cohenSetName I z).mp hz
    obtain ⟨i, hi, hij⟩ := hπ.surjective hj
    refine (mem_nameAction_iff (cohenSetName_isName I) _ _).mpr
      ⟨cohenRealName I i, ∅, (mem_cohenSetName I _).mpr ⟨i, hi, rfl⟩, ?_⟩
    rw [nameAction_cohenRealName hπ hi, hij, htop]

theorem nameStabilizer_cohenSetName (I : V) :
    nameStabilizer (cohenGroup I) (cohenSetName I) = cohenGroup I := by
  ext σ
  simp only [nameStabilizer, mem_sep_iff]
  constructor
  · exact And.left
  · intro hσ
    obtain ⟨π, hπ, rfl⟩ := (mem_cohenGroup I σ).mp hσ
    exact ⟨(mem_cohenGroup I _).mpr ⟨π, hπ, rfl⟩, nameAction_cohenSetName hπ⟩

theorem cohenSetName_hereditarilySymmetric (I : V) :
    IsHereditarilySymmetricName (cohenConditions I) (cohenGroup I) (cohenFilter I) (cohenSetName I) := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨cohenSetName_isName I, ?_⟩, ?_⟩
  · rw [nameStabilizer_cohenSetName]
    exact (cohenFilter_normal I).2.1
  · intro σ p hp
    obtain ⟨i, hi, he⟩ := (mem_cohenSetName I _).mp hp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact cohenRealName_hereditarilySymmetric hi

end ZFVP
