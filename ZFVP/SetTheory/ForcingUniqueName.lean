import ZFVP.SetTheory.ForcingNames
import ZFVP.SetTheory.Collection
import ZFVP.SetTheory.LeastOrdinalChoice
import ZFVP.SetTheory.ForcingUnionName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingWitnessBound (P : V) (F : V → V → V) (a α : V) : Prop :=
  ∀ p ∈ P, (∃ ν, IsForcingName P ν ∧ p ∈ F a ν) →
    ∃ ν ∈ hierarchy α, IsForcingName P ν ∧ p ∈ F a ν

theorem forcingWitnessBound_definable (P : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ℒₛₑₜ-relation (IsForcingWitnessBound P F) := by
  unfold IsForcingWitnessBound
  definability

theorem forcingWitnessBound_exists (P : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (a : V) :
    ∃ α, IsOrdinal α ∧ IsForcingWitnessBound P F a α := by
  let D := {p ∈ P ; ∃ ν, IsForcingName P ν ∧ p ∈ F a ν}
  obtain ⟨B, hB⟩ := collection D (fun p ν ↦ IsForcingName P ν ∧ p ∈ F a ν)
    (by definability) (fun p hp ↦ (mem_sep_iff.mp hp).2)
  refine ⟨rank B, inferInstance, ?_⟩
  intro p hp hex
  obtain ⟨ν, hν, hn, hf⟩ := hB p (mem_sep_iff.mpr ⟨hp, hex⟩)
  exact ⟨ν, subset_hierarchy_rank B ν hν, hn, hf⟩

noncomputable def forcingWitnessBound (P : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (a : V) : V :=
  leastOrdinalOrZero (IsForcingWitnessBound P F) (forcingWitnessBound_definable P F hF) a

instance forcingWitnessBound_function_definable (P : V) (F : V → V → V)
    (hF : ℒₛₑₜ-function₂ F) : ℒₛₑₜ-function₁ (forcingWitnessBound P F hF) := by
  unfold forcingWitnessBound
  infer_instance

theorem forcingWitnessBound_spec (P : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (a : V) :
    IsForcingWitnessBound P F a (forcingWitnessBound P F hF a) :=
  (leastOrdinalOrZero_spec _ _ a (forcingWitnessBound_exists P F hF a)).2.1

/-- Collect all bounded witnesses with their witnessing conditions. This
construction makes no selection from a family of names. -/
noncomputable def forcingWitnessName (P : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (a : V) : V :=
  {z ∈ hierarchy (forcingWitnessBound P F hF a) ×ˢ P ;
    IsForcingName P (kpair.π₁ z) ∧ kpair.π₂ z ∈ F a (kpair.π₁ z)}

instance forcingWitnessName_definable (P : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ℒₛₑₜ-function₁ (forcingWitnessName P F hF) := by
  have hd : ℒₛₑₜ-relation (fun X a : V ↦ ∀ z, z ∈ X ↔
      z ∈ hierarchy (forcingWitnessBound P F hF a) ×ˢ P ∧
        IsForcingName P (kpair.π₁ z) ∧ kpair.π₂ z ∈ F a (kpair.π₁ z)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  rw [mem_ext_iff]
  simp only [forcingWitnessName, mem_sep_iff]
  rfl

theorem mem_forcingWitnessName_iff (P : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (a ν p : V) :
    ⟨ν, p⟩ₖ ∈ forcingWitnessName P F hF a ↔
      ν ∈ hierarchy (forcingWitnessBound P F hF a) ∧ p ∈ P ∧ IsForcingName P ν ∧ p ∈ F a ν := by
  simp [forcingWitnessName, and_assoc]

theorem forcingWitnessName_isName (P : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (a : V) :
    IsForcingName P (forcingWitnessName P F hF a) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨ν, _, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact ⟨ν, p, hp, rfl, ((mem_forcingWitnessName_iff P F hF a ν p).mp hz).2.2.1⟩

noncomputable def forcingUniqueName (P R : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (a : V) : V :=
  forcingUnionName P R (forcingWitnessName P F hF a)

instance forcingUniqueName_definable (P R : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ℒₛₑₜ-function₁ (forcingUniqueName P R F hF) := by
  have hd : ℒₛₑₜ-relation (fun X a : V ↦ ∀ z, z ∈ X ↔
      z ∈ nameClosure (forcingWitnessName P F hF a) ×ˢ P ∧
        ∃ σ s t, ⟨σ, s⟩ₖ ∈ forcingWitnessName P F hF a ∧
          ⟨kpair.π₁ z, t⟩ₖ ∈ σ ∧ ⟨kpair.π₂ z, s⟩ₖ ∈ R ∧ ⟨kpair.π₂ z, t⟩ₖ ∈ R) := by definability
  apply Language.Definable.of_iff hd
  intro v
  rw [mem_ext_iff]
  simp only [forcingUniqueName, forcingUnionName, mem_sep_iff]
  rfl

theorem forcingUniqueName_isName (P R : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (a : V) :
    IsForcingName P (forcingUniqueName P R F hF a) :=
  forcingUnionName_isName (forcingWitnessName_isName P F hF a)

end ZFVP
