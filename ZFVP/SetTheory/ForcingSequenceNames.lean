import ZFVP.SetTheory.ForcingPairNames
import ZFVP.SetTheory.CheckNames
import ZFVP.SetTheory.FunctionUnion

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsNameSequence (P s : V) : Prop := ∀ i ∈ domain s, IsForcingName P (s ‘ i)

instance isNameSequence_definable : ℒₛₑₜ-relation[V] IsNameSequence := by
  unfold IsNameSequence
  definability

noncomputable def sequenceName (one s : V) : V :=
  repl (fun i ↦ ⟨orderedPairName one (checkName one i) (s ‘ i), one⟩ₖ)
    (by definability) (domain s)

theorem mem_sequenceName (one s z : V) : z ∈ sequenceName one s ↔
    ∃ i ∈ domain s, z = ⟨orderedPairName one (checkName one i) (s ‘ i), one⟩ₖ := repl_spec _

instance sequenceName_definable : ℒₛₑₜ-function₂[V] sequenceName := by
  have h : ℒₛₑₜ-relation₃[V] (fun t one s ↦ ∀ z, z ∈ t ↔
      ∃ i ∈ domain s, z = ⟨orderedPairName one (checkName one i) (s ‘ i), one⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = sequenceName (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_sequenceName]

theorem sequenceName_isName {P one s : V} (hone : one ∈ P) (hs : IsNameSequence P s) :
    IsForcingName P (sequenceName one s) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨i, hi, rfl⟩ := (mem_sequenceName _ _ _).mp hz
  exact ⟨orderedPairName one (checkName one i) (s ‘ i), one, hone, rfl,
    orderedPairName_isName hone (checkName_isName hone i) (hs i hi)⟩

theorem IsNameSequence.restrict {P s A : V} [IsFunction s] (hs : IsNameSequence P s)
    (hA : A ⊆ domain s) : IsNameSequence P (s ↾ A) := by
  intro i hi
  have hiA : i ∈ A := by
    obtain ⟨x, hix⟩ := mem_domain_iff.mp hi
    exact (kpair_mem_restrict_iff.mp hix).2
  rw [value_restrict (hA i hiA) hiA]
  exact hs i (hA i hiA)

end ZFVP
