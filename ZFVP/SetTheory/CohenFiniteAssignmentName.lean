import ZFVP.SetTheory.CohenEnumerationName
import ZFVP.SetTheory.CohenLeastSupport
import ZFVP.SetTheory.SymmetricPairNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The Cohen-real assignment restricted to a set of coordinate labels. -/
noncomputable def cohenFiniteAssignmentName (E : V) : V :=
  repl (fun i ↦ ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName (ω : V) i), (∅ : V)⟩ₖ)
    (by definability) E

theorem mem_cohenFiniteAssignmentName (E z : V) : z ∈ cohenFiniteAssignmentName E ↔
    ∃ i ∈ E, z = ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName (ω : V) i), (∅ : V)⟩ₖ :=
  repl_spec _

instance cohenFiniteAssignmentName_definable : ℒₛₑₜ-function₁[V] cohenFiniteAssignmentName := by
  have h : ℒₛₑₜ-relation[V] (fun A E ↦ ∀ z, z ∈ A ↔
      ∃ i ∈ E, z = ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName (ω : V) i), (∅ : V)⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cohenFiniteAssignmentName (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_cohenFiniteAssignmentName]

theorem cohenFiniteAssignmentName_isName_unrestricted (E : V) :
    IsForcingName (cohenConditions (ω : V)) (cohenFiniteAssignmentName E) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨i, hi, rfl⟩ := (mem_cohenFiniteAssignmentName E z).mp hz
  exact ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName (ω : V) i), ∅, (cohen_top (ω : V)).1,
    rfl, orderedPairName_isName (cohen_top (ω : V)).1
      (checkName_isName (cohen_top (ω : V)).1 i) (cohenRealName_isName (ω : V) i)⟩

theorem cohenFiniteAssignmentName_isName {E : V} (_hEω : E ⊆ (ω : V)) :
    IsForcingName (cohenConditions (ω : V)) (cohenFiniteAssignmentName E) :=
  cohenFiniteAssignmentName_isName_unrestricted E

theorem cohenFiniteAssignmentName_subset_enumeration {E : V} (hEω : E ⊆ (ω : V)) :
    cohenFiniteAssignmentName E ⊆ cohenEnumerationName (ω : V) := by
  intro z hz
  obtain ⟨i, hi, he⟩ := (mem_cohenFiniteAssignmentName E z).mp hz
  exact (mem_cohenEnumerationName (ω : V) z).mpr ⟨i, hEω i hi, he⟩

/-- The action changes the assigned Cohen reals and preserves their ground coordinate labels. -/
theorem nameAction_cohenFiniteAssignmentName {E b : V} (hEω : E ⊆ (ω : V))
    (hb : IsInternalPermutation (ω : V) b) :
    nameAction (cohenPermutation (ω : V) b) (cohenFiniteAssignmentName E) =
      repl (fun i ↦ ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName (ω : V) (b ‘ i)), (∅ : V)⟩ₖ)
        (by definability) E := by
  have htop := forcingAutomorphism_top (cohen_poset (ω : V)) (cohen_top (ω : V))
    (cohenPermutation_automorphism hb)
  have hentry : ∀ i ∈ E,
      nameAction (cohenPermutation (ω : V) b)
        (orderedPairName ∅ (checkName ∅ i) (cohenRealName (ω : V) i)) =
      orderedPairName ∅ (checkName ∅ i) (cohenRealName (ω : V) (b ‘ i)) := by
    intro i hi
    rw [nameAction_orderedPairName (cohen_top (ω : V)).1
      (checkName_isName (cohen_top (ω : V)).1 i) (cohenRealName_isName (ω : V) i),
      htop, nameAction_checkName (cohen_top (ω : V)).1 htop i,
      nameAction_cohenRealName hb (hEω i hi)]
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨σ, p, hσp, rfl⟩ := (mem_nameAction_iff (cohenFiniteAssignmentName_isName_unrestricted E) _ z).mp hz
    obtain ⟨i, hi, he⟩ := (mem_cohenFiniteAssignmentName E _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    rw [hentry i hi, htop]
    exact (repl_spec _).mpr ⟨i, hi, rfl⟩
  · intro hz
    obtain ⟨i, hi, rfl⟩ := (repl_spec _).mp hz
    refine (mem_nameAction_iff (cohenFiniteAssignmentName_isName_unrestricted E) _ _).mpr
      ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName (ω : V) i), ∅,
        (mem_cohenFiniteAssignmentName E _).mpr ⟨i, hi, rfl⟩, ?_⟩
    rw [hentry i hi, htop]

theorem nameAction_cohenFiniteAssignmentName_fixed {E b : V} (hEω : E ⊆ (ω : V))
    (hb : IsInternalPermutation (ω : V) b) (hfix : ∀ i ∈ E, b ‘ i = i) :
    nameAction (cohenPermutation (ω : V) b) (cohenFiniteAssignmentName E) =
      cohenFiniteAssignmentName E := by
  rw [nameAction_cohenFiniteAssignmentName hEω hb]
  apply mem_ext
  intro z
  simp only [repl_spec, mem_cohenFiniteAssignmentName]
  constructor <;> rintro ⟨i, hi, he⟩ <;> refine ⟨i, hi, ?_⟩ <;>
    simpa only [hfix i hi] using he

theorem cohenFiniteAssignmentName_support {E : V}
    (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E) :
    IsCohenNameSupport (cohenFiniteAssignmentName E) E :=
  ⟨hEω, hEf, fun _b hb hfix ↦ nameAction_cohenFiniteAssignmentName_fixed hEω hb hfix⟩

theorem cohenFiniteAssignmentName_hereditarilySymmetric {E : V}
    (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E) :
    IsHereditarilySymmetricName (cohenConditions (ω : V)) (cohenGroup (ω : V))
      (cohenFilter (ω : V)) (cohenFiniteAssignmentName E) := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨cohenFiniteAssignmentName_isName_unrestricted E, ?_⟩, ?_⟩
  · apply (mem_cohenFilter_iff (ω : V) _).mpr
    refine ⟨nameStabilizer_subgroup (cohenGroup_group (ω : V)) (cohenFiniteAssignmentName_isName_unrestricted E),
      E, hEω, hEf, ?_⟩
    intro b hb hfix
    exact mem_sep_iff.mpr ⟨(mem_cohenGroup (ω : V) _).mpr ⟨b, hb, rfl⟩,
      nameAction_cohenFiniteAssignmentName_fixed hEω hb hfix⟩
  · intro σ p hσp
    obtain ⟨i, hi, he⟩ := (mem_cohenFiniteAssignmentName E _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact hereditarilySymmetric_orderedPairName (cohen_poset (ω : V)) (cohenGroup_group (ω : V))
      (cohenFilter_normal (ω : V)) (cohen_top (ω : V))
      (hereditarilySymmetric_checkName (cohen_poset (ω : V)) (cohenGroup_group (ω : V))
        (cohenFilter_normal (ω : V)) (cohen_top (ω : V)) i)
      (cohenRealName_hereditarilySymmetric (hEω i hi))

theorem nameAction_cohenFiniteAssignmentName_eq_of_agree {E a b : V}
    (hEω : E ⊆ (ω : V)) (ha : IsInternalPermutation (ω : V) a)
    (hb : IsInternalPermutation (ω : V) b) (hagree : ∀ i ∈ E, a ‘ i = b ‘ i) :
    nameAction (cohenPermutation (ω : V) a) (cohenFiniteAssignmentName E) =
      nameAction (cohenPermutation (ω : V) b) (cohenFiniteAssignmentName E) := by
  rw [nameAction_cohenFiniteAssignmentName hEω ha, nameAction_cohenFiniteAssignmentName hEω hb]
  apply mem_ext
  intro z
  simp only [repl_spec]
  constructor <;> rintro ⟨i, hi, he⟩ <;> refine ⟨i, hi, ?_⟩
  · simpa only [hagree i hi] using he
  · simpa only [hagree i hi] using he

end ZFVP

