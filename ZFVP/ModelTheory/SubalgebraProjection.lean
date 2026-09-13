import ZFVP.ModelTheory.CompleteSubalgebra

/-! The projection of a Boolean condition to a complete subalgebra: the least element of the
subalgebra above it. Every nonzero element of the subalgebra below the projection meets the
condition (the reduction property). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A nonempty intersection of regular sets is regular. -/
theorem sInter_regular {P R X : V} (hX : ∀ A ∈ X, IsForcingRegular P R A) (hne : ∃ A, A ∈ X) :
    IsForcingRegular P R (⋂ˢ X) := by
  obtain ⟨A₀, hA₀⟩ := hne
  refine ⟨fun p hp ↦ (hX A₀ hA₀).1 p ((mem_sInter_iff.mp hp).2 A₀ hA₀), ?_, ?_⟩
  · intro p hp q hq hqp
    obtain ⟨hn, hh⟩ := mem_sInter_iff.mp hp
    exact mem_sInter_iff.mpr ⟨hn, fun A hA ↦ (hX A hA).2.1 p (hh A hA) q hq hqp⟩
  · intro p hp hd
    refine mem_sInter_iff.mpr ⟨isNonempty_def.mpr ⟨A₀, hA₀⟩, fun A hA ↦ ?_⟩
    apply (hX A hA).2.2 p hp
    intro q hq hqp
    obtain ⟨r, hr, hrq⟩ := hd q hq hqp
    exact ⟨r, (mem_sInter_iff.mp hr).2 A hA, hrq⟩

/-- A nonempty intersection of members of a complete subalgebra lies in it. -/
theorem IsCompleteSubalgebra.sInter_mem {P R D X : V} (hD : IsCompleteSubalgebra P R D)
    (hR : IsForcingPreorder P R) (hX : X ⊆ D) (hne : ∃ A, A ∈ X) : ⋂ˢ X ∈ D := by
  obtain ⟨A₀, hA₀⟩ := hne
  have hneg : ∀ C ∈ repl (fun A ↦ forcingNegation P R A) (by definability) X, IsForcingRegular P R C := by
    intro C hC
    obtain ⟨A, hA, rfl⟩ := (repl_spec _).mp hC
    exact forcingNegation_regular hR (hD.regular (hX A hA)).2.1
  have hj : regularJoin P R (repl (fun A ↦ forcingNegation P R A) (by definability) X) ∈ D := by
    apply hD.2.2.2
    intro C hC
    obtain ⟨A, hA, rfl⟩ := (repl_spec _).mp hC
    exact hD.2.2.1 A (hX A hA)
  have key : ⋂ˢ X = forcingNegation P R
      (regularJoin P R (repl (fun A ↦ forcingNegation P R A) (by definability) X)) := by
    ext p
    rw [mem_forcingNegation_regularJoin_iff hR hneg, mem_sInter_iff]
    constructor
    · rintro ⟨_, hh⟩
      refine ⟨(hD.regular (hX A₀ hA₀)).1 p (hh A₀ hA₀), fun C hC ↦ ?_⟩
      obtain ⟨A, hA, rfl⟩ := (repl_spec _).mp hC
      rw [forcingNegation_negation hR (hD.regular (hX A hA))]
      exact hh A hA
    · rintro ⟨_, hh⟩
      refine ⟨isNonempty_def.mpr ⟨A₀, hA₀⟩, fun A hA ↦ ?_⟩
      have := hh _ ((repl_spec _).mpr ⟨A, hA, rfl⟩)
      rwa [forcingNegation_negation hR (hD.regular (hX A hA))] at this
  rw [key]
  exact hD.2.2.1 _ hj

/-- The least member of `D` containing `b`. -/
noncomputable def subalgebraProjectionSet (D b : V) : V := ⋂ˢ {d ∈ D ; b ⊆ d}

theorem mem_subalgebraProjectionSet_iff (D b z : V) :
    z ∈ subalgebraProjectionSet D b ↔ (∃ d, d ∈ D ∧ b ⊆ d) ∧ ∀ d ∈ D, b ⊆ d → z ∈ d := by
  unfold subalgebraProjectionSet
  rw [mem_sInter_iff, isNonempty_def]
  constructor
  · rintro ⟨⟨d, hd⟩, hh⟩
    exact ⟨⟨d, mem_sep_iff.mp hd⟩, fun d hd hbd ↦ hh d (mem_sep_iff.mpr ⟨hd, hbd⟩)⟩
  · rintro ⟨⟨d, hd, hbd⟩, hh⟩
    exact ⟨⟨d, mem_sep_iff.mpr ⟨hd, hbd⟩⟩, fun d hd ↦ hh d (mem_sep_iff.mp hd).1 (mem_sep_iff.mp hd).2⟩

theorem subalgebraProjectionSet_definable (D : V) : ℒₛₑₜ-function₁[V] (subalgebraProjectionSet D) := by
  have h : ℒₛₑₜ-relation[V] (fun y b ↦ ∀ z, z ∈ y ↔ (∃ d, d ∈ D ∧ b ⊆ d) ∧ ∀ d ∈ D, b ⊆ d → z ∈ d) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = subalgebraProjectionSet D (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_subalgebraProjectionSet_iff]

section

variable {P R D : V} (hD : IsCompleteSubalgebra P R D)
include hD

theorem subset_subalgebraProjectionSet {b : V} (hb : b ⊆ P) : b ⊆ subalgebraProjectionSet D b := by
  intro p hp
  refine mem_sInter_iff.mpr ⟨isNonempty_def.mpr ⟨P, mem_sep_iff.mpr ⟨hD.2.1, hb⟩⟩, fun d hd ↦ ?_⟩
  exact (mem_sep_iff.mp hd).2 p hp

omit hD in
theorem subalgebraProjectionSet_subset {b d : V} (hd : d ∈ D) (hbd : b ⊆ d) :
    subalgebraProjectionSet D b ⊆ d := fun p hp ↦
  (mem_sInter_iff.mp hp).2 d (mem_sep_iff.mpr ⟨hd, hbd⟩)

theorem subalgebraProjectionSet_mem (hR : IsForcingPreorder P R) {b : V} (hb : b ⊆ P) :
    subalgebraProjectionSet D b ∈ D :=
  hD.sInter_mem hR (fun d hd ↦ (mem_sep_iff.mp hd).1) ⟨P, mem_sep_iff.mpr ⟨hD.2.1, hb⟩⟩

theorem subalgebraProjectionSet_mono (hR : IsForcingPreorder P R) {b c : V} (hbc : b ⊆ c)
    (hc : c ⊆ P) : subalgebraProjectionSet D b ⊆ subalgebraProjectionSet D c :=
  subalgebraProjectionSet_subset (subalgebraProjectionSet_mem hD hR hc)
    (subset_trans hbc (subset_subalgebraProjectionSet hD hc))

/-- Reduction: a nonzero member of `D` below the projection of `b` meets `b`. -/
theorem subalgebraProjectionSet_meets (hR : IsForcingPreorder P R) {b d : V}
    (hb : IsForcingRegular P R b) (hd : d ∈ D) (hdp : d ⊆ subalgebraProjectionSet D b)
    (hdne : ∃ p, p ∈ d) : ∃ p, p ∈ b ∩ d := by
  by_contra hno
  push Not at hno
  have hdis : b ∩ d = ∅ := by
    ext p
    simp only [not_mem_empty, iff_false]
    exact hno p
  have hsub : b ⊆ forcingNegation P R d :=
    (subset_forcingNegation_iff hR hb (hD.regular hd).1).mpr hdis
  have h1 : subalgebraProjectionSet D b ⊆ forcingNegation P R d :=
    subalgebraProjectionSet_subset (hD.2.2.1 d hd) hsub
  obtain ⟨p, hp⟩ := hdne
  have : p ∈ d ∩ forcingNegation P R d := mem_inter_iff.mpr ⟨hp, h1 p (hdp p hp)⟩
  rw [inter_forcingNegation_eq_empty hR (hD.regular hd).1] at this
  exact not_mem_empty this

end

end ZFVP
