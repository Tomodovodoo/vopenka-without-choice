import ZFVP.SetTheory.BooleanCompletion

/-! The complete Boolean algebra of regular subsets of a forcing preorder: meets are
intersections, joins are regular joins, complements are forcing negations. Distributivity of
meets over arbitrary joins, de Morgan laws, and the order/disjointness dictionary. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem mem_regularJoin_iff (P R X p : V) :
    p ∈ regularJoin P R X ↔ p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r, (∃ A ∈ X, r ∈ A) ∧ ⟨r, q⟩ₖ ∈ R := by
  unfold regularJoin
  rw [mem_forcingClosure_iff]
  simp only [mem_sUnion_iff]

theorem regularJoin_subset_poset (P R X : V) : regularJoin P R X ⊆ P :=
  forcingClosure_subset _ _ _

theorem regularJoin_mono {P R X Y : V} (h : X ⊆ Y) : regularJoin P R X ⊆ regularJoin P R Y :=
  forcingClosure_mono (fun p hp ↦ by
    obtain ⟨A, hA, hpA⟩ := mem_sUnion_iff.mp hp
    exact mem_sUnion_iff.mpr ⟨A, h A hA, hpA⟩)

theorem regularJoin_empty {P R : V} (hR : IsForcingPreorder P R) : regularJoin P R (∅ : V) = ∅ := by
  ext p
  simp only [mem_regularJoin_iff, not_mem_empty, iff_false, not_and]
  intro hp h
  obtain ⟨r, ⟨A, hA, _⟩, _⟩ := h p hp (hR.2.1 p hp)
  exact hA

/-- A regular subset meeting no member of `X` is disjoint from the join. -/
theorem inter_regularJoin_eq_empty {P R A X : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) (h : ∀ C ∈ X, A ∩ C = ∅) : A ∩ regularJoin P R X = ∅ := by
  ext p
  simp only [mem_inter_iff, not_mem_empty, iff_false, not_and]
  intro hpA hpj
  obtain ⟨hpP, hh⟩ := (mem_regularJoin_iff _ _ _ _).mp hpj
  obtain ⟨r, ⟨C, hC, hrC⟩, hrp⟩ := hh p hpP (hR.2.1 p hpP)
  have hrA : r ∈ A := hA.2.1 p hpA r (kpair_mem_iff.mp (hR.1 _ hrp)).1 hrp
  have : r ∈ A ∩ C := mem_inter_iff.mpr ⟨hrA, hrC⟩
  rw [h C hC] at this
  exact not_mem_empty this

/-- Meets distribute over arbitrary joins. -/
theorem inter_regularJoin {P R A X : V} (_hR : IsForcingPreorder P R) (hA : IsForcingRegular P R A)
    (hX : ∀ C ∈ X, C ⊆ P) :
    A ∩ regularJoin P R X = regularJoin P R (repl (fun C ↦ A ∩ C) (by definability) X) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpA, hpj⟩ := mem_inter_iff.mp hp
    obtain ⟨hpP, hh⟩ := (mem_regularJoin_iff _ _ _ _).mp hpj
    refine (mem_regularJoin_iff _ _ _ _).mpr ⟨hpP, fun q hq hqp ↦ ?_⟩
    obtain ⟨r, ⟨C, hC, hrC⟩, hrq⟩ := hh q hq hqp
    have hrP : r ∈ P := hX C hC r hrC
    have hqA : q ∈ A := hA.2.1 p hpA q hq hqp
    have hrA : r ∈ A := hA.2.1 q hqA r hrP hrq
    exact ⟨r, ⟨A ∩ C, (repl_spec _).mpr ⟨C, hC, rfl⟩, mem_inter_iff.mpr ⟨hrA, hrC⟩⟩, hrq⟩
  · intro hp
    obtain ⟨hpP, hh⟩ := (mem_regularJoin_iff _ _ _ _).mp hp
    refine mem_inter_iff.mpr ⟨?_, ?_⟩
    · apply hA.2.2 p hpP
      intro q hq hqp
      obtain ⟨r, ⟨D, hD, hrD⟩, hrq⟩ := hh q hq hqp
      obtain ⟨C, _, rfl⟩ := (repl_spec _).mp hD
      exact ⟨r, (mem_inter_iff.mp hrD).1, hrq⟩
    · refine (mem_regularJoin_iff _ _ _ _).mpr ⟨hpP, fun q hq hqp ↦ ?_⟩
      obtain ⟨r, ⟨D, hD, hrD⟩, hrq⟩ := hh q hq hqp
      obtain ⟨C, hC, rfl⟩ := (repl_spec _).mp hD
      exact ⟨r, ⟨C, hC, (mem_inter_iff.mp hrD).2⟩, hrq⟩

theorem forcingNegation_antitone {P R A B : V} (h : A ⊆ B) :
    forcingNegation P R B ⊆ forcingNegation P R A := by
  intro p hp
  obtain ⟨hpP, hh⟩ := (mem_forcingNegation_iff _ _ _ _).mp hp
  exact (mem_forcingNegation_iff _ _ _ _).mpr ⟨hpP, fun q hq hqp hqA ↦ hh q hq hqp (h q hqA)⟩

/-- The negation of a join of regular sets is the intersection of the negations. -/
theorem mem_forcingNegation_regularJoin_iff {P R X p : V} (hR : IsForcingPreorder P R)
    (hX : ∀ C ∈ X, IsForcingRegular P R C) :
    p ∈ forcingNegation P R (regularJoin P R X) ↔ p ∈ P ∧ ∀ C ∈ X, p ∈ forcingNegation P R C := by
  constructor
  · intro hp
    obtain ⟨hpP, hh⟩ := (mem_forcingNegation_iff _ _ _ _).mp hp
    refine ⟨hpP, fun C hC ↦ (mem_forcingNegation_iff _ _ _ _).mpr ⟨hpP, fun q hq hqp hqC ↦ ?_⟩⟩
    exact hh q hq hqp (subset_regularJoin hR hC (hX C hC) q hqC)
  · rintro ⟨hpP, hh⟩
    refine (mem_forcingNegation_iff _ _ _ _).mpr ⟨hpP, fun q hq hqp hqj ↦ ?_⟩
    obtain ⟨_, hj⟩ := (mem_regularJoin_iff _ _ _ _).mp hqj
    obtain ⟨r, ⟨C, hC, hrC⟩, hrq⟩ := hj q hq (hR.2.1 q hq)
    have hrP : r ∈ P := (hX C hC).1 r hrC
    exact ((mem_forcingNegation_iff _ _ _ _).mp (hh C hC)).2 r hrP
      (hR.2.2 r hrP q hq p hpP hrq hqp) hrC

/-- Containment in a negation is disjointness. -/
theorem subset_forcingNegation_iff {P R A B : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) (hB : B ⊆ P) :
    A ⊆ forcingNegation P R B ↔ A ∩ B = ∅ := by
  constructor
  · intro h
    ext p
    simp only [mem_inter_iff, not_mem_empty, iff_false, not_and]
    intro hpA hpB
    exact ((mem_forcingNegation_iff _ _ _ _).mp (h p hpA)).2 p (hB p hpB) (hR.2.1 p (hB p hpB)) hpB
  · intro h p hpA
    refine (mem_forcingNegation_iff _ _ _ _).mpr ⟨hA.1 p hpA, fun q hq hqp hqB ↦ ?_⟩
    have : q ∈ A ∩ B := mem_inter_iff.mpr ⟨hA.2.1 p hpA q hq hqp, hqB⟩
    rw [h] at this
    exact not_mem_empty this

/-- De Morgan: the negation of a meet of regular sets is the join of the negations. -/
theorem forcingNegation_inter {P R A B : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) (hB : IsForcingRegular P R B) :
    forcingNegation P R (A ∩ B) =
      regularJoin P R ({forcingNegation P R A, forcingNegation P R B} : V) := by
  have hnA := forcingNegation_regular hR hA.2.1
  have hnB := forcingNegation_regular hR hB.2.1
  have hX : ∀ C ∈ ({forcingNegation P R A, forcingNegation P R B} : V), IsForcingRegular P R C := by
    intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact hnA
    · rw [mem_singleton_iff.mp hC]
      exact hnB
  have hj : IsForcingRegular P R (regularJoin P R ({forcingNegation P R A, forcingNegation P R B} : V)) :=
    regularJoin_regular hR (fun C hC ↦ (hX C hC).1)
  have key : forcingNegation P R (regularJoin P R ({forcingNegation P R A, forcingNegation P R B} : V)) =
      A ∩ B := by
    ext p
    rw [mem_forcingNegation_regularJoin_iff hR hX]
    constructor
    · rintro ⟨hpP, hh⟩
      have h1 := hh _ (mem_insert.mpr (Or.inl rfl))
      have h2 := hh _ (mem_insert.mpr (Or.inr (mem_singleton_iff.mpr rfl)))
      rw [forcingNegation_negation hR hA] at h1
      rw [forcingNegation_negation hR hB] at h2
      exact mem_inter_iff.mpr ⟨h1, h2⟩
    · intro hp
      obtain ⟨hpA, hpB⟩ := mem_inter_iff.mp hp
      refine ⟨hA.1 p hpA, fun C hC ↦ ?_⟩
      rcases mem_insert.mp hC with rfl | hC
      · rw [forcingNegation_negation hR hA]
        exact hpA
      · rw [mem_singleton_iff.mp hC, forcingNegation_negation hR hB]
        exact hpB
  rw [← key, forcingNegation_negation hR hj]

theorem subset_regularJoin_pair_left {P R A B : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) : A ⊆ regularJoin P R ({A, B} : V) :=
  subset_regularJoin hR (mem_insert.mpr (Or.inl rfl)) hA

theorem subset_regularJoin_pair_right {P R A B : V} (hR : IsForcingPreorder P R)
    (hB : IsForcingRegular P R B) : B ⊆ regularJoin P R ({A, B} : V) :=
  subset_regularJoin hR (mem_insert.mpr (Or.inr (mem_singleton_iff.mpr rfl))) hB

theorem regularJoin_pair_subset {P R A B C : V} (hR : IsForcingPreorder P R)
    (hC : IsForcingRegular P R C) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    regularJoin P R ({A, B} : V) ⊆ C := by
  refine regularJoin_subset hR (fun D hD ↦ ?_) hC
  rcases mem_insert.mp hD with rfl | hD
  · exact hAC
  · rw [mem_singleton_iff.mp hD]
    exact hBC

/-- Modus ponens for regular sets: `A ∩ (¬A ∨ B) ⊆ B`. -/
theorem inter_regularJoin_negation_subset {P R A B : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) (hB : IsForcingRegular P R B) :
    A ∩ regularJoin P R ({forcingNegation P R A, B} : V) ⊆ B := by
  have hnA := forcingNegation_regular hR hA.2.1
  rw [inter_regularJoin hR hA (fun C hC ↦ by
    rcases mem_insert.mp hC with rfl | hC
    · exact forcingNegation_subset _ _ _
    · rw [mem_singleton_iff.mp hC]; exact hB.1)]
  refine regularJoin_subset hR (fun D hD ↦ ?_) hB
  obtain ⟨C, hC, rfl⟩ := (repl_spec _).mp hD
  rcases mem_insert.mp hC with rfl | hC
  · rw [inter_forcingNegation_eq_empty hR hA.1]
    exact fun x hx ↦ absurd hx not_mem_empty
  · rw [mem_singleton_iff.mp hC]
    exact fun x hx ↦ (mem_inter_iff.mp hx).2

end ZFVP
