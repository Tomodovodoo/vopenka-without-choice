import ZFVP.SetTheory.TraceStages
import ZFVP.SetTheory.EndExtensionRecursion
import ZFVP.SetTheory.EndExtensionRegular
import ZFVP.SetTheory.EndExtensionReplacement

/-! The trace recursion is transported by membership end extensions: its step is built from
unions, separations, replacements, complements and regular joins, all of which commute with the
extension, so the recursion in the larger model along the image ordinal is the image of the
recursion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace MembershipEndExtension

variable (j : MembershipEndExtension V W)

theorem map_traceStep (P R Ysets H₀ X U : V) :
    j (traceStep P R Ysets H₀ X U) = traceStep (j P) (j R) (j Ysets) (j H₀) (j X) (j U) := by
  have hneg := j.map_repl {A ∈ X ; A ∉ H₀ ∪ U} (fun A ↦ forcingNegation P R A)
    (fun A ↦ forcingNegation (j P) (j R) A) (by definability) (by definability)
    (fun x _ ↦ j.map_forcingNegation P R x)
  have hjoin := j.map_repl {Y ∈ Ysets ; Y ⊆ X ∧ ∃ y ∈ Y, y ∈ H₀ ∪ U} (fun Y ↦ regularJoin P R Y)
    (fun Y ↦ regularJoin (j P) (j R) Y) (regularJoin_definable_one P R)
    (regularJoin_definable_one (j P) (j R)) (fun x _ ↦ j.map_regularJoin P R x)
  have hsep1 := j.map_separation X (fun A ↦ A ∉ H₀ ∪ U) (fun A ↦ A ∉ j H₀ ∪ j U)
    (by definability) (by definability) (fun x _ ↦ by rw [← j.map_union, j.mem_iff])
  have hsep2 := j.map_separation Ysets (fun Y ↦ Y ⊆ X ∧ ∃ y ∈ Y, y ∈ H₀ ∪ U)
    (fun Y ↦ Y ⊆ j X ∧ ∃ y ∈ Y, y ∈ j H₀ ∪ j U) (by definability) (by definability) (by
      intro Y _
      rw [j.subset_iff, ← j.map_union]
      apply and_congr_right
      intro _
      constructor
      · rintro ⟨y, hy, hyU⟩
        exact ⟨j y, (j.mem_iff _ _).mpr hy, (j.mem_iff _ _).mpr hyU⟩
      · rintro ⟨y', hy', hyU⟩
        obtain ⟨y, hy, rfl⟩ := j.endExtension Y y' hy'
        exact ⟨y, hy, (j.mem_iff _ _).mp hyU⟩)
  unfold traceStep
  rw [j.map_union, j.map_union, j.map_union, hneg, hjoin, hsep1, hsep2]

theorem map_traceStages (P R Ysets S H₀ Cl θ : V) :
    j (traceStages P R Ysets S H₀ Cl θ) =
      traceStages (j P) (j R) (j Ysets) (j S) (j H₀) (j Cl) (j θ) := by
  unfold traceStages
  apply j.map_wellFoundedRecursion (membershipRelation_wellFounded θ)
    (membershipRelation_wellFounded (j θ)) (j.map_membershipRelation θ) rfl
  intro α g
  rw [j.map_traceStep, j.map_union, j.map_sUnion, j.map_range, j.map_restrict, j.map_sUnion,
    j.map_range]

theorem map_traceSet (P R Ysets S H₀ Cl θ : V) :
    j (traceSet P R Ysets S H₀ Cl θ) = traceSet (j P) (j R) (j Ysets) (j S) (j H₀) (j Cl) (j θ) := by
  unfold traceSet
  rw [j.map_sUnion, j.map_range, j.map_traceStages]

end MembershipEndExtension

end ZFVP
