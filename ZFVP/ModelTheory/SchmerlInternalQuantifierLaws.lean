import ZFVP.ModelTheory.SchmerlInternalBMR

/-! Countability laws used by the internal Q axioms. Every witness family
below is an actual definable internal set, including the family for Q-union. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internal_uncountable_mono {A B : V} (hAB : A ⊆ B)
    (hA : ¬IsInternallyCountable A) : ¬IsInternallyCountable B :=
  fun hB ↦ hA (internallyCountable_subset hB hAB)

theorem internal_uncountable_exists_nat (hAC : InternalChoice V) (A : V)
    (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (h : ¬IsInternallyCountable {x ∈ A ; ∃ i ∈ (ω : V), R i x}) :
    ∃ i ∈ (ω : V), ¬IsInternallyCountable {x ∈ A ; R i x} := by
  classical
  by_contra hh
  push Not at hh
  have hF := Schmerl.internal_fiber_definable A R hR
  have hu := Schmerl.internal_countable_union hAC internallyCountable_omega
    (fun i ↦ {x ∈ A ; R i x}) hF hh
  apply h
  apply internallyCountable_subset hu
  intro x hx
  obtain ⟨hxA, i, hi, hix⟩ := mem_sep_iff.mp hx
  apply mem_sUnion_iff.mpr
  exact ⟨{x ∈ A ; R i x}, (repl_spec _).mpr ⟨i, hi, rfl⟩, mem_sep_iff.mpr ⟨hxA, hix⟩⟩

theorem internal_uncountable_interchange (hAC : InternalChoice V) (A : V)
    (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (h : ¬IsInternallyCountable {y ∈ A ; ∃ x ∈ A, R x y}) :
    (∃ x ∈ A, ¬IsInternallyCountable {y ∈ A ; R x y}) ∨
      ¬IsInternallyCountable {x ∈ A ; ∃ y ∈ A, R x y} := by
  classical
  by_cases hex : ∃ x ∈ A, ¬IsInternallyCountable {y ∈ A ; R x y}
  · exact Or.inl hex
  apply Or.inr
  intro hI
  push Not at hex
  have hF := Schmerl.internal_fiber_definable A R hR
  have hu := Schmerl.internal_countable_union hAC hI (fun x ↦ {y ∈ A ; R x y}) hF
    (fun x hx ↦ hex x (mem_sep_iff.mp hx).1)
  apply h
  apply internallyCountable_subset hu
  intro y hy
  obtain ⟨hyA, x, hx, hxy⟩ := mem_sep_iff.mp hy
  apply mem_sUnion_iff.mpr
  refine ⟨{y ∈ A ; R x y}, (repl_spec _).mpr ?_, mem_sep_iff.mpr ⟨hyA, hxy⟩⟩
  exact ⟨x, mem_sep_iff.mpr ⟨hx, y, hyA, hxy⟩, rfl⟩

theorem internal_twoPoints_countable (a b : V) : IsInternallyCountable ({a, b} : V) :=
  internallyCountable_of_finite (by
    have he : ({a, b} : V) = insert a (insert b ∅) := by ext x; simp
    rw [he]
    exact internallyFinite_insert (internallyFinite_insert (internallyFinite_empty (V := V)) b) a)

end ZFVP.Infinitary.Internal
