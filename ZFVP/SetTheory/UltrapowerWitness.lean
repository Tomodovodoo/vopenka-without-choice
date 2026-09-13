import ZFVP.SetTheory.UltrapowerStage
import ZFVP.SetTheory.InternalChoice

/-! The choice step of the existential case of Los's theorem for the internal ultrapower, stated
without any syntax. A definable family of subsets of `A` indexed by `P` that is nonempty at every
index of a subset `S` is realized by a single function in `A ^ P` whose value at each index of `S`
lies in the corresponding member of the family. The same statement is what closes the ultrapower
under sequences, so it is stated for an arbitrary subset `S ⊆ P`.

The file also records the two pieces of ultrafilter algebra the induction of Los's theorem uses:
a union of two subsets of the index set is in the ultrafilter exactly when one of them is, and a
subset fails to be in the ultrafilter exactly when its relative complement is. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The padded family of witnesses -/

/-- The members of `A` picked out by `W p`, padded with the fallback point `a` at the indices where
`W p` is empty. The padding keeps the family nonempty at every index, so a single choice function
covers the whole index set. -/
noncomputable def paddedWitnesses (A a : V) (W : V → V) (hW : ℒₛₑₜ-function₁[V] W) (p : V) : V :=
  sep A (fun z ↦ z ∈ W p ∨ ((∀ y, y ∉ W p) ∧ z = a))
    (by have := hW; definability)

theorem mem_paddedWitnesses_iff (A a : V) (W : V → V) (hW : ℒₛₑₜ-function₁[V] W) (p z : V) :
    z ∈ paddedWitnesses A a W hW p ↔ z ∈ A ∧ (z ∈ W p ∨ ((∀ y, y ∉ W p) ∧ z = a)) :=
  mem_sep_iff

theorem paddedWitnesses_subset (A a : V) (W : V → V) (hW : ℒₛₑₜ-function₁[V] W) (p : V) :
    paddedWitnesses A a W hW p ⊆ A :=
  fun _ hz ↦ ((mem_paddedWitnesses_iff A a W hW p _).mp hz).1

theorem paddedWitnesses_definable_one (A a : V) (W : V → V) (hW : ℒₛₑₜ-function₁[V] W) :
    ℒₛₑₜ-function₁[V] (paddedWitnesses A a W hW) := by
  have hd : ℒₛₑₜ-relation[V] (fun Y p ↦ ∀ z, z ∈ Y ↔
      z ∈ A ∧ (z ∈ W p ∨ ((∀ y, y ∉ W p) ∧ z = a))) := by
    have := hW; definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = paddedWitnesses A a W hW (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [paddedWitnesses, mem_sep_iff]

/-- The padded family is nonempty at every index of `P`: a member of `W p` if there is one, the
fallback point otherwise. -/
theorem paddedWitnesses_nonempty {P A a : V} (ha : a ∈ A) (W : V → V)
    (hW : ℒₛₑₜ-function₁[V] W) (hsub : ∀ p ∈ P, W p ⊆ A) {p : V} (hp : p ∈ P) :
    IsNonempty (paddedWitnesses A a W hW p) := by
  by_cases hne : ∃ z, z ∈ W p
  · obtain ⟨z, hz⟩ := hne
    exact ⟨⟨z, (mem_paddedWitnesses_iff A a W hW p z).mpr ⟨hsub p hp z hz, Or.inl hz⟩⟩⟩
  · push Not at hne
    exact ⟨⟨a, (mem_paddedWitnesses_iff A a W hW p a).mpr ⟨ha, Or.inr ⟨hne, rfl⟩⟩⟩⟩

/-! ### The witness function -/

/-- Picking a witness at every index of a subset of the index set: a definable family of subsets of
`A` that is nonempty at every index of `S` is realized by a single function on all of `P`. -/
theorem exists_ultraFunction_of_witnesses (hAC : InternalChoice V) {P A S : V} (hSP : S ⊆ P)
    (hA : IsNonempty A) (W : V → V) (hW : ℒₛₑₜ-function₁ W) (hsub : ∀ p ∈ P, W p ⊆ A)
    (hne : ∀ p ∈ S, IsNonempty (W p)) :
    ∃ k, k ∈ A ^ P ∧ ∀ p ∈ S, k ‘ p ∈ W p := by
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨k, hkfun, hkdom, hkval⟩ :=
    choice_for_definable_family hAC P (paddedWitnesses A a W hW)
      (paddedWitnesses_definable_one A a W hW)
      (fun p hp ↦ paddedWitnesses_nonempty ha W hW hsub hp)
  refine ⟨k, mem_function_of_domain_values hkfun hkdom
    (fun p hp ↦ paddedWitnesses_subset A a W hW p _ (hkval p hp)), ?_⟩
  intro p hp
  have hw := (mem_paddedWitnesses_iff A a W hW p _).mp (hkval p (hSP p hp))
  rcases hw.2 with h1 | h2
  · exact h1
  · obtain ⟨z, hz⟩ := (hne p hp).nonempty
    exact absurd hz (h2.1 z)

/-! ### Two facts about set ultrafilters -/

/-- A union of two subsets of the index set is in the ultrafilter exactly when one of the two is. -/
theorem union_mem_ultrafilter_iff {P U X Y : V} (hU : IsSetUltrafilter P U) (hX : X ⊆ P)
    (hY : Y ⊆ P) : X ∪ Y ∈ U ↔ X ∈ U ∨ Y ∈ U := by
  have hXY : X ∪ Y ⊆ P := by
    intro z hz
    rcases mem_union_iff.mp hz with h | h
    · exact hX z h
    · exact hY z h
  constructor
  · intro hmem
    by_contra hno
    push Not at hno
    obtain ⟨hnX, hnY⟩ := hno
    have hcX : relativeComplement P X ∈ U := by
      rcases hU.dichotomy hX with h | h
      · exact absurd h hnX
      · exact h
    have hcY : relativeComplement P Y ∈ U := by
      rcases hU.dichotomy hY with h | h
      · exact absurd h hnY
      · exact h
    obtain ⟨z, hz⟩ := hU.nonempty_of_mem (hU.inter (hU.inter hcX hcY) hmem)
    rw [mem_inter_iff, mem_inter_iff, mem_relativeComplement_iff, mem_relativeComplement_iff,
      mem_union_iff] at hz
    rcases hz.2 with h | h
    · exact hz.1.1.2 h
    · exact hz.1.2.2 h
  · rintro (h | h)
    · exact hU.upward h hXY (fun z hz ↦ mem_union_iff.mpr (Or.inl hz))
    · exact hU.upward h hXY (fun z hz ↦ mem_union_iff.mpr (Or.inr hz))

/-- A subset of the index set is outside the ultrafilter exactly when its relative complement is
inside. -/
theorem not_mem_ultrafilter_iff_compl {P U X : V} (hU : IsSetUltrafilter P U) (hX : X ⊆ P) :
    X ∉ U ↔ relativeComplement P X ∈ U :=
  (ultraCompl_mem_iff hU hX).symm

end ZFVP
