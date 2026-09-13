import ZFVP.SetTheory.EndExtensionLevyCollapse
import ZFVP.SetTheory.InfiniteDependentChoice

/-! The set `[A]^{<ω}` of finite subsets of `A`, its absoluteness for membership end extensions
(Fact (∇) in Enayat's Theorem 5.18), the matching statement for `Fin(A,2)` (Fact (∗∗)), and the two
facts about `[A]^{<ω}` as a poset under inclusion used there: it is closed under binary unions, and
it has no maximal element when `A` is internally infinite. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `[A]^{<ω}`, the set of internally finite subsets of `A`. -/
noncomputable def finiteSubsets (A : V) : V := {x ∈ ℘ A ; IsInternallyFinite x}

theorem mem_finiteSubsets_iff (A x : V) :
    x ∈ finiteSubsets A ↔ (x ⊆ A ∧ IsInternallyFinite x) := by
  simp only [finiteSubsets, mem_sep_iff, mem_power_iff]

instance finiteSubsets_definable : ℒₛₑₜ-function₁[V] finiteSubsets := by
  have h : ℒₛₑₜ-relation[V] (fun S A ↦ ∀ x, x ∈ S ↔ (x ⊆ A ∧ IsInternallyFinite x)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = finiteSubsets (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_finiteSubsets_iff]

theorem empty_mem_finiteSubsets (A : V) : (∅ : V) ∈ finiteSubsets A :=
  (mem_finiteSubsets_iff A ∅).mpr ⟨empty_subset A, internallyFinite_empty⟩

/-- `[A]^{<ω}` is directed: it is closed under binary unions. -/
theorem finiteSubsets_union {A x y : V} (hx : x ∈ finiteSubsets A) (hy : y ∈ finiteSubsets A) :
    x ∪ y ∈ finiteSubsets A := by
  obtain ⟨hxs, hxf⟩ := (mem_finiteSubsets_iff A x).mp hx
  obtain ⟨hys, hyf⟩ := (mem_finiteSubsets_iff A y).mp hy
  refine (mem_finiteSubsets_iff A _).mpr ⟨?_, internallyFinite_union hxf hyf⟩
  intro z hz
  rcases mem_union_iff.mp hz with h | h
  · exact hxs z h
  · exact hys z h

/-- A finite subset of an internally infinite set is properly contained in a larger one, so
`[A]^{<ω}` has no maximal element. -/
theorem finiteSubsets_no_maximum {A : V} (hA : IsInternallyInfinite A) {x : V}
    (hx : x ∈ finiteSubsets A) : ∃ y ∈ finiteSubsets A, x ⊆ y ∧ x ≠ y := by
  obtain ⟨hxs, hxf⟩ := (mem_finiteSubsets_iff A x).mp hx
  have hne : ∃ a ∈ A, a ∉ x := by
    by_contra h
    push Not at h
    exact hA (internallyFinite_subset hxf (fun z hz ↦ h z hz))
  obtain ⟨a, haA, hax⟩ := hne
  refine ⟨insert a x, (mem_finiteSubsets_iff A _).mpr ⟨?_, internallyFinite_insert hxf a⟩,
    ?_, ?_⟩
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact haA
    · exact hxs z hz
  · intro z hz
    exact mem_insert.mpr (Or.inr hz)
  · intro he
    apply hax
    rw [he]
    exact mem_insert.mpr (Or.inl rfl)

namespace MembershipEndExtension

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Fact (∇): the set of finite subsets is absolute for membership end extensions. -/
theorem map_finiteSubsets (j : MembershipEndExtension V W) (A : V) :
    j (finiteSubsets A) = finiteSubsets (j A) := by
  apply mem_ext
  intro q
  constructor
  · intro hq
    obtain ⟨p, hp, rfl⟩ := j.endExtension _ _ hq
    obtain ⟨hsub, hfin⟩ := (mem_finiteSubsets_iff A p).mp hp
    exact (mem_finiteSubsets_iff (j A) (j p)).mpr
      ⟨(j.subset_iff _ _).mpr hsub, j.map_internallyFinite hfin⟩
  · intro hq
    obtain ⟨hsub, hfin⟩ := (mem_finiteSubsets_iff (j A) q).mp hq
    obtain ⟨p, hpsub, rfl⟩ := j.exists_eq_map_of_finite_subset hsub hfin
    exact (j.mem_iff _ _).mpr
      ((mem_finiteSubsets_iff A p).mpr ⟨hpsub, (j.internallyFinite_iff p).mp hfin⟩)

/-- Fact (∗∗): the set `Fin(A,2)` of finite partial functions from `A` to `2` is absolute. -/
theorem map_finiteFunctionsTwo (j : MembershipEndExtension V W) (A : V) :
    j (finitePartialFunctions A ((2 : ℕ) : V)) = finitePartialFunctions (j A) ((2 : ℕ) : W) := by
  rw [j.map_finitePartialFunctions, j.map_numeral]

end MembershipEndExtension

end ZFVP
