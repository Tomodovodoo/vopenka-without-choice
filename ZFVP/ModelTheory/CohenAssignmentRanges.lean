import ZFVP.ModelTheory.CohenFiniteAssignmentValues
import ZFVP.SetTheory.EndExtensionFinite

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

theorem mem_finiteAssignmentValue_range_iff (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (b : V) (hb : IsInternalPermutation (ω : V) b)
    (x : (cohenContext (ω : V) G hG).Model) :
    x ∈ range (finiteAssignmentValue hG E hEω hEf b hb) ↔ ∃ i : V, ∃ hi : i ∈ E,
      x = real hG (b ‘ i) (function_value_mem hb.1 (hEω i hi)) := by
  rw [mem_range_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨i, hi, he⟩ := (mem_finiteAssignmentValue_iff hG E hEω hEf b hb _).mp hy
    exact ⟨i, hi, (kpair_iff.mp he).2⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(cohenContext (ω : V) G hG).check i,
      (mem_finiteAssignmentValue_iff hG E hEω hEf b hb _).mpr ⟨i, hi, rfl⟩⟩

theorem finiteAssignmentValue_range_finite (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (b : V) (hb : IsInternalPermutation (ω : V) b) :
    IsInternallyFinite (range (finiteAssignmentValue hG E hEω hEf b hb)) := by
  have hf := finiteAssignmentValue_function hG E hEω hEf b hb
  have : IsFunction (finiteAssignmentValue hG E hEω hEf b hb) := IsFunction.of_mem hf
  apply internallyFinite_range
  apply internallyFinite_function
  rw [domain_eq_of_mem_function hf]
  exact (cohenContext (ω : V) G hG).checkEmbedding.map_internallyFinite hEf

theorem finiteAssignmentValue_range_subset_reals (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (b : V) (hb : IsInternalPermutation (ω : V) b) :
    range (finiteAssignmentValue hG E hEω hEf b hb) ⊆ reals hG :=
  range_subset_of_mem_function (finiteAssignmentValue_function hG E hEω hEf b hb)

/-- Inclusion between assignment ranges is exactly inclusion between their coordinate images. -/
theorem finiteAssignmentValue_range_subset_iff (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (b : V) (hb : IsInternalPermutation (ω : V) b)
    (F : V) (hFω : F ⊆ (ω : V)) (hFf : IsInternallyFinite F)
    (c : V) (hc : IsInternalPermutation (ω : V) c) :
    range (finiteAssignmentValue hG E hEω hEf b hb) ⊆
      range (finiteAssignmentValue hG F hFω hFf c hc) ↔
    repl (fun i ↦ b ‘ i) (by definability) E ⊆ repl (fun i ↦ c ‘ i) (by definability) F := by
  constructor
  · intro hsub x hx
    obtain ⟨i, hi, rfl⟩ := (repl_spec _).mp hx
    have hiR := (mem_finiteAssignmentValue_range_iff hG E hEω hEf b hb _).mpr ⟨i, hi, rfl⟩
    obtain ⟨j, hj, he⟩ := (mem_finiteAssignmentValue_range_iff hG F hFω hFf c hc _).mp (hsub _ hiR)
    exact (repl_spec _).mpr ⟨j, hj,
      (real_eq_iff hG (function_value_mem hb.1 (hEω i hi))
        (function_value_mem hc.1 (hFω j hj))).mp he⟩
  · intro hsub x hx
    obtain ⟨i, hi, rfl⟩ := (mem_finiteAssignmentValue_range_iff hG E hEω hEf b hb x).mp hx
    obtain ⟨j, hj, he⟩ := (repl_spec _).mp (hsub _ ((repl_spec _).mpr ⟨i, hi, rfl⟩))
    exact (mem_finiteAssignmentValue_range_iff hG F hFω hFf c hc _).mpr ⟨j, hj,
      (real_eq_iff hG (function_value_mem hb.1 (hEω i hi))
        (function_value_mem hc.1 (hFω j hj))).mpr he⟩

/-- The real set coded by `E` is contained in an assignment range precisely when the latter
coordinate image contains `E`. -/
theorem finiteAssignmentValue_identity_range_subset_iff (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (F : V) (hFω : F ⊆ (ω : V)) (hFf : IsInternallyFinite F)
    (b : V) (hb : IsInternalPermutation (ω : V) b) :
    range (finiteAssignmentValue hG E hEω hEf (identity (ω : V)) (internalPermutation_identity (ω : V))) ⊆
      range (finiteAssignmentValue hG F hFω hFf b hb) ↔
    E ⊆ repl (fun i ↦ b ‘ i) (by definability) F := by
  rw [finiteAssignmentValue_range_subset_iff]
  have he : repl (fun i ↦ (identity (ω : V)) ‘ i) (by definability) E = E := by
    apply mem_ext
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, he⟩ := (repl_spec _).mp hx
      rw [identity_value (hEω i hi)] at he
      exact he.symm ▸ hi
    · intro hx
      exact (repl_spec _).mpr ⟨x, hx, (identity_value (hEω x hx)).symm⟩
  rw [he]

end CohenModel
end ZFVP
