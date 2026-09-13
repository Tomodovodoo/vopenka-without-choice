import ZFVP.SetTheory.Rank
import ZFVP.SetTheory.FunctionValue

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The lexicographic order on subsets of the internal natural numbers. -/
def RealLexLt (x y : V) : Prop :=
  ∃ n ∈ (ω : V), n ∉ x ∧ n ∈ y ∧ ∀ m ∈ n, (m ∈ x ↔ m ∈ y)

instance realLexLt_definable : ℒₛₑₜ-relation[V] RealLexLt := by
  unfold RealLexLt
  definability

theorem realLexLt_irrefl (x : V) : ¬RealLexLt x x := by
  rintro ⟨n, _, hn, hn', _⟩
  exact hn hn'

theorem realLexLt_trans {x y z : V} (hxy : RealLexLt x y) (hyz : RealLexLt y z) :
    RealLexLt x z := by
  obtain ⟨i, hi, hix, hiy, he⟩ := hxy
  obtain ⟨j, hj, hjy, hjz, hf⟩ := hyz
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy i j with hij | rfl | hji
  · refine ⟨i, hi, hix, (hf i hij).mp hiy, ?_⟩
    intro k hk
    exact (he k hk).trans (hf k (IsOrdinal.toIsTransitive.mem_trans hk hij))
  · exact (hjy hiy).elim
  · refine ⟨j, hj, fun hh ↦ hjy ((he j hji).mp hh), hjz, ?_⟩
    intro k hk
    exact (he k (IsOrdinal.toIsTransitive.mem_trans hk hji)).trans (hf k hk)

theorem realLexLt_trichotomy {x y : V} (hx : x ⊆ (ω : V)) (hy : y ⊆ (ω : V)) :
    RealLexLt x y ∨ x = y ∨ RealLexLt y x := by
  classical
  by_cases hxy : x = y
  · exact Or.inr (Or.inl hxy)
  have hex : ∃ n : V, IsOrdinal n ∧ n ∈ (ω : V) ∧ ¬(n ∈ x ↔ n ∈ y) := by
    by_contra hn
    apply hxy
    apply mem_ext
    intro n
    by_cases hω : n ∈ (ω : V)
    · by_contra he
      exact hn ⟨n, IsOrdinal.of_mem hω, hω, he⟩
    · exact ⟨fun h ↦ (hω (hx n h)).elim, fun h ↦ (hω (hy n h)).elim⟩
  obtain ⟨n, ⟨hnord, ⟨hn, hne⟩, hmin⟩, _⟩ :=
    leastOrdinal_existsUnique (fun n : V ↦ n ∈ (ω : V) ∧ ¬(n ∈ x ↔ n ∈ y))
      (by definability) hex
  let := hnord
  have he : ∀ m ∈ n, (m ∈ x ↔ m ∈ y) := by
    intro m hm
    by_contra hh
    have hmω : m ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hm hn
    exact mem_irrefl m (hmin m (IsOrdinal.of_mem hmω) ⟨hmω, hh⟩ m hm)
  by_cases hnx : n ∈ x
  · have hny : n ∉ y := fun hny ↦ hne ⟨fun _ ↦ hny, fun _ ↦ hnx⟩
    exact Or.inr (Or.inr ⟨n, hn, hny, hnx, fun m hm ↦ (he m hm).symm⟩)
  · have hny : n ∈ y := by
      by_contra hny
      exact hne ⟨fun hh ↦ (hnx hh).elim, fun hh ↦ (hny hh).elim⟩
    exact Or.inl ⟨n, hn, hnx, hny, he⟩

/-- Compare maps at their first differing coordinate in a fixed subset of `ω`. -/
def RealMapLexLt (B f g : V) : Prop :=
  ∃ i ∈ B, RealLexLt (f ‘ i) (g ‘ i) ∧ ∀ j ∈ i, j ∈ B → f ‘ j = g ‘ j

instance realMapLexLt_definable : ℒₛₑₜ-relation₃[V] RealMapLexLt := by
  unfold RealMapLexLt
  definability

theorem realMapLexLt_irrefl (B f : V) : ¬RealMapLexLt B f f := by
  rintro ⟨i, _, hi, _⟩
  exact realLexLt_irrefl _ hi

theorem realMapLexLt_trans {B f g h : V} (hB : B ⊆ (ω : V))
    (hfg : RealMapLexLt B f g) (hgh : RealMapLexLt B g h) : RealMapLexLt B f h := by
  obtain ⟨i, hi, hifg, he⟩ := hfg
  obtain ⟨j, hj, hjgh, hf⟩ := hgh
  let := IsOrdinal.of_mem (hB i hi)
  let := IsOrdinal.of_mem (hB j hj)
  rcases IsOrdinal.mem_trichotomy i j with hij | rfl | hji
  · refine ⟨i, hi, ?_, ?_⟩
    · rwa [← hf i hij hi]
    · intro k hk hkB
      exact (he k hk hkB).trans (hf k (IsOrdinal.toIsTransitive.mem_trans hk hij) hkB)
  · exact ⟨i, hi, realLexLt_trans hifg hjgh, fun k hk hkB ↦
      (he k hk hkB).trans (hf k hk hkB)⟩
  · refine ⟨j, hj, ?_, ?_⟩
    · rwa [he j hji hj]
    · intro k hk hkB
      exact (he k (IsOrdinal.toIsTransitive.mem_trans hk hji) hkB).trans (hf k hk hkB)

theorem realMapLexLt_trichotomy {B f g : V} (hB : B ⊆ (ω : V))
    (hf : f ∈ (℘ (ω : V)) ^ B) (hg : g ∈ (℘ (ω : V)) ^ B) :
    RealMapLexLt B f g ∨ f = g ∨ RealMapLexLt B g f := by
  classical
  by_cases hfg : f = g
  · exact Or.inr (Or.inl hfg)
  let := IsFunction.of_mem hf
  let := IsFunction.of_mem hg
  have hex : ∃ i : V, IsOrdinal i ∧ i ∈ B ∧ f ‘ i ≠ g ‘ i := by
    by_contra hn
    apply hfg
    apply function_ext hf hg
    intro i hi y _ hiy
    have hv : f ‘ i = g ‘ i := by
      by_contra he
      exact hn ⟨i, IsOrdinal.of_mem (hB i hi), hi, he⟩
    have hy : y = g ‘ i := (value_eq_of_kpair_mem hiy).symm.trans hv
    rw [hy]
    exact kpair_value_mem ((domain_eq_of_mem_function hg).symm ▸ hi)
  obtain ⟨i, ⟨hiord, ⟨hi, hne⟩, hmin⟩, _⟩ :=
    leastOrdinal_existsUnique (fun i : V ↦ i ∈ B ∧ f ‘ i ≠ g ‘ i) (by definability) hex
  let := hiord
  have he : ∀ j ∈ i, j ∈ B → f ‘ j = g ‘ j := by
    intro j hj hjB
    by_contra hh
    exact mem_irrefl j (hmin j (IsOrdinal.of_mem (hB j hjB)) ⟨hjB, hh⟩ j hj)
  rcases realLexLt_trichotomy (mem_power_iff.mp (function_value_mem hf hi))
      (mem_power_iff.mp (function_value_mem hg hi)) with hlt | heq | hgt
  · exact Or.inl ⟨i, hi, hlt, he⟩
  · exact (hne heq).elim
  · exact Or.inr (Or.inr ⟨i, hi, hgt, fun j hj hjB ↦ (he j hj hjB).symm⟩)

end ZFVP
