import ZFVP.Syntax.MembershipRenamingConstructors
import ZFVP.SetTheory.NaturalArithmeticLaws

/-! Reversed finite contexts give persistent natural-number names when a new
bound variable is prepended at index zero. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def reverseIndices (n : V) : V :=
  {p ∈ n ×ˢ n ; succ (ordinalAdd (kpair.π₁ p) (kpair.π₂ p)) = n}

instance reverseIndices_definable : ℒₛₑₜ-function₁[V] reverseIndices := by
  have he : ℒₛₑₜ-relation[V] (fun A n ↦ ∀ p, p ∈ A ↔
      p ∈ n ×ˢ n ∧ succ (ordinalAdd (kpair.π₁ p) (kpair.π₂ p)) = n) := by definability
  apply Language.Definable.of_iff he
  intro v
  change v 0 = reverseIndices (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [reverseIndices, mem_sep_iff]

theorem pair_mem_reverseIndices_iff (n i j : V) :
    ⟨i, j⟩ₖ ∈ reverseIndices n ↔ i ∈ n ∧ j ∈ n ∧ succ (ordinalAdd i j) = n := by
  simp only [reverseIndices, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem reverseIndices_total {n : V} (hn : n ∈ (ω : V)) :
    ∀ i ∈ n, ∃ j ∈ n, ⟨i, j⟩ₖ ∈ reverseIndices n := by
  apply naturalNumber_induction (fun n ↦ ∀ i ∈ n, ∃ j ∈ n, ⟨i, j⟩ₖ ∈ reverseIndices n)
    (by definability) ?_ ?_ n hn
  · intro i hi
    exact (not_mem_empty hi).elim
  · intro n hn ih i hi
    rcases internalBoundIndex_cases hn hi with rfl | ⟨a, ha, rfl⟩
    · refine ⟨n, by simp, (pair_mem_reverseIndices_iff _ _ _).mpr ⟨zero_mem_succ_natural hn, by simp, ?_⟩⟩
      rw [ordinalAdd_zero_left_natural hn]
    · obtain ⟨b, hb, hab⟩ := ih a ha
      have hs := ((pair_mem_reverseIndices_iff _ _ _).mp hab).2.2
      have haω := IsOrdinal.toIsTransitive.mem_trans ha hn
      have hbω := IsOrdinal.toIsTransitive.mem_trans hb hn
      refine ⟨b, mem_succ_iff.mpr (Or.inr hb), (pair_mem_reverseIndices_iff _ _ _).mpr
        ⟨succ_mem_succ_of_natural_mem hn ha, mem_succ_iff.mpr (Or.inr hb), ?_⟩⟩
      rw [ordinalAdd_succ_left_natural haω hbω, hs]

theorem reverseIndices_unique {n i j k : V} (hn : n ∈ (ω : V))
    (hj : ⟨i, j⟩ₖ ∈ reverseIndices n) (hk : ⟨i, k⟩ₖ ∈ reverseIndices n) : j = k := by
  obtain ⟨hi, hj, he⟩ := (pair_mem_reverseIndices_iff _ _ _).mp hj
  obtain ⟨_, hk, hf⟩ := (pair_mem_reverseIndices_iff _ _ _).mp hk
  have hiω := IsOrdinal.toIsTransitive.mem_trans hi hn
  have hjω := IsOrdinal.toIsTransitive.mem_trans hj hn
  have hkω := IsOrdinal.toIsTransitive.mem_trans hk hn
  have : IsOrdinal i := IsOrdinal.of_mem hiω
  have : IsOrdinal j := IsOrdinal.of_mem hjω
  have : IsOrdinal k := IsOrdinal.of_mem hkω
  have hs := congrArg (fun x : V ↦ ⋃ˢ x) (he.trans hf.symm)
  have hs' : ordinalAdd i j = ordinalAdd i k := by simpa only [sUnion_succ_of_transitive] using hs
  exact ordinalAdd_right_injective hs'

theorem reverseIndices_function {n : V} (hn : n ∈ (ω : V)) : reverseIndices n ∈ n ^ n := by
  apply mem_function.intro
  · exact fun _ hp ↦ (mem_sep_iff.mp hp).1
  · intro i hi
    obtain ⟨j, _, hj⟩ := reverseIndices_total hn i hi
    exact ⟨j, hj, fun k hk ↦ reverseIndices_unique hn hk hj⟩

theorem reverseIndices_value_spec {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) :
    (reverseIndices n) ‘ i ∈ n ∧ succ (ordinalAdd i ((reverseIndices n) ‘ i)) = n := by
  have : IsFunction (reverseIndices n) := IsFunction.of_mem (reverseIndices_function hn)
  have hp := kpair_value_mem (f := reverseIndices n) ((domain_eq_of_mem_function (reverseIndices_function hn)).symm ▸ hi)
  exact ((pair_mem_reverseIndices_iff _ _ _).mp hp).2

theorem reverseIndices_value_of_sum {n i j : V} (hn : n ∈ (ω : V))
    (hi : i ∈ n) (hj : j ∈ n) (he : succ (ordinalAdd i j) = n) :
    (reverseIndices n) ‘ i = j := by
  have : IsFunction (reverseIndices n) := IsFunction.of_mem (reverseIndices_function hn)
  exact value_eq_of_kpair_mem ((pair_mem_reverseIndices_iff _ _ _).mpr ⟨hi, hj, he⟩)

theorem reverseIndices_involutive {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) :
    (reverseIndices n) ‘ ((reverseIndices n) ‘ i) = i := by
  obtain ⟨hj, he⟩ := reverseIndices_value_spec hn hi
  apply reverseIndices_value_of_sum hn hj hi
  rw [ordinalAdd_comm_natural (IsOrdinal.toIsTransitive.mem_trans hj hn)
    (IsOrdinal.toIsTransitive.mem_trans hi hn)]
  exact he

theorem reverseIndices_compose_self {n : V} (hn : n ∈ (ω : V)) :
    compose (reverseIndices n) (reverseIndices n) = SetTheory.identity n := by
  have hf := reverseIndices_function hn
  apply function_eq_of_values (compose_function hf hf) (identity_mem_function n)
  intro i hi
  rw [value_compose_of_mem_function hf hf hi, identity_value hi, reverseIndices_involutive hn hi]

theorem reverseIndices_succ_zero {n : V} (hn : n ∈ (ω : V)) :
    (reverseIndices (succ n)) ‘ (0 : V) = n := by
  apply reverseIndices_value_of_sum (ω_succ_closed hn) (zero_mem_succ_natural hn) (by simp)
  rw [ordinalAdd_zero_left_natural hn]

theorem reverseIndices_succ_succ {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) :
    (reverseIndices (succ n)) ‘ (succ i) = (reverseIndices n) ‘ i := by
  obtain ⟨hj, he⟩ := reverseIndices_value_spec hn hi
  apply reverseIndices_value_of_sum (ω_succ_closed hn) (succ_mem_succ_of_natural_mem hn hi)
    (mem_succ_iff.mpr (Or.inr hj))
  rw [ordinalAdd_succ_left_natural (IsOrdinal.toIsTransitive.mem_trans hi hn)
    (IsOrdinal.toIsTransitive.mem_trans hj hn), he]

noncomputable def tailShiftIndices (n k : V) : V :=
  definableGraph n (fun i ↦ ordinalAdd i k) (by definability)

instance tailShiftIndices_definable : ℒₛₑₜ-function₂[V] tailShiftIndices := by
  have he : ℒₛₑₜ-relation₃[V] (fun A n k ↦ ∀ p, p ∈ A ↔ ∃ i ∈ n, p = ⟨i, ordinalAdd i k⟩ₖ) := by definability
  apply Language.Definable.of_iff he
  intro v
  change v 0 = tailShiftIndices (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [tailShiftIndices, mem_definableGraph_iff]

theorem tailShiftIndices_function {n k : V} (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) :
    tailShiftIndices n k ∈ (ordinalAdd n k) ^ n := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  have hiω := IsOrdinal.toIsTransitive.mem_trans hi hn
  have : IsOrdinal n := IsOrdinal.of_mem hn
  rw [ordinalAdd_comm_natural hiω hk, ordinalAdd_comm_natural hn hk]
  exact ordinalAdd_mem hi

theorem tailShiftIndices_value {n i : V} (hi : i ∈ n) (k : V) :
    (tailShiftIndices n k) ‘ i = ordinalAdd i k := value_definableGraph _ _ _ hi

theorem reverseIndices_add {n k i : V} (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) (hi : i ∈ n) :
    (reverseIndices (ordinalAdd n k)) ‘ (ordinalAdd i k) = (reverseIndices n) ‘ i := by
  obtain ⟨hj, he⟩ := reverseIndices_value_spec hn hi
  have hiω := IsOrdinal.toIsTransitive.mem_trans hi hn
  have hjω := IsOrdinal.toIsTransitive.mem_trans hj hn
  have hi' : ordinalAdd i k ∈ ordinalAdd n k := by
    rw [ordinalAdd_comm_natural hiω hk, ordinalAdd_comm_natural hn hk]
    have : IsOrdinal n := IsOrdinal.of_mem hn
    exact ordinalAdd_mem hi
  have : IsOrdinal k := IsOrdinal.of_mem hk
  have hj' : (reverseIndices n) ‘ i ∈ ordinalAdd n k := subset_ordinalAdd n k _ hj
  apply reverseIndices_value_of_sum (ordinalAdd_natural hn hk) hi' hj'
  rw [ordinalAdd_swap_natural hiω hk hjω, ← ordinalAdd_succ_left_natural (ordinalAdd_natural hiω hjω) hk, he]

end ZFVP
