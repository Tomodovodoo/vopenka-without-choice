import ZFVP.SetTheory.BaireRunPrefixes
import ZFVP.SetTheory.CantorInfiniteOnes
import ZFVP.SetTheory.PerfectSetCore

/-! The run encoding of an entire Baire real as a Cantor real. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def baireRunCodeFormula : SetTheorySemisentence 2 :=
  f“c a. ∀ p, p ∈ c ↔ ∃ n ∈ !isω, p ∈ !baireRunPrefixFormula a n”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def baireRunCode (a : V) : V :=
  ⋃ˢ repl (baireRunPrefix a) (by definability) (ω : V)

theorem mem_baireRunCode_iff (a p : V) :
    p ∈ baireRunCode a ↔ ∃ n ∈ (ω : V), p ∈ baireRunPrefix a n := by
  simp only [baireRunCode, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, hp⟩
    exact ⟨n, hn, hp⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨_, ⟨n, hn, rfl⟩, hp⟩

instance baireRunCodeFormula_defined : ℒₛₑₜ-function₁[V] baireRunCode via baireRunCodeFormula :=
  ⟨fun v ↦ by simp [baireRunCodeFormula, mem_ext_iff (y := baireRunCode _), mem_baireRunCode_iff]⟩

instance baireRunCode_definable : ℒₛₑₜ-function₁[V] baireRunCode :=
  baireRunCodeFormula_defined.to_definable

theorem baireRunPrefix_subset_code (a : V) {n : V} (hn : n ∈ (ω : V)) :
    baireRunPrefix a n ⊆ baireRunCode a :=
  fun p hp ↦ (mem_baireRunCode_iff a p).mpr ⟨n, hn, hp⟩

theorem baireRunPrefix_real_mem {a n : V} (ha : a ∈ baireSpace V) (hn : n ∈ (ω : V)) :
    baireRunPrefix a n ∈ binarySequences V :=
  baireRunPrefix_mem ha hn (IsTransitive.transitive _ hn)

theorem baireRunCode_isFunction {a : V} (ha : a ∈ baireSpace V) : IsFunction (baireRunCode a) := by
  apply isFunction_sUnion
  · intro f hf
    obtain ⟨n, hn, rfl⟩ := (repl_spec (by definability)).mp hf
    exact binarySequence_isFunction (baireRunPrefix_real_mem ha hn)
  · intro f hf g hg i y z hiy hiz
    obtain ⟨n, hn, rfl⟩ := (repl_spec (by definability)).mp hf
    obtain ⟨k, hk, rfl⟩ := (repl_spec (by definability)).mp hg
    have : IsOrdinal n := IsOrdinal.of_mem hn
    have : IsOrdinal k := IsOrdinal.of_mem hk
    have : IsFunction (baireRunPrefix a n) := binarySequence_isFunction (baireRunPrefix_real_mem ha hn)
    have : IsFunction (baireRunPrefix a k) := binarySequence_isFunction (baireRunPrefix_real_mem ha hk)
    rcases IsOrdinal.subset_or_supset (α := n) (β := k) with hnk | hkn
    · exact IsFunction.unique
        (baireRunPrefix_mono ha hn hk hnk (IsTransitive.transitive _ hk) _ hiy) hiz
    · exact IsFunction.unique hiy
        (baireRunPrefix_mono ha hk hn hkn (IsTransitive.transitive _ hn) _ hiz)

theorem baireRunCode_domain {a : V} (ha : a ∈ baireSpace V) : domain (baireRunCode a) = (ω : V) := by
  apply mem_ext
  intro k
  constructor
  · intro hk
    obtain ⟨y, hky⟩ := mem_domain_iff.mp hk
    obtain ⟨n, hn, hp⟩ := (mem_baireRunCode_iff a _).mp hky
    exact IsTransitive.ω.transitive _ (binarySequence_domain_mem (baireRunPrefix_real_mem ha hn))
      _ (mem_domain_of_kpair_mem hp)
  · intro hk
    have hn := ω_succ_closed hk
    have : IsFunction (baireRunPrefix a (succ k)) :=
      binarySequence_isFunction (baireRunPrefix_real_mem ha hn)
    have hdom : k ∈ domain (baireRunPrefix a (succ k)) :=
      baireRunPrefix_length_bound ha hn (IsTransitive.transitive _ hn) _ (mem_succ_self k)
    exact mem_domain_of_kpair_mem (baireRunPrefix_subset_code a hn _ (kpair_value_mem hdom))

theorem baireRunCode_mem {a : V} (ha : a ∈ baireSpace V) : baireRunCode a ∈ cantorSpace V := by
  have : IsFunction (baireRunCode a) := baireRunCode_isFunction ha
  have h := IsFunction.mem_function (baireRunCode a)
  rw [baireRunCode_domain ha] at h
  apply mem_function_of_mem_function_of_subset h
  intro y hy
  obtain ⟨k, hky⟩ := mem_range_iff.mp hy
  obtain ⟨n, hn, hp⟩ := (mem_baireRunCode_iff a _).mp hky
  obtain ⟨m, hm, hpm⟩ := (mem_binarySequences_iff _).mp (baireRunPrefix_real_mem ha hn)
  exact range_subset_of_mem_function hpm _ (mem_range_of_kpair_mem hp)

theorem baireRunCode_value_of_prefix {a n k : V} (ha : a ∈ baireSpace V)
    (hn : n ∈ (ω : V)) (hk : k ∈ domain (baireRunPrefix a n)) :
    (baireRunCode a) ‘ k = (baireRunPrefix a n) ‘ k := by
  have : IsFunction (baireRunCode a) := baireRunCode_isFunction ha
  have : IsFunction (baireRunPrefix a n) := binarySequence_isFunction (baireRunPrefix_real_mem ha hn)
  exact value_eq_of_subset_function (baireRunPrefix_subset_code a hn) hk

theorem baireRunCode_infiniteOnes {a : V} (ha : a ∈ baireSpace V) :
    baireRunCode a ∈ cantorInfiniteOnes V := by
  refine (mem_cantorInfiniteOnes_iff _).mpr ⟨baireRunCode_mem ha, ?_⟩
  intro n hn
  have hp := baireRunPrefix_real_mem ha hn
  obtain ⟨hdom, hpf⟩ := (mem_finiteSequences_iff_domain _ _).mp hp
  have han : a ‘ n ∈ (ω : V) := function_value_mem ha hn
  have := IsOrdinal.of_mem han
  let k := ordinalAdd (domain (baireRunPrefix a n)) (a ‘ n)
  have hk : k ∈ (ω : V) := ordinalAdd_natural hdom han
  have hnk : n ⊆ k := subset_trans
    (baireRunPrefix_length_bound ha hn (IsTransitive.transitive _ hn)) (subset_ordinalAdd _ _)
  refine ⟨k, hk, hnk, ?_⟩
  have hkd : k ∈ domain (baireRunPrefix a (succ n)) := by
    rw [baireRunPrefix_succ a hn, binaryAppendRun_domain hpf]
    exact mem_succ_self k
  rw [baireRunCode_value_of_prefix ha (ω_succ_closed hn) hkd, baireRunPrefix_succ a hn]
  exact binaryAppendRun_separator hp

theorem baireRunCode_injective {a b : V} (ha : a ∈ baireSpace V) (hb : b ∈ baireSpace V)
    (he : baireRunCode a = baireRunCode b) : a = b := by
  have : IsFunction a := IsFunction.of_mem ha
  have : IsFunction b := IsFunction.of_mem hb
  have : IsFunction (baireRunCode a) := baireRunCode_isFunction ha
  have hagree : ∀ n ∈ (ω : V), ∀ i ∈ n, a ‘ i = b ‘ i := by
    apply naturalNumber_induction (fun n ↦ ∀ i ∈ n, a ‘ i = b ‘ i) (by definability)
    · intro i hi
      exact (not_mem_empty hi).elim
    · intro n hn ih
      have hpa := baireRunPrefix_real_mem ha (ω_succ_closed hn)
      have hpb := baireRunPrefix_real_mem hb (ω_succ_closed hn)
      have : IsFunction (baireRunPrefix a (succ n)) := binarySequence_isFunction hpa
      have : IsFunction (baireRunPrefix b (succ n)) := binarySequence_isFunction hpb
      have hsuba := baireRunPrefix_subset_code a (ω_succ_closed hn)
      have hsubb : baireRunPrefix b (succ n) ⊆ baireRunCode a := by
        rw [he]
        exact baireRunPrefix_subset_code b (ω_succ_closed hn)
      have hnab := not_incompatible_of_subset_subset hsuba hsubb
      have hnba := not_incompatible_of_subset_subset hsubb hsuba
      have heprefix := baireRunPrefix_agree hn ih
      rw [baireRunPrefix_succ a hn, baireRunPrefix_succ b hn, heprefix] at hnab hnba
      have han := function_value_mem ha hn
      have hbn := function_value_mem hb hn
      have : IsOrdinal (a ‘ n) := IsOrdinal.of_mem han
      have : IsOrdinal (b ‘ n) := IsOrdinal.of_mem hbn
      have hv : a ‘ n = b ‘ n := by
        rcases IsOrdinal.mem_trichotomy (a ‘ n) (b ‘ n) with hlt | heq | hgt
        · exact (hnab (binaryAppendRun_disagree (baireRunPrefix_real_mem hb hn) han hbn hlt)).elim
        · exact heq
        · exact (hnba (binaryAppendRun_disagree (baireRunPrefix_real_mem hb hn) hbn han hgt)).elim
      intro i hi
      rcases mem_succ_iff.mp hi with rfl | hi
      · exact hv
      · exact ih i hi
  apply functions_eq_of_domain_values (by rw [domain_eq_of_mem_function ha, domain_eq_of_mem_function hb])
  intro n hn
  rw [domain_eq_of_mem_function ha] at hn
  exact hagree (succ n) (ω_succ_closed hn) n (mem_succ_self n)

end ZFVP
