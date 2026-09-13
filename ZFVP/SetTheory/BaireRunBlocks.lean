import ZFVP.SetTheory.BaireSpace
import ZFVP.SetTheory.NaturalArithmeticOrder
import ZFVP.SetTheory.NaturalIteration

/-! Finite blocks for the map a ↦ 0^(a(0)) 1 0^(a(1)) 1 ... . -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def binaryZeroExtendFormula : SetTheorySemisentence 3 :=
  f“y s n. ∀ p, p ∈ y ↔ ∃ i ∈ n, p = !kpair.dfn i (!value.dfn s i)”

def binaryAppendRunFormula : SetTheorySemisentence 3 :=
  f“y s a. y = !insert.dfn
    (!kpair.dfn (!ordinalAddFormula (!domain.dfn s) a) (!(numeralFormula 1)))
    (!binaryZeroExtendFormula s (!ordinalAddFormula (!domain.dfn s) a))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryZeroExtend (s n : V) : V :=
  definableGraph n (fun i ↦ s ‘ i) (by definability)

theorem mem_binaryZeroExtend_iff (s n p : V) :
    p ∈ binaryZeroExtend s n ↔ ∃ i ∈ n, p = ⟨i, s ‘ i⟩ₖ := by
  simp [binaryZeroExtend, mem_definableGraph_iff]

instance binaryZeroExtendFormula_defined :
    ℒₛₑₜ-function₂[V] binaryZeroExtend via binaryZeroExtendFormula :=
  ⟨fun v ↦ by simp [binaryZeroExtendFormula, mem_ext_iff (y := binaryZeroExtend _ _),
    mem_binaryZeroExtend_iff]⟩

instance binaryZeroExtend_definable : ℒₛₑₜ-function₂[V] binaryZeroExtend :=
  binaryZeroExtendFormula_defined.to_definable

theorem binaryZeroExtend_value {s n i : V} (hi : i ∈ n) :
    (binaryZeroExtend s n) ‘ i = s ‘ i := value_definableGraph _ _ _ hi

theorem binaryZeroExtend_mem {s m n : V} (hs : s ∈ ((2 : ℕ) : V) ^ m) :
    binaryZeroExtend s n ∈ ((2 : ℕ) : V) ^ n := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  by_cases him : i ∈ m
  · exact function_value_mem hs him
  · rw [value_eq_empty_of_not_mem_domain (by rw [domain_eq_of_mem_function hs]; exact him)]
    simp [zero_def]

theorem binaryZeroExtend_extends {s m n : V} (hs : s ∈ ((2 : ℕ) : V) ^ m) (hmn : m ⊆ n) :
    s ⊆ binaryZeroExtend s n := by
  have : IsFunction s := IsFunction.of_mem hs
  intro p hp
  obtain ⟨i, hi, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hs p hp)
  exact (pair_mem_definableGraph_iff _ _ _ _ _).mpr ⟨hmn i hi, (value_eq_of_kpair_mem hp).symm⟩

noncomputable def binaryAppendRun (s a : V) : V :=
  insert ⟨ordinalAdd (domain s) a, (1 : V)⟩ₖ
    (binaryZeroExtend s (ordinalAdd (domain s) a))

instance binaryAppendRunFormula_defined :
    ℒₛₑₜ-function₂[V] binaryAppendRun via binaryAppendRunFormula :=
  ⟨fun v ↦ by simp [binaryAppendRunFormula, binaryAppendRun]⟩

instance binaryAppendRun_definable : ℒₛₑₜ-function₂[V] binaryAppendRun :=
  binaryAppendRunFormula_defined.to_definable

theorem binaryAppendRun_mem_function {s m a : V} (hs : s ∈ ((2 : ℕ) : V) ^ m) :
    binaryAppendRun s a ∈ ((2 : ℕ) : V) ^ succ (ordinalAdd m a) := by
  unfold binaryAppendRun
  rw [domain_eq_of_mem_function hs]
  exact function_append_mem (binaryZeroExtend_mem hs) (by simp)

theorem binaryAppendRun_mem {s a : V} (hs : s ∈ binarySequences V) (ha : a ∈ (ω : V)) :
    binaryAppendRun s a ∈ binarySequences V := by
  obtain ⟨m, hm, hsm⟩ := (mem_binarySequences_iff s).mp hs
  exact (mem_binarySequences_iff _).mpr
    ⟨succ (ordinalAdd m a), ω_succ_closed (ordinalAdd_natural hm ha), binaryAppendRun_mem_function hsm⟩

theorem binaryAppendRun_domain {s m a : V} (hs : s ∈ ((2 : ℕ) : V) ^ m) :
    domain (binaryAppendRun s a) = succ (ordinalAdd m a) :=
  domain_eq_of_mem_function (binaryAppendRun_mem_function hs)

theorem binaryAppendRun_extends {s a : V} (hs : s ∈ binarySequences V) (ha : a ∈ (ω : V)) :
    s ⊆ binaryAppendRun s a := by
  have := IsOrdinal.of_mem ha
  obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  intro p hp
  exact mem_insert.mpr (Or.inr (binaryZeroExtend_extends hsf (subset_ordinalAdd _ a) p hp))

theorem binaryAppendRun_separator {s a : V} (hs : s ∈ binarySequences V) :
    (binaryAppendRun s a) ‘ (ordinalAdd (domain s) a) = 1 := by
  obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  have : IsFunction (binaryAppendRun s a) := IsFunction.of_mem (binaryAppendRun_mem_function hsf)
  exact value_eq_of_kpair_mem (by simp [binaryAppendRun])

theorem binaryAppendRun_zero {s a k : V} (hs : s ∈ binarySequences V)
    (hk : k ∈ ordinalAdd (domain s) a) (hks : k ∉ domain s) :
    (binaryAppendRun s a) ‘ k = 0 := by
  obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  have hz := binaryZeroExtend_mem (n := ordinalAdd (domain s) a) hsf
  have : IsFunction (binaryZeroExtend s (ordinalAdd (domain s) a)) := IsFunction.of_mem hz
  have : IsFunction (binaryAppendRun s a) := IsFunction.of_mem (binaryAppendRun_mem_function hsf)
  have hpair : ⟨k, (binaryZeroExtend s (ordinalAdd (domain s) a)) ‘ k⟩ₖ ∈ binaryAppendRun s a :=
    mem_insert.mpr (Or.inr (kpair_value_mem (by rw [domain_eq_of_mem_function hz]; exact hk)))
  rw [value_eq_of_kpair_mem hpair, binaryZeroExtend_value hk,
    value_eq_empty_of_not_mem_domain hks]
  rfl

theorem binaryAppendRun_disagree {s a b : V} (hs : s ∈ binarySequences V)
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hab : a ∈ b) :
    Incompatible (binaryAppendRun s a) (binaryAppendRun s b) := by
  have := IsOrdinal.of_mem ha
  have := IsOrdinal.of_mem hb
  obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  let k := ordinalAdd (domain s) a
  have hkb : k ∈ ordinalAdd (domain s) b := ordinalAdd_mem hab
  have hkn : k ∉ domain s := fun h ↦ mem_irrefl k (subset_ordinalAdd (domain s) a k h)
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [binaryAppendRun_domain hsf]
    exact mem_succ_self k
  · rw [binaryAppendRun_domain hsf]
    exact mem_succ_iff.mpr (Or.inr hkb)
  · rw [binaryAppendRun_separator hs, binaryAppendRun_zero hs hkb hkn]
    exact Ne.symm zero_ne_one

end ZFVP
