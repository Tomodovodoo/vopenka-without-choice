import ZFVP.ModelTheory.SchmerlInternalClosedPreservation
import ZFVP.SetTheory.CountablePartialFunctions
import ZFVP.SetTheory.HartogsRegularChoice

/-! The usual forcing of initial segments of a diamond sequence, coded
inside a ZF model. Conditions are functions of ordinal length below kappa,
whose value at each index is a subset of that index. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def diamondConditions (κ : V) : V :=
  {p ∈ shorterSequences κ (℘ κ) ; ∀ i ∈ domain p, (p ‘ i) ⊆ i}

theorem mem_diamondConditions (κ p : V) : p ∈ diamondConditions κ ↔
    domain p ∈ κ ∧ p ∈ (℘ κ) ^ domain p ∧ ∀ i ∈ domain p, (p ‘ i) ⊆ i := by
  simp only [diamondConditions, mem_sep_iff, mem_shorterSequences_domain, and_assoc]

instance diamondConditions_definable : ℒₛₑₜ-function₁[V] diamondConditions := by
  have h : ℒₛₑₜ-relation[V] (fun P κ ↦ ∀ p, p ∈ P ↔
    domain p ∈ κ ∧ p ∈ (℘ κ) ^ domain p ∧ ∀ i ∈ domain p, (p ‘ i) ⊆ i) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_diamondConditions]
  rfl

noncomputable def diamondOrder (κ : V) : V := reverseInclusionOrder (diamondConditions κ)

theorem diamond_poset (κ : V) : IsForcingPoset (diamondConditions κ) (diamondOrder κ) :=
  reverseInclusionOrder_poset _

theorem diamondCondition_function {κ p : V} (hp : p ∈ diamondConditions κ) : IsFunction p :=
  IsFunction.of_mem ((mem_diamondConditions κ p).mp hp).2.1

theorem empty_mem_diamondConditions {κ : V} (hzero : (∅ : V) ∈ κ) :
    (∅ : V) ∈ diamondConditions κ := by
  apply (mem_diamondConditions κ ∅).mpr
  simp only [domain_empty]
  refine ⟨hzero, ?_, fun i hi ↦ False.elim (not_mem_empty hi)⟩
  simp [mem_function_iff]

theorem diamond_top {κ : V} (hzero : (∅ : V) ∈ κ) :
    IsForcingTop (diamondConditions κ) (diamondOrder κ) ∅ := by
  refine ⟨empty_mem_diamondConditions hzero, fun p hp ↦ ?_⟩
  exact (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hp, empty_mem_diamondConditions hzero, empty_subset _⟩

/-- Union is a condition for every internal descending omega-sequence. -/
theorem diamond_chain_union {κ f : V} (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hf : IsForcingDescending (diamondConditions κ) (diamondOrder κ) (ω : V) f) :
    ⋃ˢ range f ∈ diamondConditions κ := by
  let : IsOrdinal κ := hκ.1.1
  let : IsFunction f := IsFunction.of_mem hf.1
  have hP (p : V) (hp : p ∈ range f) : p ∈ diamondConditions κ :=
    range_subset_of_mem_function hf.1 p hp
  have hfun (p : V) (hp : p ∈ range f) : IsFunction p := diamondCondition_function (hP p hp)
  have hcompat : CompatibleFunctionFamily (range f) :=
    compatible_range_of_increasing hf.1
      (fun p hp ↦ diamondCondition_function hp)
      (fun i hi j hj ↦ ((pair_mem_reverseInclusionOrder _ _ _).mp (hf.2 i hi j hj)).2.2)
  let q := ⋃ˢ range f
  let : IsFunction q := isFunction_sUnion hfun hcompat
  let d := definableGraph (ω : V) (fun i ↦ domain (f ‘ i)) (by definability)
  have hd : d ∈ κ ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun i hi ↦ ((mem_diamondConditions κ _).mp (function_value_mem hf.1 hi)).1)
  have hqd : domain q = ⋃ˢ range d := domain_sUnion_range_eq (domain_eq_of_mem_function hf.1)
  have hdord : IsOrdinal (domain q) := by
    rw [hqd]
    exact IsOrdinal.sUnion (fun x hx ↦ IsOrdinal.of_mem (range_subset_of_mem_function hd x hx))
  let : IsOrdinal (domain q) := hdord
  obtain ⟨β, hβ, hb⟩ := regularCardinal_maps_bounded hκ hω hd
  let : IsOrdinal β := IsOrdinal.of_mem hβ
  have hqβ : domain q ⊆ β := by
    rw [hqd]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
    let : IsFunction d := IsFunction.of_mem hd
    have hi := domain_eq_of_mem_function hd ▸ mem_domain_of_kpair_mem hiy
    have hyβ := value_eq_of_kpair_mem hiy ▸ hb i hi
    exact IsOrdinal.toIsTransitive.transitive y hyβ x hxy
  have hqκ : domain q ∈ κ := ordinal_mem_of_subset_mem hqβ hβ
  apply (mem_diamondConditions κ q).mpr
  refine ⟨hqκ, ?_, ?_⟩
  · apply mem_function.intro
    · intro z hz
      obtain ⟨p, hp, hzp⟩ := mem_sUnion_iff.mp hz
      let : IsFunction p := hfun p hp
      obtain ⟨i, x, rfl⟩ := IsFunction.mem_eq_kpair hzp
      exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hz,
        range_subset_of_mem_function ((mem_diamondConditions κ p).mp (hP p hp)).2.1
          _ (mem_range_of_kpair_mem hzp)⟩
    · intro i hi
      obtain ⟨x, hix⟩ := mem_domain_iff.mp hi
      exact ⟨x, hix, fun y hiy ↦ IsFunction.unique hiy hix⟩
  · intro i hi
    obtain ⟨p, hp, hip⟩ := (mem_domain_sUnion_iff _ _).mp hi
    rw [value_sUnion_of_mem hfun hcompat hp hip]
    exact ((mem_diamondConditions κ p).mp (hP p hp)).2.2 i hip

theorem diamond_closedAt_omega {κ : V} (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ) :
    IsForcingClosedAt (diamondConditions κ) (diamondOrder κ) (ω : V) := by
  intro f hf
  let : IsFunction f := IsFunction.of_mem hf.1
  have hq := diamond_chain_union hκ hω hf
  refine ⟨⋃ˢ range f, hq, fun i hi ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hq, function_value_mem hf.1 hi, ?_⟩⟩
  intro z hz
  exact mem_sUnion_iff.mpr ⟨f ‘ i, mem_range_of_kpair_mem
    (kpair_value_mem ((domain_eq_of_mem_function hf.1).symm ▸ hi)), hz⟩

end ZFVP.Schmerl
