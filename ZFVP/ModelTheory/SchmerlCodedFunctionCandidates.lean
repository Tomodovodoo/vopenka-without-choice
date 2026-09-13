import ZFVP.ModelTheory.SchmerlCodedFunctionBranchFilter
import ZFVP.ModelTheory.SchmerlInternalBranchCore

/-! A cofinal function candidate determines a branch on the selected domains.
Its full downward closure is the finite-function filter used by Rubin's clause. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedFunctionCandidate (M s κ c g b : V) : V :=
  {x ∈ codedFunctionNodes M s ; b ∈ codedFunctionNodes M s ∧
    ∃ y ∈ codedSelectedFunctionNodes M s κ c,
      (⟨y, b⟩ₖ ∈ codedFunctionOrder M s ∨
        ⟨b, y⟩ₖ ∈ codedFunctionOrder M s ∧ g ‘ b = g ‘ y) ∧
      ⟨x, y⟩ₖ ∈ codedFunctionOrder M s}

theorem mem_codedFunctionCandidate (M s κ c g b x : V) :
    x ∈ codedFunctionCandidate M s κ c g b ↔ x ∈ codedFunctionNodes M s ∧ b ∈ codedFunctionNodes M s ∧
      ∃ y ∈ codedSelectedFunctionNodes M s κ c,
        (⟨y, b⟩ₖ ∈ codedFunctionOrder M s ∨
          ⟨b, y⟩ₖ ∈ codedFunctionOrder M s ∧ g ‘ b = g ‘ y) ∧
        ⟨x, y⟩ₖ ∈ codedFunctionOrder M s := mem_sep_iff

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation
open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W) (s : W)
variable {κ c g b : V} [IsOrdinal κ]
variable (hc : IsInternalCofinalStrictChain κ (codedFiniteDomains R.code (R.equiv s).val)
  (codedFiniteDomainOrder R.code (R.equiv s).val) c)

omit [IsOrdinal κ] in
theorem codedFunctionCandidate_witness {x : V}
    (hx : x ∈ codedFunctionCandidate R.code (R.equiv s).val κ c g b) :
    ∃ y ∈ codedFunctionCandidate R.code (R.equiv s).val κ c g b ∩
        codedSelectedFunctionNodes R.code (R.equiv s).val κ c,
      ⟨x, y⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val := by
  obtain ⟨_, hb, y, hy, hcone, hxy⟩ := (mem_codedFunctionCandidate _ _ _ _ _ _ _).mp hx
  have hyT := ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hy).1
  exact ⟨y, mem_inter_iff.mpr ⟨(mem_codedFunctionCandidate _ _ _ _ _ _ _).mpr
    ⟨hyT, hb, y, hy, hcone, (R.functionOrder_poset s).1.2.1 y hyT⟩, hy⟩, hxy⟩

omit [IsOrdinal κ] in
theorem codedFunctionCandidate_downward {x y : V}
    (hx : x ∈ codedFunctionNodes R.code (R.equiv s).val)
    (hy : y ∈ codedFunctionCandidate R.code (R.equiv s).val κ c g b)
    (hxy : ⟨x, y⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val) :
    x ∈ codedFunctionCandidate R.code (R.equiv s).val κ c g b := by
  obtain ⟨hyT, hb, z, hz, hcone, hyz⟩ := (mem_codedFunctionCandidate _ _ _ _ _ _ _).mp hy
  exact (mem_codedFunctionCandidate _ _ _ _ _ _ _).mpr ⟨hx, hb, z, hz, hcone,
    (R.functionOrder_poset s).1.2.2 x hx y hyT z ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hz).1 hxy hyz⟩

omit [IsOrdinal κ] in
theorem codedFunctionCandidate_eq_filter :
    codedFunctionCandidate R.code (R.equiv s).val κ c g b =
      codedFunctionBranchFilter R.code (R.equiv s).val
        (codedFunctionCandidate R.code (R.equiv s).val κ c g b ∩
          codedSelectedFunctionNodes R.code (R.equiv s).val κ c) := by
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := R.codedFunctionCandidate_witness s hx
    exact (mem_codedFunctionBranchFilter _ _ _ _).mpr
      ⟨((mem_codedFunctionCandidate _ _ _ _ _ _ _).mp hx).1, y, hy, hxy⟩
  · intro hx
    obtain ⟨hxT, y, hy, hxy⟩ := (mem_codedFunctionBranchFilter _ _ _ _).mp hx
    exact R.codedFunctionCandidate_downward s hxT (mem_inter_iff.mp hy).1 hxy

include hc

theorem codedFunctionCandidate_selected_chain
    (hb : b ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
    (hweak : InternallyWeakSpecialization (codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
      (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) g)
    {x y : V}
    (hx : x ∈ codedFunctionCandidate R.code (R.equiv s).val κ c g b ∩
      codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
    (hy : y ∈ codedFunctionCandidate R.code (R.equiv s).val κ c g b ∩
      codedSelectedFunctionNodes R.code (R.equiv s).val κ c) :
    ⟨x, y⟩ₖ ∈ codedSelectedFunctionOrder R.code (R.equiv s).val κ c ∨
      ⟨y, x⟩ₖ ∈ codedSelectedFunctionOrder R.code (R.equiv s).val κ c := by
  obtain ⟨hxB, hxS⟩ := mem_inter_iff.mp hx
  obtain ⟨hyB, hyS⟩ := mem_inter_iff.mp hy
  obtain ⟨hxT, hbT, u, hu, hbu, hxu⟩ := (mem_codedFunctionCandidate _ _ _ _ _ _ _).mp hxB
  obtain ⟨hyT, _, v, hv, hbv, hyv⟩ := (mem_codedFunctionCandidate _ _ _ _ _ _ _).mp hyB
  have huT := ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hu).1
  have hvT := ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hv).1
  have hsel {a d : V} (ha : a ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
      (hd : d ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
      (had : ⟨a, d⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val) :
      ⟨a, d⟩ₖ ∈ codedSelectedFunctionOrder R.code (R.equiv s).val κ c :=
    (pair_mem_codedSelectedFunctionOrder _ _ _ _ _ _).mpr ⟨had, ha, hd⟩
  have huv : ⟨u, v⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val ∨
      ⟨v, u⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val := by
    rcases hbu with hub | ⟨hbu, hgu⟩ <;> rcases hbv with hvb | ⟨hbv, hgv⟩
    · exact ((R.selectedFunctionTree s hc).below_linear u hu v hv b hb (hsel hu hb hub) (hsel hv hb hvb)).imp
        (fun h ↦ (mem_inter_iff.mp h).1) (fun h ↦ (mem_inter_iff.mp h).1)
    · exact Or.inl ((R.functionOrder_poset s).1.2.2 u huT b hbT v hvT hub hbv)
    · exact Or.inr ((R.functionOrder_poset s).1.2.2 v hvT b hbT u huT hvb hbu)
    · exact (hweak b hb u hu v hv (hsel hb hu hbu) (hsel hb hv hbv) hgu hgv).imp
        (fun h ↦ (mem_inter_iff.mp h).1) (fun h ↦ (mem_inter_iff.mp h).1)
  rcases huv with huv | hvu
  · exact (R.selectedFunctionTree s hc).below_linear x hxS y hyS v hv
      (hsel hxS hv ((R.functionOrder_poset s).1.2.2 x hxT u huT v hvT hxu huv)) (hsel hyS hv hyv)
  · exact (R.selectedFunctionTree s hc).below_linear x hxS y hyS u hu
      (hsel hxS hu hxu) (hsel hyS hu ((R.functionOrder_poset s).1.2.2 y hyT v hvT u huT hyv hvu))

theorem codedFunctionCandidate_selected_branch
    (hb : b ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
    (hweak : InternallyWeakSpecialization (codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
      (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) g)
    (hcof : ∀ i ∈ κ, ∃ x ∈ codedFunctionCandidate R.code (R.equiv s).val κ c g b,
      ⟨c ‘ i, (codedFunctionDomains R.code (R.equiv s).val) ‘ x⟩ₖ ∈
        codedFiniteDomainOrder R.code (R.equiv s).val) :
    IsInternalCofinalBranch (codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
      (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) κ
      (codedSelectedFunctionRank R.code (R.equiv s).val κ c)
      (codedFunctionCandidate R.code (R.equiv s).val κ c g b ∩
        codedSelectedFunctionNodes R.code (R.equiv s).val κ c) := by
  refine ⟨fun _ hx ↦ (mem_inter_iff.mp hx).2,
    fun _ hx _ hy ↦ R.codedFunctionCandidate_selected_chain s hc hb hweak hx hy, ?_, ?_⟩
  · intro i hi
    obtain ⟨x, hx, hix⟩ := hcof i hi
    obtain ⟨y, hy, hxy⟩ := R.codedFunctionCandidate_witness s hx
    have hxT := ((mem_codedFunctionCandidate _ _ _ _ _ _ _).mp hx).1
    have hyT := (mem_inter_iff.mp hy).2
    have hyFull := ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hyT).1
    have hr := codedSelectedFunctionRank_spec hc hyT
    have hiy := (R.finiteDomainOrder_poset s).1.2.2 _ (function_value_mem hc.1 hi)
      _ (function_value_mem (R.functionDomains_function s) hxT)
      _ (function_value_mem (R.functionDomains_function s) hyFull)
      hix (R.functionDomains_monotone s hxT hyFull hxy)
    rw [hr.2] at hiy
    exact ⟨y, hy, hc.index_mono (R.finiteDomainOrder_poset s) hi hr.1 hiy⟩
  · intro x hx y hy hxy
    exact mem_inter_iff.mpr ⟨R.codedFunctionCandidate_downward s
      ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hx).1 (mem_inter_iff.mp hy).1 (mem_inter_iff.mp hxy).1, hx⟩

end ZFVP.BinaryRelationRepresentation
