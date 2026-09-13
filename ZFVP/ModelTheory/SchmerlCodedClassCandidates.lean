import ZFVP.ModelTheory.SchmerlCodedClassColors
import ZFVP.ModelTheory.SchmerlCodedBranchFilter

/-! Cofinal candidates of the fixed branch clause are actual internal sets.
The weak coloring makes their selected-level restrictions full cofinal branches,
so the no-new-branches theorem applies to the candidates used by the sentence. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedClassCandidate (M κ c g b : V) : V :=
  {x ∈ codedClassNodes M ; b ∈ codedClassNodes M ∧
    ∃ y ∈ codedSelectedClassNodes M κ c,
      (⟨y, b⟩ₖ ∈ codedClassOrder M ∨ ⟨b, y⟩ₖ ∈ codedClassOrder M ∧ g ‘ b = g ‘ y) ∧
      ⟨x, y⟩ₖ ∈ codedClassOrder M}

theorem mem_codedClassCandidate (M κ c g b x : V) :
    x ∈ codedClassCandidate M κ c g b ↔ x ∈ codedClassNodes M ∧ b ∈ codedClassNodes M ∧
      ∃ y ∈ codedSelectedClassNodes M κ c,
        (⟨y, b⟩ₖ ∈ codedClassOrder M ∨ ⟨b, y⟩ₖ ∈ codedClassOrder M ∧ g ‘ b = g ‘ y) ∧
        ⟨x, y⟩ₖ ∈ codedClassOrder M := mem_sep_iff

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)
variable {κ c g b : V} [IsOrdinal κ]
variable (hc : IsInternalCofinalStrictChain κ (codedOrdinals R.code) (codedOrdinalOrder R.code) c)

omit [IsOrdinal κ] in
theorem codedClassCandidate_witness {x : V} (hx : x ∈ codedClassCandidate R.code κ c g b) :
    ∃ y ∈ codedClassCandidate R.code κ c g b ∩ codedSelectedClassNodes R.code κ c,
      ⟨x, y⟩ₖ ∈ codedClassOrder R.code := by
  obtain ⟨_, hb, y, hy, hcone, hxy⟩ := (mem_codedClassCandidate _ _ _ _ _ _).mp hx
  have hyT := ((mem_codedSelectedClassNodes _ _ _ _).mp hy).1
  exact ⟨y, mem_inter_iff.mpr ⟨(mem_codedClassCandidate _ _ _ _ _ _).mpr
    ⟨hyT, hb, y, hy, hcone, R.classOrder_poset.1.2.1 y hyT⟩, hy⟩, hxy⟩

omit [IsOrdinal κ] in
theorem codedClassCandidate_downward {x y : V} (hx : x ∈ codedClassNodes R.code)
    (hy : y ∈ codedClassCandidate R.code κ c g b) (hxy : ⟨x, y⟩ₖ ∈ codedClassOrder R.code) :
    x ∈ codedClassCandidate R.code κ c g b := by
  obtain ⟨hyT, hb, z, hz, hcone, hyz⟩ := (mem_codedClassCandidate _ _ _ _ _ _).mp hy
  exact (mem_codedClassCandidate _ _ _ _ _ _).mpr ⟨hx, hb, z, hz, hcone,
    R.classOrder_poset.1.2.2 x hx y hyT z ((mem_codedSelectedClassNodes _ _ _ _).mp hz).1 hxy hyz⟩

omit [IsOrdinal κ] in
theorem codedClassCandidate_eq_filter :
    codedClassCandidate R.code κ c g b = codedBranchFilter R.code
      (codedClassCandidate R.code κ c g b ∩ codedSelectedClassNodes R.code κ c) := by
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := R.codedClassCandidate_witness hx
    exact (mem_codedBranchFilter _ _ _).mpr ⟨((mem_codedClassCandidate _ _ _ _ _ _).mp hx).1, y, hy, hxy⟩
  · intro hx
    obtain ⟨hxT, y, hy, hxy⟩ := (mem_codedBranchFilter _ _ _).mp hx
    exact R.codedClassCandidate_downward hxT (mem_inter_iff.mp hy).1 hxy

omit [IsOrdinal κ] in
theorem codedClassCandidate_chain
    (hb : b ∈ codedSelectedClassNodes R.code κ c)
    (hweak : InternallyWeakSpecialization (codedSelectedClassNodes R.code κ c) (codedSelectedClassOrder R.code κ c) g)
    {x y : V} (hx : x ∈ codedClassCandidate R.code κ c g b) (hy : y ∈ codedClassCandidate R.code κ c g b) :
    ⟨x, y⟩ₖ ∈ codedClassOrder R.code ∨ ⟨y, x⟩ₖ ∈ codedClassOrder R.code := by
  obtain ⟨hxT, hbT, u, hu, hbu, hxu⟩ := (mem_codedClassCandidate _ _ _ _ _ _).mp hx
  obtain ⟨hyT, _, v, hv, hbv, hyv⟩ := (mem_codedClassCandidate _ _ _ _ _ _).mp hy
  have huT := ((mem_codedSelectedClassNodes _ _ _ _).mp hu).1
  have hvT := ((mem_codedSelectedClassNodes _ _ _ _).mp hv).1
  have huv : ⟨u, v⟩ₖ ∈ codedClassOrder R.code ∨ ⟨v, u⟩ₖ ∈ codedClassOrder R.code := by
    rcases hbu with hub | ⟨hbu, hgu⟩ <;> rcases hbv with hvb | ⟨hbv, hgv⟩
    · exact R.classOrder_below_linear huT hvT hbT hub hvb
    · exact Or.inl (R.classOrder_poset.1.2.2 u huT b hbT v hvT hub hbv)
    · exact Or.inr (R.classOrder_poset.1.2.2 v hvT b hbT u huT hvb hbu)
    · exact (hweak b hb u hu v hv
        ((pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr ⟨hbu, hb, hu⟩)
        ((pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr ⟨hbv, hb, hv⟩) hgu hgv).imp
        (fun h ↦ (mem_inter_iff.mp h).1) (fun h ↦ (mem_inter_iff.mp h).1)
  rcases huv with huv | hvu
  · exact R.classOrder_below_linear hxT hyT hvT
      (R.classOrder_poset.1.2.2 x hxT u huT v hvT hxu huv) hyv
  · exact R.classOrder_below_linear hxT hyT huT hxu
      (R.classOrder_poset.1.2.2 y hyT v hvT u huT hyv hvu)

include hc in
theorem codedClassCandidate_selected_branch
    (hb : b ∈ codedSelectedClassNodes R.code κ c)
    (hweak : InternallyWeakSpecialization (codedSelectedClassNodes R.code κ c) (codedSelectedClassOrder R.code κ c) g)
    (hcof : ∀ i ∈ κ, ∃ x ∈ codedClassCandidate R.code κ c g b,
      ⟨c ‘ i, (codedClassLevels R.code) ‘ x⟩ₖ ∈ codedOrdinalOrder R.code) :
    IsInternalCofinalBranch (codedSelectedClassNodes R.code κ c) (codedSelectedClassOrder R.code κ c) κ
      (codedSelectedClassRank R.code κ c) (codedClassCandidate R.code κ c g b ∩ codedSelectedClassNodes R.code κ c) := by
  refine ⟨fun _ hx ↦ (mem_inter_iff.mp hx).2, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨hxB, hxT⟩ := mem_inter_iff.mp hx
    obtain ⟨hyB, hyT⟩ := mem_inter_iff.mp hy
    exact (R.codedClassCandidate_chain hb hweak hxB hyB).imp
      (fun h ↦ (pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr ⟨h, hxT, hyT⟩)
      (fun h ↦ (pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr ⟨h, hyT, hxT⟩)
  · intro i hi
    obtain ⟨x, hx, hix⟩ := hcof i hi
    obtain ⟨y, hy, hxy⟩ := R.codedClassCandidate_witness hx
    have hxT := ((mem_codedClassCandidate _ _ _ _ _ _).mp hx).1
    have hyT := (mem_inter_iff.mp hy).2
    have hyFull := ((mem_codedSelectedClassNodes _ _ _ _).mp hyT).1
    have hr := codedSelectedClassRank_spec hc hyT
    have hiy := R.ordinalOrder_poset.1.2.2 _ (function_value_mem hc.1 hi)
      _ (function_value_mem R.classLevels_function hxT) _ (function_value_mem R.classLevels_function hyFull)
      hix (R.classLevels_monotone hxT hyFull hxy)
    rw [hr.2] at hiy
    exact ⟨y, hy, hc.index_mono R.ordinalOrder_poset hi hr.1 hiy⟩
  · intro x hx y hy hxy
    exact mem_inter_iff.mpr ⟨R.codedClassCandidate_downward
      ((mem_codedSelectedClassNodes _ _ _ _).mp hx).1 (mem_inter_iff.mp hy).1 (mem_inter_iff.mp hxy).1, hx⟩

end ZFVP.BinaryRelationRepresentation
