import ZFVP.SetTheory.UsubaLSSequence
import ZFVP.SetTheory.IncreasingSequenceCofinality

/-! The definable LS targets have prescribed cofinality. In particular,
for each infinite regular `κ`, unbounded LS cardinals give singular limits
of LS cardinals of cofinality `κ` above any prescribed ordinal. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem usubaLSLimit_cofinality
    (hLS : ∀ β : V, IsOrdinal β → ∃ κ : V, β ∈ κ ∧ IsLSCardinal κ)
    {ξ α : V} [IsOrdinal ξ] [IsOrdinal α]
    (hlim : ∀ j ∈ α, succ j ∈ α) :
    internalCofinality (usubaLSLimit ξ α) = internalCofinality α := by
  let f := definableGraph α (usubaLSSequence ξ) (by definability)
  have hf : f ∈ (usubaLSLimit ξ α) ^ α :=
    definableGraph_mem_function_of_mapsTo _ _ _ _
      (fun i hi ↦ usubaLSSequence_mem_limit hLS hlim hi)
  have hval (i : V) (hi : i ∈ α) : f ‘ i = usubaLSSequence ξ i :=
    value_definableGraph _ _ _ hi
  apply increasingSequence_cofinality hf
  · intro i hi j hj hij
    let := IsOrdinal.of_mem hj
    rw [hval i hi, hval j hj]
    exact usubaLSSequence_increasing hLS hij
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := (mem_usubaLSLimit _ _ _).mp hx
    exact ⟨i, hi, (hval i hi).symm ▸ hxi⟩

theorem usubaLSLimit_cofinally_LS
    (hLS : ∀ β : V, IsOrdinal β → ∃ κ : V, β ∈ κ ∧ IsLSCardinal κ)
    {ξ α : V} [IsOrdinal ξ] [IsOrdinal α]
    (hlim : ∀ j ∈ α, succ j ∈ α) :
    ∀ β ∈ usubaLSLimit ξ α,
      ∃ μ ∈ usubaLSLimit ξ α, β ∈ μ ∧ IsLSCardinal μ := by
  intro β hβ
  obtain ⟨j, hj, hβj⟩ := (mem_usubaLSLimit _ _ _).mp hβ
  let := IsOrdinal.of_mem hj
  exact ⟨usubaLSSequence ξ j, usubaLSSequence_mem_limit hLS hlim hj,
    hβj, (usubaLSSequence_spec hLS ξ j).2⟩

theorem singularLS_prescribed_regular_cofinality
    (hLS : ∀ β : V, IsOrdinal β → ∃ κ : V, β ∈ κ ∧ IsLSCardinal κ)
    {κ : V} (hκ : IsRegularCardinal κ) (ξ : V) [IsOrdinal ξ] :
    ∃ lam : V, ξ ∈ lam ∧ IsLSCardinal lam ∧ internalCofinality lam = κ ∧
      internalCofinality lam ∈ lam ∧
      ∀ β ∈ lam, ∃ μ ∈ lam, β ∈ μ ∧ IsLSCardinal μ := by
  let := hκ.1.1
  have : IsOrdinal (ξ ∪ κ) := ordinal_union_ordinal _ _
  have hne : IsNonempty κ := ⟨∅, hκ.2.1 ∅ (by simp)⟩
  have hlim : ∀ j ∈ κ, succ j ∈ κ := fun j hj ↦ regularCardinal_succ_closed hκ hj
  have hs := usubaLSLimit_isLS hLS (ξ := ξ ∪ κ) hne hlim
  have hcf : internalCofinality (usubaLSLimit (ξ ∪ κ) κ) = κ :=
    (usubaLSLimit_cofinality hLS hlim).trans hκ.2.2
  refine ⟨usubaLSLimit (ξ ∪ κ) κ,
    ordinal_mem_of_subset_mem (subset_union_left _ _) hs.1, hs.2, hcf, ?_,
    usubaLSLimit_cofinally_LS hLS hlim⟩
  rw [hcf]
  exact ordinal_mem_of_subset_mem (subset_union_right _ _) hs.1

end ZFVP
