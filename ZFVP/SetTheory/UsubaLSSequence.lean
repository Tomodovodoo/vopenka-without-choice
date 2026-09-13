import ZFVP.SetTheory.LowenheimSkolemCardinals
import ZFVP.SetTheory.OrdinalClosureSequence
import ZFVP.SetTheory.LeastOrdinalChoice

/-! Definable targets for the collapse iteration in Usuba Corollary 4.8.
At each stage take the least LS cardinal above the seed and the supremum
of preceding stages. Every limit of this sequence is again LS. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def usubaNextLS (α : V) : V :=
  leastOrdinalOrZero (fun a κ ↦ a ∈ κ ∧ IsLSCardinal κ) (by definability) α

instance usubaNextLS_definable : ℒₛₑₜ-function₁[V] usubaNextLS := by
  unfold usubaNextLS
  definability

instance usubaNextLS_ordinal (α : V) : IsOrdinal (usubaNextLS α) :=
  leastOrdinalOrZero_ordinal _ _ α

theorem usubaNextLS_spec
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (α : V) [IsOrdinal α] :
    α ∈ usubaNextLS α ∧ IsLSCardinal (usubaNextLS α) := by
  obtain ⟨κ, hακ, hκ⟩ := hLS α inferInstance
  exact (leastOrdinalOrZero_spec (fun a κ ↦ a ∈ κ ∧ IsLSCardinal κ)
    (by definability) α ⟨κ, hκ.1.1, hακ, hκ⟩).2.1

theorem usubaNextLS_least {α κ : V} (hακ : α ∈ κ) (hκ : IsLSCardinal κ) :
    usubaNextLS α ⊆ κ :=
  (leastOrdinalOrZero_spec _ _ α ⟨κ, hκ.1.1, hακ, hκ⟩).2.2 κ hκ.1.1 ⟨hακ, hκ⟩

noncomputable def usubaLSSequence (ξ i : V) : V :=
  ordinalClosureSequence usubaNextLS (by definability) ξ i

instance usubaLSSequence_definable (ξ : V) : ℒₛₑₜ-function₁[V] (usubaLSSequence ξ) := by
  unfold usubaLSSequence
  definability

theorem usubaLSSequence_eq (ξ i : V) [IsOrdinal i] :
    usubaLSSequence ξ i = usubaNextLS
      (ξ ∪ ⋃ˢ repl (usubaLSSequence ξ) (by definability) i) :=
  ordinalClosureSequence_eq usubaNextLS (by definability) ξ i

instance usubaLSSequence_ordinal (ξ i : V) [IsOrdinal i] :
    IsOrdinal (usubaLSSequence ξ i) := by
  rw [usubaLSSequence_eq]
  infer_instance

theorem usubaLSSequence_spec
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (ξ i : V) [IsOrdinal ξ] [IsOrdinal i] :
    ξ ∈ usubaLSSequence ξ i ∧ IsLSCardinal (usubaLSSequence ξ i) := by
  let u := ⋃ˢ repl (usubaLSSequence ξ) (by definability) i
  have hu : IsOrdinal u := IsOrdinal.sUnion (by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := (repl_spec _).mp hy
    let := IsOrdinal.of_mem hj
    infer_instance)
  let := hu
  have : IsOrdinal (ξ ∪ u) := ordinal_union_ordinal _ _
  rw [usubaLSSequence_eq]
  have hs := usubaNextLS_spec hLS (ξ ∪ u)
  exact ⟨ordinal_mem_of_subset_mem (subset_union_left _ _) hs.1, hs.2⟩

theorem usubaLSSequence_increasing
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    {ξ i j : V} [IsOrdinal ξ] [IsOrdinal j] (hij : i ∈ j) :
    usubaLSSequence ξ i ∈ usubaLSSequence ξ j := by
  let := IsOrdinal.of_mem hij
  let u := ⋃ˢ repl (usubaLSSequence ξ) (by definability) j
  have hu : IsOrdinal u := IsOrdinal.sUnion (by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := (repl_spec _).mp hy
    let := IsOrdinal.of_mem hk
    infer_instance)
  let := hu
  have : IsOrdinal (ξ ∪ u) := ordinal_union_ordinal _ _
  rw [usubaLSSequence_eq ξ j]
  have hsub : usubaLSSequence ξ i ⊆ u :=
    subset_sUnion_of_mem ((repl_spec _).mpr ⟨i, hij, rfl⟩)
  exact ordinal_mem_of_subset_mem (subset_trans hsub (subset_union_right _ _))
    (usubaNextLS_spec hLS (ξ ∪ u)).1

noncomputable def usubaLSLimit (ξ α : V) : V :=
  ⋃ˢ repl (usubaLSSequence ξ) (by definability) α

instance usubaLSLimit_definable (ξ : V) : ℒₛₑₜ-function₁[V] (usubaLSLimit ξ) := by
  unfold usubaLSLimit
  definability

instance usubaLSLimit_ordinal (ξ α : V) [IsOrdinal α] :
    IsOrdinal (usubaLSLimit ξ α) := IsOrdinal.sUnion (by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := (repl_spec _).mp hy
  let := IsOrdinal.of_mem hi
  infer_instance)

theorem mem_usubaLSLimit (ξ α x : V) :
    x ∈ usubaLSLimit ξ α ↔ ∃ i ∈ α, x ∈ usubaLSSequence ξ i := by
  simp only [usubaLSLimit, mem_sUnion_iff]
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨i, hi, rfl⟩ := (repl_spec _).mp hy
    exact ⟨i, hi, hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨_, (repl_spec _).mpr ⟨i, hi, rfl⟩, hx⟩

theorem usubaLSSequence_mem_limit
    (hLS : ∀ β : V, IsOrdinal β → ∃ κ : V, β ∈ κ ∧ IsLSCardinal κ)
    {ξ α i : V} [IsOrdinal ξ] [IsOrdinal α]
    (hlim : ∀ j ∈ α, succ j ∈ α) (hi : i ∈ α) :
    usubaLSSequence ξ i ∈ usubaLSLimit ξ α := by
  let := IsOrdinal.of_mem hi
  exact (mem_usubaLSLimit _ _ _).mpr ⟨succ i, hlim i hi,
    usubaLSSequence_increasing hLS (mem_succ_self i)⟩

theorem usubaLSLimit_isLS
    (hLS : ∀ β : V, IsOrdinal β → ∃ κ : V, β ∈ κ ∧ IsLSCardinal κ)
    {ξ α : V} [IsOrdinal ξ] [IsOrdinal α] (hne : IsNonempty α)
    (hlim : ∀ j ∈ α, succ j ∈ α) :
    ξ ∈ usubaLSLimit ξ α ∧ IsLSCardinal (usubaLSLimit ξ α) := by
  obtain ⟨i, hi⟩ := hne
  let := IsOrdinal.of_mem hi
  have hξ : ξ ∈ usubaLSLimit ξ α :=
    (mem_usubaLSLimit _ _ _).mpr ⟨i, hi, (usubaLSSequence_spec hLS ξ i).1⟩
  refine ⟨hξ, lsCardinal_of_cofinally_ls ⟨ξ, hξ⟩ ?_⟩
  intro β hβ
  obtain ⟨j, hj, hβj⟩ := (mem_usubaLSLimit _ _ _).mp hβ
  let := IsOrdinal.of_mem hj
  exact ⟨usubaLSSequence ξ j, usubaLSSequence_mem_limit hLS hlim hj,
    hβj, (usubaLSSequence_spec hLS ξ j).2⟩

end ZFVP
