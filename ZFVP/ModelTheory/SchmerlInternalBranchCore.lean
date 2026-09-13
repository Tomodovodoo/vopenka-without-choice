import ZFVP.ModelTheory.SchmerlInternalBranchNames
import ZFVP.ModelTheory.SchmerlInternalSpecialization
import ZFVP.SetTheory.HartogsRegularChoice
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.FiniteCardinalArithmetic

/-! Separated internal branch markers give a core with only internally countable
chains. Its internal anchor map extends a strict coloring to a weak coloring. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure InternalSeparatedMarkerData (D S κ rank J m : V) : Prop where
  order : IsForcingPoset D S
  tree : InternalRankedTree D S κ rank
  marker_function : m ∈ D ^ J
  branches : ∀ B ∈ J, IsInternalCofinalBranch D S κ rank B
  marker_mem : ∀ B ∈ J, m ‘ B ∈ B
  separates : ∀ B ∈ J, ∀ C ∈ J, B ≠ C → ⟨m ‘ B, m ‘ C⟩ₖ ∈ S → m ‘ C ∉ B

noncomputable def internalBranchCore (D S J m : V) : V :=
  {x ∈ D ; ∀ B ∈ J, x ∈ B → ⟨x, m ‘ B⟩ₖ ∈ S}

theorem mem_internalBranchCore (D S J m x : V) :
    x ∈ internalBranchCore D S J m ↔
      x ∈ D ∧ ∀ B ∈ J, x ∈ B → ⟨x, m ‘ B⟩ₖ ∈ S := by
  simp only [internalBranchCore, mem_sep_iff]

instance internalBranchCore_definable : ℒₛₑₜ-function₄[V] internalBranchCore := by
  have h : ℒₛₑₜ-relation₅[V] (fun C D S J m ↦ ∀ x,
      x ∈ C ↔ x ∈ D ∧ ∀ B ∈ J, x ∈ B → ⟨x, m ‘ B⟩ₖ ∈ S) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_internalBranchCore]
  rfl

def InInternalMarkedTail (S m x B : V) : Prop := x ∈ B ∧ ⟨x, m ‘ B⟩ₖ ∉ S

instance inInternalMarkedTail_definable : ℒₛₑₜ-relation₄[V] InInternalMarkedTail := by
  unfold InInternalMarkedTail
  definability

namespace InternalSeparatedMarkerData

variable {D S κ rank J m : V} (h : InternalSeparatedMarkerData D S κ rank J m)

include h

theorem marker_in_domain {B : V} (hB : B ∈ J) : m ‘ B ∈ D :=
  function_value_mem h.marker_function hB

theorem marker_injective {B C : V} (hB : B ∈ J) (hC : C ∈ J)
    (he : m ‘ B = m ‘ C) : B = C := by
  by_contra hne
  apply h.separates B hB C hC hne
  · rw [he]
    exact h.order.1.2.1 _ (h.marker_in_domain hC)
  · rw [← he]
    exact h.marker_mem B hB

theorem marker_in_core {B : V} (hB : B ∈ J) : m ‘ B ∈ internalBranchCore D S J m := by
  refine (mem_internalBranchCore _ _ _ _ _).mpr ⟨h.marker_in_domain hB, ?_⟩
  intro C hC hmC
  rcases (h.branches C hC).2.1 _ hmC _ (h.marker_mem C hC) with hle | hle
  · exact hle
  · by_cases he : C = B
    · subst C
      exact h.order.1.2.1 _ (h.marker_in_domain hB)
    · exact False.elim (h.separates C hC B hB he hle hmC)

omit h in
theorem tail_not_core {x B : V} (hB : B ∈ J) (hx : InInternalMarkedTail S m x B) :
    x ∉ internalBranchCore D S J m := by
  intro hc
  exact hx.2 (((mem_internalBranchCore _ _ _ _ _).mp hc).2 B hB hx.1)

theorem marker_le_tail {x B : V} (hB : B ∈ J) (hx : InInternalMarkedTail S m x B) :
    ⟨m ‘ B, x⟩ₖ ∈ S :=
  ((h.branches B hB).2.1 _ hx.1 _ (h.marker_mem B hB)).resolve_left hx.2

theorem tail_unique {x B C : V} (hB : B ∈ J) (hC : C ∈ J)
    (hxB : InInternalMarkedTail S m x B) (hxC : InInternalMarkedTail S m x C) : B = C := by
  by_contra hne
  have hxD := (h.branches B hB).1 x hxB.1
  rcases h.tree.below_linear _ (h.marker_in_domain hB) _ (h.marker_in_domain hC) x hxD
      (h.marker_le_tail hB hxB) (h.marker_le_tail hC hxC) with hBC | hCB
  · exact h.separates B hB C hC hne hBC
      ((h.branches B hB).2.2.2 _ (h.marker_in_domain hC) x hxB.1 (h.marker_le_tail hC hxC))
  · exact h.separates C hC B hB (Ne.symm hne) hCB
      ((h.branches C hC).2.2.2 _ (h.marker_in_domain hB) x hxC.1 (h.marker_le_tail hB hxB))

omit h in
theorem exists_tail_of_not_core {x : V} (hx : x ∈ D)
    (hc : x ∉ internalBranchCore D S J m) : ∃ B ∈ J, InInternalMarkedTail S m x B := by
  classical
  by_contra hn
  apply hc
  refine (mem_internalBranchCore _ _ _ _ _).mpr ⟨hx, ?_⟩
  intro B hB hxB
  by_contra hle
  exact hn ⟨B, hB, hxB, hle⟩

end InternalSeparatedMarkerData

/-- A graph defined by separation, without choosing a branch externally. -/
noncomputable def internalBranchAnchor (D S J m : V) : V :=
  {a ∈ D ×ˢ D ;
    (kpair.π₁ a ∈ internalBranchCore D S J m ∧ kpair.π₂ a = kpair.π₁ a) ∨
      ∃ B ∈ J, InInternalMarkedTail S m (kpair.π₁ a) B ∧ kpair.π₂ a = m ‘ B}

theorem pair_mem_internalBranchAnchor (D S J m x y : V) :
    ⟨x, y⟩ₖ ∈ internalBranchAnchor D S J m ↔
      x ∈ D ∧ y ∈ D ∧ ((x ∈ internalBranchCore D S J m ∧ y = x) ∨
        ∃ B ∈ J, InInternalMarkedTail S m x B ∧ y = m ‘ B) := by
  simp only [internalBranchAnchor, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

instance internalBranchAnchor_definable : ℒₛₑₜ-function₄[V] internalBranchAnchor := by
  have h : ℒₛₑₜ-relation₅[V] (fun A D S J m ↦ ∀ a,
      a ∈ A ↔ a ∈ D ×ˢ D ∧
        ((kpair.π₁ a ∈ internalBranchCore D S J m ∧ kpair.π₂ a = kpair.π₁ a) ∨
          ∃ B ∈ J, InInternalMarkedTail S m (kpair.π₁ a) B ∧ kpair.π₂ a = m ‘ B)) := by
    unfold internalBranchCore InInternalMarkedTail
    simp only [mem_sep_iff]
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [internalBranchAnchor, mem_sep_iff]
  rfl

namespace InternalSeparatedMarkerData

variable {D S κ rank J m : V} (h : InternalSeparatedMarkerData D S κ rank J m)

include h

theorem anchor_function :
    internalBranchAnchor D S J m ∈ internalBranchCore D S J m ^ D := by
  classical
  apply mem_function.intro
  · intro a ha
    have haD : a ∈ D ×ˢ D := (mem_sep_iff.mp ha).1
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp haD
    refine kpair_mem_iff.mpr ⟨hx, ?_⟩
    rcases ((pair_mem_internalBranchAnchor _ _ _ _ _ _).mp ha).2.2 with hc | ⟨B, hB, _, he⟩
    · exact hc.2.symm ▸ hc.1
    · rw [he]
      exact h.marker_in_core hB
  · intro x hx
    have uniq : ∀ y z, ⟨x, y⟩ₖ ∈ internalBranchAnchor D S J m →
        ⟨x, z⟩ₖ ∈ internalBranchAnchor D S J m → y = z := by
      intro y z hy hz
      rcases ((pair_mem_internalBranchAnchor _ _ _ _ _ _).mp hy).2.2 with ⟨hc, rfl⟩ | ⟨B, hB, hxB, rfl⟩
      · rcases ((pair_mem_internalBranchAnchor _ _ _ _ _ _).mp hz).2.2 with ⟨_, rfl⟩ | ⟨C, hC, hxC, _⟩
        · rfl
        · exact False.elim (tail_not_core hC hxC hc)
      · rcases ((pair_mem_internalBranchAnchor _ _ _ _ _ _).mp hz).2.2 with ⟨hc, _⟩ | ⟨C, hC, hxC, rfl⟩
        · exact False.elim (tail_not_core hB hxB hc)
        · rw [h.tail_unique hB hC hxB hxC]
    by_cases hc : x ∈ internalBranchCore D S J m
    · have hp := (pair_mem_internalBranchAnchor _ _ _ _ _ _).mpr ⟨hx, hx, Or.inl ⟨hc, rfl⟩⟩
      exact ⟨x, hp, fun z hz ↦ uniq z x hz hp⟩
    · obtain ⟨B, hB, hxB⟩ := exists_tail_of_not_core hx hc
      have hp := (pair_mem_internalBranchAnchor _ _ _ _ _ _).mpr
        ⟨hx, h.marker_in_domain hB, Or.inr ⟨B, hB, hxB, rfl⟩⟩
      exact ⟨m ‘ B, hp, fun z hz ↦ uniq z _ hz hp⟩

theorem anchor_of_core {x : V} (hx : x ∈ internalBranchCore D S J m) :
    (internalBranchAnchor D S J m) ‘ x = x := by
  let := IsFunction.of_mem h.anchor_function
  have hxD := ((mem_internalBranchCore _ _ _ _ _).mp hx).1
  exact value_eq_of_kpair_mem ((pair_mem_internalBranchAnchor _ _ _ _ _ _).mpr
    ⟨hxD, hxD, Or.inl ⟨hx, rfl⟩⟩)

theorem anchor_of_tail {x B : V} (hB : B ∈ J) (hx : InInternalMarkedTail S m x B) :
    (internalBranchAnchor D S J m) ‘ x = m ‘ B := by
  let := IsFunction.of_mem h.anchor_function
  exact value_eq_of_kpair_mem ((pair_mem_internalBranchAnchor _ _ _ _ _ _).mpr
    ⟨(h.branches B hB).1 x hx.1, h.marker_in_domain hB, Or.inr ⟨B, hB, hx, rfl⟩⟩)

theorem anchor_le {x : V} (hx : x ∈ D) : ⟨(internalBranchAnchor D S J m) ‘ x, x⟩ₖ ∈ S := by
  classical
  by_cases hc : x ∈ internalBranchCore D S J m
  · rw [h.anchor_of_core hc]
    exact h.order.1.2.1 x hx
  · obtain ⟨B, hB, hxB⟩ := exists_tail_of_not_core hx hc
    rw [h.anchor_of_tail hB hxB]
    exact h.marker_le_tail hB hxB

theorem anchor_le_marker {x B : V} (hB : B ∈ J) (hxB : x ∈ B) :
    ⟨(internalBranchAnchor D S J m) ‘ x, m ‘ B⟩ₖ ∈ S := by
  classical
  by_cases hc : x ∈ internalBranchCore D S J m
  · rw [h.anchor_of_core hc]
    exact ((mem_internalBranchCore _ _ _ _ _).mp hc).2 B hB hxB
  · obtain ⟨C, hC, hxC⟩ := exists_tail_of_not_core ((h.branches B hB).1 x hxB) hc
    rw [h.anchor_of_tail hC hxC]
    have hmCB := (h.branches B hB).2.2.2 _ (h.marker_in_domain hC) x hxB (h.marker_le_tail hC hxC)
    rcases (h.branches B hB).2.1 _ hmCB _ (h.marker_mem B hB) with hle | hle
    · exact hle
    · by_cases he : B = C
      · subst C
        exact h.order.1.2.1 _ (h.marker_in_domain hB)
      · exact False.elim (h.separates B hB C hC he hle hmCB)

theorem anchor_monotone {x y : V} (hx : x ∈ D) (hy : y ∈ D) (hxy : ⟨x, y⟩ₖ ∈ S) :
    ⟨(internalBranchAnchor D S J m) ‘ x, (internalBranchAnchor D S J m) ‘ y⟩ₖ ∈ S := by
  classical
  by_cases hc : y ∈ internalBranchCore D S J m
  · rw [h.anchor_of_core hc]
    exact h.order.1.2.2 _
      ((mem_internalBranchCore _ _ _ _ _).mp (function_value_mem h.anchor_function hx)).1
      x hx y hy (h.anchor_le hx) hxy
  · obtain ⟨B, hB, hyB⟩ := exists_tail_of_not_core hy hc
    rw [h.anchor_of_tail hB hyB]
    exact h.anchor_le_marker hB ((h.branches B hB).2.2.2 x hx y hyB.1 hxy)

theorem anchor_fibers_chain {x y : V} (hx : x ∈ D) (hy : y ∈ D)
    (he : (internalBranchAnchor D S J m) ‘ x = (internalBranchAnchor D S J m) ‘ y) :
    ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S := by
  classical
  by_cases hxc : x ∈ internalBranchCore D S J m
  · have hxy := h.anchor_le hy
    rw [← he, h.anchor_of_core hxc] at hxy
    exact Or.inl hxy
  by_cases hyc : y ∈ internalBranchCore D S J m
  · have hyx := h.anchor_le hx
    rw [he, h.anchor_of_core hyc] at hyx
    exact Or.inr hyx
  obtain ⟨B, hB, hxB⟩ := exists_tail_of_not_core hx hxc
  obtain ⟨C, hC, hyC⟩ := exists_tail_of_not_core hy hyc
  rw [h.anchor_of_tail hB hxB, h.anchor_of_tail hC hyC] at he
  have hBC := h.marker_injective hB hC he
  subst C
  exact (h.branches B hB).2.1 x hxB.1 y hyC.1

end InternalSeparatedMarkerData

/-- The downward closure is itself an internal separation set. -/
noncomputable def internalChainDownclosure (D S C : V) : V :=
  {x ∈ D ; ∃ y ∈ C, ⟨x, y⟩ₖ ∈ S}

theorem mem_internalChainDownclosure (D S C x : V) :
    x ∈ internalChainDownclosure D S C ↔ x ∈ D ∧ ∃ y ∈ C, ⟨x, y⟩ₖ ∈ S := by
  simp only [internalChainDownclosure, mem_sep_iff]

theorem internalChainDownclosure_is_cofinalBranch {D S κ rank C : V}
    (horder : IsForcingPoset D S) (htree : InternalRankedTree D S κ rank)
    (hC : C ⊆ D) (hchain : ∀ x ∈ C, ∀ y ∈ C, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S)
    (hcof : ∀ i ∈ κ, ∃ x ∈ C, i ⊆ (rank ‘ x)) :
    IsInternalCofinalBranch D S κ rank (internalChainDownclosure D S C) := by
  refine ⟨fun x hx ↦ ((mem_internalChainDownclosure _ _ _ _).mp hx).1, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨hxD, a, ha, hxa⟩ := (mem_internalChainDownclosure _ _ _ _).mp hx
    obtain ⟨hyD, b, hb, hyb⟩ := (mem_internalChainDownclosure _ _ _ _).mp hy
    rcases hchain a ha b hb with hab | hba
    · exact htree.below_linear x hxD y hyD b (hC b hb)
        (horder.1.2.2 x hxD a (hC a ha) b (hC b hb) hxa hab) hyb
    · exact htree.below_linear x hxD y hyD a (hC a ha) hxa
        (horder.1.2.2 y hyD b (hC b hb) a (hC a ha) hyb hba)
  · intro i hi
    obtain ⟨x, hx, hix⟩ := hcof i hi
    exact ⟨x, (mem_internalChainDownclosure _ _ _ _).mpr
      ⟨hC x hx, x, hx, horder.1.2.1 x (hC x hx)⟩, hix⟩
  · intro x hx y hy hxy
    obtain ⟨hyD, z, hz, hyz⟩ := (mem_internalChainDownclosure _ _ _ _).mp hy
    exact (mem_internalChainDownclosure _ _ _ _).mpr
      ⟨hx, z, hz, horder.1.2.2 x hx y hyD z (hC z hz) hxy hyz⟩

namespace InternalSeparatedMarkerData

variable {D S rank J m : V}
  (h : InternalSeparatedMarkerData D S (hartogsNumber (ω : V)) rank J m)

include h

/-- Exhaustiveness rules out a core chain with cofinal ranks: its downward
closure would contain its own marker, which bounds the whole chain. -/
theorem core_chain_ranks_bounded
    (hall : ∀ B : V, IsInternalCofinalBranch D S (hartogsNumber (ω : V)) rank B → B ∈ J)
    {C : V} (hC : C ⊆ internalBranchCore D S J m)
    (hchain : ∀ x ∈ C, ∀ y ∈ C, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) :
    ∃ i ∈ hartogsNumber (ω : V), ∀ x ∈ C, rank ‘ x ∈ i := by
  classical
  have hCD : C ⊆ D := fun x hx ↦ ((mem_internalBranchCore _ _ _ _ _).mp (hC x hx)).1
  have hncof : ¬∀ i ∈ hartogsNumber (ω : V), ∃ x ∈ C, i ⊆ (rank ‘ x) := by
    intro hcof
    let B := internalChainDownclosure D S C
    have hBj : B ∈ J := hall B (internalChainDownclosure_is_cofinalBranch h.order h.tree hCD hchain hcof)
    have hmD := h.marker_in_domain hBj
    have hmκ := function_value_mem h.tree.rank_function hmD
    obtain ⟨x, hx, hlarge⟩ := hcof (succ (rank ‘ (m ‘ B)))
      (hartogsNumber_succ_mem (CardLE.refl _) hmκ)
    have hxB : x ∈ B := (mem_internalChainDownclosure _ _ _ _).mpr
      ⟨hCD x hx, x, hx, h.order.1.2.1 x (hCD x hx)⟩
    have hxm := ((mem_internalBranchCore _ _ _ _ _).mp (hC x hx)).2 B hBj hxB
    have hbound := h.tree.rank_monotone x (hCD x hx) _ hmD hxm
    exact mem_irrefl _ (hbound _ (hlarge _ (mem_succ_self _)))
  push Not at hncof
  obtain ⟨i, hi, hib⟩ := hncof
  refine ⟨i, hi, fun x hx ↦ ?_⟩
  have : IsOrdinal i := IsOrdinal.of_mem hi
  have : IsOrdinal (rank ‘ x) := IsOrdinal.of_mem (function_value_mem h.tree.rank_function (hCD x hx))
  rcases IsOrdinal.mem_trichotomy (rank ‘ x) i with hxi | he | hix
  · exact hxi
  · exact False.elim (hib x hx (he.symm ▸ SetTheory.subset_refl i))
  · exact False.elim (hib x hx (IsOrdinal.toIsTransitive.transitive i hix))

/-- This is an internal injection into an ordinal below internal omega-one.
It applies even when that ordinal is externally uncountable or ill-founded. -/
theorem core_chains_countable
    (hrankinj : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ S → rank ‘ x = rank ‘ y → x = y)
    (hall : ∀ B : V, IsInternalCofinalBranch D S (hartogsNumber (ω : V)) rank B → B ∈ J)
    (C : V) (hC : C ⊆ internalBranchCore D S J m)
    (hchain : ∀ x ∈ C, ∀ y ∈ C, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) :
    IsInternallyCountable C := by
  obtain ⟨i, hi, hbound⟩ := h.core_chain_ranks_bounded hall hC hchain
  apply internallyCountable_of_cardLE (countable_of_mem_hartogs_omega hi)
  apply cardLE_of_injective_map (fun x ↦ rank ‘ x) (by definability) hbound
  intro x hx y hy he
  have hxD := ((mem_internalBranchCore _ _ _ _ _).mp (hC x hx)).1
  have hyD := ((mem_internalBranchCore _ _ _ _ _).mp (hC y hy)).1
  rcases hchain x hx y hy with hxy | hyx
  · exact hrankinj x hxD y hyD hxy he
  · exact (hrankinj y hyD x hxD hyx he.symm).symm

end InternalSeparatedMarkerData

/-- Equal-colored nodes above one node must be comparable. -/
def InternallyWeakSpecialization (D S f : V) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
    ⟨x, y⟩ₖ ∈ S → ⟨x, z⟩ₖ ∈ S → f ‘ x = f ‘ y → f ‘ x = f ‘ z →
      ⟨y, z⟩ₖ ∈ S ∨ ⟨z, y⟩ₖ ∈ S

instance internallyWeakSpecialization_definable : ℒₛₑₜ-relation₃[V] InternallyWeakSpecialization := by
  unfold InternallyWeakSpecialization
  definability

/-- The color-extension argument only needs an internal monotone anchor with
chain fibers. The core and marker construction can remain in the ground model. -/
theorem compose_strict_of_chain_fibers {D A S a f : V}
    (ha : a ∈ A ^ D)
    (hmono : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ S → ⟨a ‘ x, a ‘ y⟩ₖ ∈ S)
    (hfib : ∀ x ∈ D, ∀ y ∈ D, a ‘ x = a ‘ y → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S)
    (hf : f ∈ (ω : V) ^ A) (hstrict : InternallyStrict S f) :
    compose a f ∈ (ω : V) ^ D ∧ InternallyWeakSpecialization D S (compose a f) := by
  let := IsFunction.of_mem hf
  have heq : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ S →
      (compose a f) ‘ x = (compose a f) ‘ y → a ‘ x = a ‘ y := by
    intro x hx y hy hxy he
    rw [value_compose_of_mem_function ha hf hx, value_compose_of_mem_function ha hf hy] at he
    have hax := function_value_mem ha hx
    have hay := function_value_mem ha hy
    have hpx : ⟨a ‘ x, f ‘ (a ‘ x)⟩ₖ ∈ f :=
      kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hax)
    have hpy : ⟨a ‘ y, f ‘ (a ‘ x)⟩ₖ ∈ f := by
      rw [he]
      exact kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hay)
    exact hstrict _ _ _ hpx hpy (hmono x hx y hy hxy)
  refine ⟨compose_function ha hf, ?_⟩
  intro x hx y hy z hz hxy hxz hxyc hxzc
  exact hfib y hy z hz ((heq x hx y hy hxy hxyc).symm.trans (heq x hx z hz hxz hxzc))

namespace InternalSeparatedMarkerData

variable {D S κ rank J m : V} (h : InternalSeparatedMarkerData D S κ rank J m)

include h

theorem core_reflexive : ∀ x ∈ internalBranchCore D S J m, ⟨x, x⟩ₖ ∈ S :=
  fun x hx ↦ h.order.1.2.1 x ((mem_internalBranchCore _ _ _ _ _).mp hx).1

theorem core_below_linear : ∀ x ∈ internalBranchCore D S J m,
    ∀ y ∈ internalBranchCore D S J m, ∀ z ∈ internalBranchCore D S J m,
      ⟨x, z⟩ₖ ∈ S → ⟨y, z⟩ₖ ∈ S → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S :=
  fun x hx y hy z hz ↦ h.tree.below_linear
    x ((mem_internalBranchCore _ _ _ _ _).mp hx).1
    y ((mem_internalBranchCore _ _ _ _ _).mp hy).1
    z ((mem_internalBranchCore _ _ _ _ _).mp hz).1

/-- Composition is an actual internal function on the entire original tree. -/
theorem extend_strict_coloring {f : V}
    (hf : f ∈ (ω : V) ^ internalBranchCore D S J m) (hstrict : InternallyStrict S f) :
    compose (internalBranchAnchor D S J m) f ∈ (ω : V) ^ D ∧
      InternallyWeakSpecialization D S (compose (internalBranchAnchor D S J m) f) ∧
      ∀ x ∈ internalBranchCore D S J m,
        (compose (internalBranchAnchor D S J m) f) ‘ x = f ‘ x := by
  let a := internalBranchAnchor D S J m
  have ha : a ∈ internalBranchCore D S J m ^ D := h.anchor_function
  obtain ⟨hg, hweak⟩ := compose_strict_of_chain_fibers ha
    (fun _ hx _ hy ↦ h.anchor_monotone hx hy)
    (fun _ hx _ hy ↦ h.anchor_fibers_chain hx hy) hf hstrict
  refine ⟨hg, hweak, ?_⟩
  intro x hx
  rw [value_compose_of_mem_function ha hf ((mem_internalBranchCore _ _ _ _ _).mp hx).1]
  rw [show a ‘ x = x from h.anchor_of_core hx]

end InternalSeparatedMarkerData

end ZFVP.Schmerl
