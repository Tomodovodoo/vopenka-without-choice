import ZFVP.ModelTheory.LevyCollapseSubgeneric

/-! The upper part of a Levy collapse condition (columns `≥ β`), the sub-poset of conditions
supported above `β`, and gluing lower and upper parts: `Coll(ω,<κ) ≅ Coll(ω,<β) × Coll(ω,[β,κ))`
at the level of conditions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The part of a condition on the columns `≥ β`. -/
noncomputable def levyUpper (β p : V) : V := p \ levyCut β p

theorem levyUpper_subset (β p : V) : levyUpper β p ⊆ p := fun _ h ↦ (mem_sdiff_iff.mp h).1

theorem mem_levyUpper_iff (β p z : V) : z ∈ levyUpper β p ↔ z ∈ p ∧ z ∉ levyCut β p := mem_sdiff_iff

theorem kpair_mem_levyUpper_iff (β p x y : V) :
    ⟨x, y⟩ₖ ∈ levyUpper β p ↔ ⟨x, y⟩ₖ ∈ p ∧ x ∉ (ω : V) ×ˢ β := by
  rw [mem_levyUpper_iff, kpair_mem_levyCut_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hx ↦ h2 ⟨h1, hx⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h ↦ h2 h.2⟩

theorem levyCut_union_levyUpper (β p : V) : levyCut β p ∪ levyUpper β p = p := by
  ext z
  rw [mem_union_iff, mem_levyUpper_iff]
  constructor
  · rintro (h | h)
    · exact levyCut_subset β p z h
    · exact h.1
  · intro hz
    by_cases h : z ∈ levyCut β p
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩

theorem levyCut_levyUpper (β p : V) : levyCut β (levyUpper β p) = ∅ := by
  ext z
  simp only [not_mem_empty, iff_false]
  intro hz
  obtain ⟨hzu, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
  exact ((kpair_mem_levyUpper_iff β p x y).mp hzu).2 hx

theorem levyUpper_mono {β p q : V} (h : p ⊆ q) : levyUpper β p ⊆ levyUpper β q := by
  intro z hz
  obtain ⟨hzp, hzc⟩ := (mem_levyUpper_iff β p z).mp hz
  refine (mem_levyUpper_iff β q z).mpr ⟨h z hzp, fun hc ↦ hzc ?_⟩
  obtain ⟨_, x, hx, y, rfl⟩ := mem_restrict_iff.mp hc
  exact (kpair_mem_levyCut_iff β p x y).mpr ⟨hzp, hx⟩

/-- Conditions supported on the columns `≥ β`. -/
noncomputable def levyCollapseAbove (κ β : V) : V := {p ∈ levyCollapse κ ; levyCut β p = ∅}

theorem mem_levyCollapseAbove_iff (κ β p : V) :
    p ∈ levyCollapseAbove κ β ↔ p ∈ levyCollapse κ ∧ levyCut β p = ∅ := mem_sep_iff

theorem levyCollapseAbove_subset (κ β : V) : levyCollapseAbove κ β ⊆ levyCollapse κ := sep_subset

theorem empty_mem_levyCollapseAbove (κ β : V) : (∅ : V) ∈ levyCollapseAbove κ β :=
  (mem_levyCollapseAbove_iff _ _ _).mpr ⟨empty_mem_levyCollapse κ, by
    ext z
    simp only [not_mem_empty, iff_false]
    intro hz
    exact not_mem_empty (levyCut_subset β ∅ z hz)⟩

theorem levyUpper_mem_above {κ β p : V} (hp : p ∈ levyCollapse κ) :
    levyUpper β p ∈ levyCollapseAbove κ β :=
  (mem_levyCollapseAbove_iff _ _ _).mpr
    ⟨levyCollapse_subset hp (levyUpper_subset β p), levyCut_levyUpper β p⟩

theorem levyUpper_of_above {κ β p : V} (hp : p ∈ levyCollapseAbove κ β) : levyUpper β p = p := by
  have h := ((mem_levyCollapseAbove_iff _ _ _).mp hp).2
  unfold levyUpper
  rw [h]
  ext z
  rw [mem_sdiff_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, not_mem_empty⟩⟩

theorem levyUpper_of_mem_collapse {β q : V} (hq : q ∈ levyCollapse β) : levyUpper β q = ∅ := by
  unfold levyUpper
  rw [levyCut_eq_self hq]
  ext z
  rw [mem_sdiff_iff]
  exact ⟨fun h ↦ absurd h.1 h.2, fun h ↦ absurd h not_mem_empty⟩

/-- An element of a condition supported above `β` has its coordinate outside `ω × β`. -/
theorem coordinate_not_mem_of_above {κ β u x y : V} (hu : u ∈ levyCollapseAbove κ β)
    (h : ⟨x, y⟩ₖ ∈ u) : x ∉ (ω : V) ×ˢ β := by
  intro hx
  have hcut := ((mem_levyCollapseAbove_iff _ _ _).mp hu).2
  have : ⟨x, y⟩ₖ ∈ levyCut β u := (kpair_mem_levyCut_iff β u x y).mpr ⟨h, hx⟩
  rw [hcut] at this
  exact not_mem_empty this

/-- An element of a condition of the subcollapse has its coordinate in `ω × β`. -/
theorem coordinate_mem_of_collapse {β q x y : V} (hq : q ∈ levyCollapse β) (h : ⟨x, y⟩ₖ ∈ q) :
    x ∈ (ω : V) ×ˢ β := by
  have := (kpair_mem_levyCut_iff β q x y).mp (by rw [levyCut_eq_self hq]; exact h)
  exact this.2

/-- Gluing a lower part and an upper part. -/
theorem levyCollapse_union_above {κ β q u : V} (hβ : β ⊆ κ) (hq : q ∈ levyCollapse β)
    (hu : u ∈ levyCollapseAbove κ β) : q ∪ u ∈ levyCollapse κ := by
  refine levyCollapse_union (levyCollapse_mono hβ _ hq) (levyCollapseAbove_subset κ β u hu) ?_
  intro x y z hxy hxz
  exact absurd (coordinate_mem_of_collapse hq hxy) (coordinate_not_mem_of_above hu hxz)

theorem levyCut_union_above {κ β q u : V} (hq : q ∈ levyCollapse β) (hu : u ∈ levyCollapseAbove κ β) :
    levyCut β (q ∪ u) = q := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzu, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
    rcases mem_union_iff.mp hzu with h | h
    · exact h
    · exact absurd hx (coordinate_not_mem_of_above hu h)
  · intro hz
    have hz' : z ∈ levyCut β q := by rw [levyCut_eq_self hq]; exact hz
    exact levyCut_mono (fun w hw ↦ mem_union_iff.mpr (Or.inl hw)) z hz'

theorem levyUpper_union_above {κ β q u : V} (hq : q ∈ levyCollapse β) (hu : u ∈ levyCollapseAbove κ β) :
    levyUpper β (q ∪ u) = u := by
  unfold levyUpper
  rw [levyCut_union_above hq hu]
  ext z
  rw [mem_sdiff_iff, mem_union_iff]
  constructor
  · rintro ⟨h | h, hzq⟩
    · exact absurd h hzq
    · exact h
  · intro hz
    refine ⟨Or.inr hz, fun hzq ↦ ?_⟩
    have hz' := ((mem_levyCollapseAbove_iff _ _ _).mp hu).1
    obtain ⟨hfp, _⟩ := (mem_levyCollapse_iff _ _).mp hz'
    obtain ⟨hsub, _, _⟩ := (mem_finitePartialFunctions _ _ _).mp hfp
    obtain ⟨x, _, y, _, rfl⟩ := mem_prod_iff.mp (hsub z hz)
    exact coordinate_not_mem_of_above hu hz (coordinate_mem_of_collapse hq hzq)

/-- A condition above `β` contained in `r` is contained in the upper part of `r`. -/
theorem above_subset_levyUpper {κ β p r : V} (hp : p ∈ levyCollapseAbove κ β) (h : p ⊆ r) :
    p ⊆ levyUpper β r := by
  intro z hz
  have hp' := ((mem_levyCollapseAbove_iff _ _ _).mp hp).1
  obtain ⟨hfp, _⟩ := (mem_levyCollapse_iff _ _).mp hp'
  obtain ⟨hsub, _, _⟩ := (mem_finitePartialFunctions _ _ _).mp hfp
  obtain ⟨x, _, y, _, rfl⟩ := mem_prod_iff.mp (hsub z hz)
  exact (kpair_mem_levyUpper_iff β r x y).mpr ⟨h _ hz, coordinate_not_mem_of_above hp hz⟩

/-- The lower part of a condition in the generic lies in the generic. -/
theorem levyCut_mem_of_mem {κ β : V} {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
    {p : V} (hp : p ∈ G) : levyCut β p ∈ G :=
  hG.1.2.2.1 p hp _ (levyCollapse_subset (hG.1.1 p hp) (levyCut_subset β p)) (levyCut_le (hG.1.1 p hp))

theorem levyUpper_mem_of_mem {κ β : V} {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
    {p : V} (hp : p ∈ G) : levyUpper β p ∈ G :=
  hG.1.2.2.1 p hp _ (levyCollapse_subset (hG.1.1 p hp) (levyUpper_subset β p))
    ((pair_mem_reverseInclusionOrder _ _ _).mpr
      ⟨hG.1.1 p hp, levyCollapse_subset (hG.1.1 p hp) (levyUpper_subset β p), levyUpper_subset β p⟩)

end ZFVP
