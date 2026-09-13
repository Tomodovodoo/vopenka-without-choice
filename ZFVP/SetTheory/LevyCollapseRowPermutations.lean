import ZFVP.SetTheory.LevyCollapseSupport
import ZFVP.SetTheory.PartialFunctionAutomorphisms
import ZFVP.SetTheory.InternalTranspositions
import ZFVP.SetTheory.FiniteNaturalSets
import ZFVP.SetTheory.FunctionComposition

/-! Row permutations of the Levy collapse: a permutation `σ` of `ω` acts on `ω × κ` by
`(n, α) ↦ (σ n, α)` in the columns `α ∉ β` and trivially in the columns below `β`. This gives
forcing automorphisms of `Coll(ω, <κ)` fixing `Coll(ω, <β)` pointwise, and any condition can be
moved off the rows used above `β` by another condition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A map on `ω × κ` preserving the column coordinate. -/
def PreservesColumns (κ π : V) : Prop :=
  ∀ z ∈ (ω : V) ×ˢ κ, kpair.π₂ (π ‘ z) = kpair.π₂ z

theorem PreservesColumns.inv {κ π : V} (hπ : IsInternalPermutation ((ω : V) ×ˢ κ) π)
    (h : PreservesColumns κ π) : PreservesColumns κ (converseGraph π) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hπ.surjective hz
  rw [hπ.inv_value hx, h x hx]

/-- Column-preserving permutations act on the Levy collapse. -/
theorem permutedGraph_levy_mem {κ π p : V} (hπ : IsInternalPermutation ((ω : V) ×ˢ κ) π)
    (hcol : PreservesColumns κ π) (hp : p ∈ levyCollapse κ) :
    permutedGraph π p ∈ levyCollapse κ := by
  have hpf := levyCollapse_finitePartialFunction hp
  have hpfun : IsFunction p := ((mem_finitePartialFunctions _ _ p).mp hpf).2.1
  refine (mem_levyCollapse_iff κ _).mpr ⟨permutedGraph_condition hπ hpf, ?_⟩
  intro m α γ h
  obtain ⟨u, hu, he⟩ := (pair_mem_permutedGraph _ p _ γ).mp h
  have hsub := ((mem_finitePartialFunctions _ _ p).mp hpf).1
  have hu' := (kpair_mem_iff.mp (hsub _ hu)).1
  obtain ⟨n, hn, α', hα', rfl⟩ := mem_prod_iff.mp hu'
  have hγ : γ ∈ α' := levyCollapse_value hp hu
  have hc := hcol _ hu'
  rw [← he] at hc
  simp only [kpair.π₂_kpair] at hc
  rw [hc]
  exact hγ

/-- The graph of the row map on `ω × κ`. -/
noncomputable def levyRowPermutation (κ β σ : V) : V :=
  {w ∈ ((ω : V) ×ˢ κ) ×ˢ ((ω : V) ×ˢ κ) ;
    (kpair.π₂ (kpair.π₁ w) ∈ β ∧ kpair.π₂ w = kpair.π₁ w) ∨
    (kpair.π₂ (kpair.π₁ w) ∉ β ∧
      kpair.π₂ w = ⟨σ ‘ (kpair.π₁ (kpair.π₁ w)), kpair.π₂ (kpair.π₁ w)⟩ₖ)}

instance levyRowPermutation_definable : ℒₛₑₜ-function₃[V] levyRowPermutation := by
  have hd : ℒₛₑₜ-relation₄[V] (fun π κ β σ ↦ ∀ w, w ∈ π ↔
    w ∈ ((ω : V) ×ˢ κ) ×ˢ ((ω : V) ×ˢ κ) ∧
    ((kpair.π₂ (kpair.π₁ w) ∈ β ∧ kpair.π₂ w = kpair.π₁ w) ∨
    (kpair.π₂ (kpair.π₁ w) ∉ β ∧
      kpair.π₂ w = ⟨σ ‘ (kpair.π₁ (kpair.π₁ w)), kpair.π₂ (kpair.π₁ w)⟩ₖ))) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = levyRowPermutation (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h w ↦ (h w).trans (show w ∈ levyRowPermutation (v 1) (v 2) (v 3) ↔ _ from mem_sep_iff),
    fun h w ↦ (h w).trans (show w ∈ levyRowPermutation (v 1) (v 2) (v 3) ↔ _ from mem_sep_iff).symm⟩

theorem kpair_mem_levyRowPermutation_iff (κ β σ n α z : V) :
    ⟨⟨n, α⟩ₖ, z⟩ₖ ∈ levyRowPermutation κ β σ ↔
      n ∈ (ω : V) ∧ α ∈ κ ∧ z ∈ (ω : V) ×ˢ κ ∧
      ((α ∈ β ∧ z = ⟨n, α⟩ₖ) ∨ (α ∉ β ∧ z = ⟨σ ‘ n, α⟩ₖ)) := by
  unfold levyRowPermutation
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

variable {κ β σ : V}

theorem levyRowPermutation_function (hσ : IsInternalPermutation (ω : V) σ) :
    levyRowPermutation κ β σ ∈ ((ω : V) ×ˢ κ) ^ ((ω : V) ×ˢ κ) := by
  apply mem_function.intro
  · intro w hw
    exact (mem_sep_iff.mp hw).1
  · intro x hx
    obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hx
    by_cases hαβ : α ∈ β
    · refine ⟨⟨n, α⟩ₖ, (kpair_mem_levyRowPermutation_iff κ β σ n α _).mpr
        ⟨hn, hα, hx, Or.inl ⟨hαβ, rfl⟩⟩, ?_⟩
      intro z hz
      obtain ⟨_, _, _, h | h⟩ := (kpair_mem_levyRowPermutation_iff κ β σ n α z).mp hz
      · exact h.2
      · exact (h.1 hαβ).elim
    · have hσn : σ ‘ n ∈ (ω : V) := function_value_mem hσ.1 hn
      refine ⟨⟨σ ‘ n, α⟩ₖ, (kpair_mem_levyRowPermutation_iff κ β σ n α _).mpr
        ⟨hn, hα, kpair_mem_iff.mpr ⟨hσn, hα⟩, Or.inr ⟨hαβ, rfl⟩⟩, ?_⟩
      intro z hz
      obtain ⟨_, _, _, h | h⟩ := (kpair_mem_levyRowPermutation_iff κ β σ n α z).mp hz
      · exact (hαβ h.1).elim
      · exact h.2

theorem levyRowPermutation_value_below (hσ : IsInternalPermutation (ω : V) σ) {n α : V}
    (hn : n ∈ (ω : V)) (hα : α ∈ κ) (hαβ : α ∈ β) :
    (levyRowPermutation κ β σ) ‘ ⟨n, α⟩ₖ = ⟨n, α⟩ₖ := by
  have := IsFunction.of_mem (levyRowPermutation_function (κ := κ) (β := β) hσ)
  exact value_eq_of_kpair_mem ((kpair_mem_levyRowPermutation_iff κ β σ n α _).mpr
    ⟨hn, hα, kpair_mem_iff.mpr ⟨hn, hα⟩, Or.inl ⟨hαβ, rfl⟩⟩)

theorem levyRowPermutation_value_above (hσ : IsInternalPermutation (ω : V) σ) {n α : V}
    (hn : n ∈ (ω : V)) (hα : α ∈ κ) (hαβ : α ∉ β) :
    (levyRowPermutation κ β σ) ‘ ⟨n, α⟩ₖ = ⟨σ ‘ n, α⟩ₖ := by
  have := IsFunction.of_mem (levyRowPermutation_function (κ := κ) (β := β) hσ)
  exact value_eq_of_kpair_mem ((kpair_mem_levyRowPermutation_iff κ β σ n α _).mpr
    ⟨hn, hα, kpair_mem_iff.mpr ⟨function_value_mem hσ.1 hn, hα⟩, Or.inr ⟨hαβ, rfl⟩⟩)

theorem levyRowPermutation_preservesColumns (hσ : IsInternalPermutation (ω : V) σ) :
    PreservesColumns κ (levyRowPermutation κ β σ) := by
  intro z hz
  obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hz
  by_cases hαβ : α ∈ β
  · rw [levyRowPermutation_value_below hσ hn hα hαβ]
  · rw [levyRowPermutation_value_above hσ hn hα hαβ]
    simp only [kpair.π₂_kpair]

theorem levyRowPermutation_permutation (hσ : IsInternalPermutation (ω : V) σ) :
    IsInternalPermutation ((ω : V) ×ˢ κ) (levyRowPermutation κ β σ) := by
  have hf := levyRowPermutation_function (κ := κ) (β := β) hσ
  have := IsFunction.of_mem hf
  have : IsFunction σ := IsFunction.of_mem hσ.1
  have hdσ : domain σ = (ω : V) := domain_eq_of_mem_function hσ.1
  refine ⟨hf, ?_, ?_⟩
  · intro x y z hx hy
    obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp (mem_of_mem_functions hf hx).1
    obtain ⟨m, hm, α', hα', rfl⟩ := mem_prod_iff.mp (mem_of_mem_functions hf hy).1
    have hx' := value_eq_of_kpair_mem hx
    have hy' := value_eq_of_kpair_mem hy
    by_cases hαβ : α ∈ β
    · rw [levyRowPermutation_value_below hσ hn hα hαβ] at hx'
      by_cases hα'β : α' ∈ β
      · rw [levyRowPermutation_value_below hσ hm hα' hα'β] at hy'
        exact hx'.trans hy'.symm
      · rw [levyRowPermutation_value_above hσ hm hα' hα'β] at hy'
        obtain ⟨_, rfl⟩ := kpair_iff.mp (hx'.trans hy'.symm)
        exact (hα'β hαβ).elim
    · rw [levyRowPermutation_value_above hσ hn hα hαβ] at hx'
      by_cases hα'β : α' ∈ β
      · rw [levyRowPermutation_value_below hσ hm hα' hα'β] at hy'
        obtain ⟨_, rfl⟩ := kpair_iff.mp (hx'.trans hy'.symm)
        exact (hαβ hα'β).elim
      · rw [levyRowPermutation_value_above hσ hm hα' hα'β] at hy'
        obtain ⟨he, rfl⟩ := kpair_iff.mp (hx'.trans hy'.symm)
        have h1 : ⟨n, σ ‘ n⟩ₖ ∈ σ := kpair_value_mem (by rw [hdσ]; exact hn)
        have h2 : ⟨m, σ ‘ m⟩ₖ ∈ σ := kpair_value_mem (by rw [hdσ]; exact hm)
        rw [he] at h1
        rw [hσ.2.1 n m _ h1 h2]
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro y hy
    obtain ⟨m, hm, α, hα, rfl⟩ := mem_prod_iff.mp hy
    by_cases hαβ : α ∈ β
    · have := levyRowPermutation_value_below (κ := κ) hσ hm hα hαβ
      exact this ▸ value_mem_range hf (kpair_mem_iff.mpr ⟨hm, hα⟩)
    · obtain ⟨n, hn, hnm⟩ := hσ.surjective hm
      have := levyRowPermutation_value_above (κ := κ) hσ hn hα hαβ
      rw [hnm] at this
      exact this ▸ value_mem_range hf (kpair_mem_iff.mpr ⟨hn, hα⟩)

/-- The forcing automorphism of `Coll(ω, <κ)` induced by a row permutation. -/
noncomputable def levyPermutation (κ β σ : V) : V :=
  definableGraph (levyCollapse κ) (permutedGraph (levyRowPermutation κ β σ)) (by definability)

theorem levyPermutation_value {p : V} (hp : p ∈ levyCollapse κ) :
    (levyPermutation κ β σ) ‘ p = permutedGraph (levyRowPermutation κ β σ) p :=
  value_definableGraph _ _ _ hp

theorem levyPermutation_function (hσ : IsInternalPermutation (ω : V) σ) :
    levyPermutation κ β σ ∈ levyCollapse κ ^ levyCollapse κ :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hp ↦ permutedGraph_levy_mem
    (levyRowPermutation_permutation hσ) (levyRowPermutation_preservesColumns hσ) hp)

theorem levyPermutation_automorphism (hσ : IsInternalPermutation (ω : V) σ) :
    IsForcingAutomorphism (levyCollapse κ) (levyOrder κ) (levyPermutation κ β σ) := by
  have hπ := levyRowPermutation_permutation (κ := κ) (β := β) hσ
  have hcol := levyRowPermutation_preservesColumns (κ := κ) (β := β) hσ
  have hf := levyPermutation_function (κ := κ) (β := β) hσ
  have : IsFunction (levyPermutation κ β σ) := IsFunction.of_mem hf
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro p q z hp hq
    have hpP := (mem_of_mem_functions hf hp).1
    have hqP := (mem_of_mem_functions hf hq).1
    have he : permutedGraph (levyRowPermutation κ β σ) p =
        permutedGraph (levyRowPermutation κ β σ) q := by
      rw [← levyPermutation_value hpP, ← levyPermutation_value hqP]
      exact (value_eq_of_kpair_mem hp).trans (value_eq_of_kpair_mem hq).symm
    have hh := congrArg (permutedGraph (converseGraph (levyRowPermutation κ β σ))) he
    simpa only [permutedGraph_inverse hπ (levyCollapse_finitePartialFunction hpP),
      permutedGraph_inverse hπ (levyCollapse_finitePartialFunction hqP)] using hh
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro q hq
    have hi := permutedGraph_levy_mem hπ.inv (hcol.inv hπ) hq
    have hv : (levyPermutation κ β σ) ‘ (permutedGraph (converseGraph (levyRowPermutation κ β σ)) q) = q := by
      rw [levyPermutation_value hi, permutedGraph_inverse_right hπ (levyCollapse_finitePartialFunction hq)]
    exact hv ▸ value_mem_range hf hi
  · intro p hp q hq
    unfold levyOrder
    rw [pair_mem_reverseInclusionOrder, pair_mem_reverseInclusionOrder,
      levyPermutation_value hp, levyPermutation_value hq]
    have hp' := permutedGraph_levy_mem hπ hcol hp
    have hq' := permutedGraph_levy_mem hπ hcol hq
    simp only [hp, hq, hp', hq', true_and]
    constructor
    · exact permutedGraph_mono
    · intro h
      have hh := permutedGraph_mono (π := converseGraph (levyRowPermutation κ β σ)) h
      simpa only [permutedGraph_inverse hπ (levyCollapse_finitePartialFunction hp),
        permutedGraph_inverse hπ (levyCollapse_finitePartialFunction hq)] using hh

/-- Row permutations fix the subcollapse below `β` pointwise. -/
theorem levyPermutation_fixed (hσ : IsInternalPermutation (ω : V) σ) {p : V}
    (hp : p ∈ levyCollapse β) (hβ : β ⊆ κ) : (levyPermutation κ β σ) ‘ p = p := by
  have hpκ : p ∈ levyCollapse κ := levyCollapse_mono hβ _ hp
  rw [levyPermutation_value hpκ]
  have hsub := ((mem_finitePartialFunctions _ _ p).mp (levyCollapse_finitePartialFunction hp)).1
  ext z
  rw [mem_permutedGraph]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨x, hx, γ, _, rfl⟩ := mem_prod_iff.mp (hsub _ hu)
    obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hx
    unfold permutedGraphEntry
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    rw [levyRowPermutation_value_below hσ hn (hβ _ hα) hα]
    exact hu
  · intro hz
    refine ⟨z, hz, ?_⟩
    obtain ⟨x, hx, γ, _, rfl⟩ := mem_prod_iff.mp (hsub _ hz)
    obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hx
    unfold permutedGraphEntry
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    rw [levyRowPermutation_value_below hσ hn (hβ _ hα) hα]

/-- The rows used by a condition in the columns above `β`. -/
noncomputable def levyRows (β p : V) : V :=
  {n ∈ (ω : V) ; ∃ α γ, ⟨⟨n, α⟩ₖ, γ⟩ₖ ∈ p ∧ α ∉ β}

theorem levyRows_finite {p : V} (hp : p ∈ levyCollapse κ) : IsInternallyFinite (levyRows β p) := by
  apply internallyFinite_subset (internallyFinite_repl (fun z ↦ kpair.π₁ (kpair.π₁ z))
    (by definability) (levyCollapse_internallyFinite hp))
  intro n hn
  obtain ⟨_, α, γ, h, _⟩ := mem_sep_iff.mp hn
  exact (repl_spec _).mpr ⟨_, h, by simp⟩

theorem levyRows_subset (β p : V) : levyRows β p ⊆ (ω : V) := sep_subset

/-- Moving the rows of `p` above `β` off the rows of `q` makes the result compatible with `q`
whenever `q` extends the part of `p` below `β`. -/
theorem levyPermutation_compatible (hσ : IsInternalPermutation (ω : V) σ) {p q : V}
    (hp : p ∈ levyCollapse κ) (hq : q ∈ levyCollapse κ) (hcut : levyCut β p ⊆ q)
    (hmove : ∀ n ∈ levyRows β p, σ ‘ n ∉ levyRows β q) :
    ∀ x y z, ⟨x, y⟩ₖ ∈ permutedGraph (levyRowPermutation κ β σ) p → ⟨x, z⟩ₖ ∈ q → y = z := by
  intro x y z hxy hxz
  have hpfun : IsFunction p := ((mem_finitePartialFunctions _ _ p).mp (levyCollapse_finitePartialFunction hp)).2.1
  have hqfun : IsFunction q := ((mem_finitePartialFunctions _ _ q).mp (levyCollapse_finitePartialFunction hq)).2.1
  obtain ⟨u, hu, rfl⟩ := (pair_mem_permutedGraph _ p _ y).mp hxy
  have hsub := ((mem_finitePartialFunctions _ _ p).mp (levyCollapse_finitePartialFunction hp)).1
  obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp (kpair_mem_iff.mp (hsub _ hu)).1
  by_cases hαβ : α ∈ β
  · rw [levyRowPermutation_value_below hσ hn hα hαβ] at hxz
    have hcutmem : ⟨⟨n, α⟩ₖ, y⟩ₖ ∈ q := hcut _ ((kpair_mem_levyCut_iff' hp).mpr ⟨hu, hαβ⟩)
    exact IsFunction.unique (hf := hqfun) hcutmem hxz
  · rw [levyRowPermutation_value_above hσ hn hα hαβ] at hxz
    exfalso
    apply hmove n (mem_sep_iff.mpr ⟨hn, α, y, hu, hαβ⟩)
    exact mem_sep_iff.mpr ⟨function_value_mem hσ.1 hn, α, z, hxz, hαβ⟩

/-- A permutation of `ω` moving a finite set of naturals off another finite set. -/
theorem exists_permutation_moving {X Y : V} (hX : IsInternallyFinite X) (hXω : X ⊆ (ω : V))
    (hY : IsInternallyFinite Y) (hYω : Y ⊆ (ω : V)) :
    ∃ σ, IsInternalPermutation (ω : V) σ ∧ ∀ n ∈ X, σ ‘ n ∉ Y := by
  have key : ∀ X, IsInternallyFinite X → IsInternallyFinite X ∧ (X ⊆ (ω : V) →
      ∃ σ, IsInternalPermutation (ω : V) σ ∧ ∀ n ∈ X, σ ‘ n ∉ Y) := by
    apply internallyFinite_induction (fun X ↦ IsInternallyFinite X ∧ (X ⊆ (ω : V) →
      ∃ σ, IsInternalPermutation (ω : V) σ ∧ ∀ n ∈ X, σ ‘ n ∉ Y)) (by definability)
    · exact ⟨internallyFinite_empty, fun _ ↦ ⟨identity ω, internalPermutation_identity ω,
        fun n hn ↦ (not_mem_empty hn).elim⟩⟩
    · intro A a ⟨hAfin, ih⟩
      refine ⟨internallyFinite_insert hAfin a, fun hsub' ↦ ?_⟩
      have hAω : A ⊆ (ω : V) := fun z hz ↦ hsub' z (mem_insert.mpr (Or.inr hz))
      have haω : a ∈ (ω : V) := hsub' a (mem_insert.mpr (Or.inl rfl))
      obtain ⟨σ₀, hσ₀, hmove⟩ := ih hAω
      have : IsFunction σ₀ := IsFunction.of_mem hσ₀.1
      by_cases haA : a ∈ A
      · exact ⟨σ₀, hσ₀, fun n hn ↦ by
          rcases mem_insert.mp hn with rfl | hn
          · exact hmove _ haA
          · exact hmove n hn⟩
      -- a fresh row avoiding `Y` and the image of `insert a A`
      have himg : IsInternallyFinite (repl (fun n ↦ σ₀ ‘ n) (by definability) (insert a A)) :=
        internallyFinite_repl _ _ (internallyFinite_insert hAfin a)
      obtain ⟨m, hm, hmn⟩ := internallyFinite_fresh_natural
        (internallyFinite_union hY himg)
      have hmY : m ∉ Y := fun h ↦ hmn (mem_union_iff.mpr (Or.inl h))
      have hmimg : ∀ n ∈ insert a A, σ₀ ‘ n ≠ m := fun n hn h ↦
        hmn (mem_union_iff.mpr (Or.inr ((repl_spec _).mpr ⟨n, hn, h.symm⟩)))
      have hσ₀a : σ₀ ‘ a ∈ (ω : V) := function_value_mem hσ₀.1 haω
      let t := internalTransposition (ω : V) (σ₀ ‘ a) m
      have ht : IsInternalPermutation (ω : V) t := internalTransposition_permutation hσ₀a hm
      refine ⟨compose σ₀ t, hσ₀.comp ht, ?_⟩
      intro n hn
      rw [value_compose_of_mem_function hσ₀.1 ht.1 (hsub' n hn)]
      rcases mem_insert.mp hn with rfl | hnA
      · rw [internalTransposition_left hσ₀a]
        exact hmY
      · have hne : σ₀ ‘ n ≠ σ₀ ‘ a := by
          intro h
          have hdσ : domain σ₀ = (ω : V) := domain_eq_of_mem_function hσ₀.1
          have h1 : ⟨n, σ₀ ‘ n⟩ₖ ∈ σ₀ := kpair_value_mem (by rw [hdσ]; exact hAω _ hnA)
          have h2 : ⟨a, σ₀ ‘ a⟩ₖ ∈ σ₀ := kpair_value_mem (by rw [hdσ]; exact haω)
          rw [h] at h1
          exact haA ((hσ₀.2.1 n a _ h1 h2) ▸ hnA)
        rw [internalTransposition_fixed (function_value_mem hσ₀.1 (hAω _ hnA)) hne
          (hmimg n (mem_insert.mpr (Or.inr hnA)))]
        exact hmove n hnA
  exact (key X hX).2 hXω

end ZFVP
