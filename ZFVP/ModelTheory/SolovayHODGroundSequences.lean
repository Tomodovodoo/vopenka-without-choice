import ZFVP.ModelTheory.LevySequenceLocalization
import ZFVP.ModelTheory.LevyStageDefinable
import ZFVP.ModelTheory.ForcingHierarchyCover
import ZFVP.ModelTheory.RankPowersetExtension
import ZFVP.ModelTheory.ForcingRealizationGeneration
import ZFVP.ModelTheory.ForcingChoice
import ZFVP.ModelTheory.LevyODLocalized
import ZFVP.SetTheory.RegularUnions

/-! Countable sequences of the Levy extension that stay inside one bounded stage are definable
from ground sets, reals and ordinals.

Three steps, each useful on its own.

An `ω`-sequence of the extension whose values lie in a single checked set is localized
(`levy_sequence_localized`), hence definable from ground sets, reals and ordinals.

An `ω`-sequence all of whose values are ground sets also lands in a single checked set: the rank
of its range is an ordinal of the extension, so it is a check `ρ̌`, and each value `ǎ` then has
`rank a ∈ ρ`, that is `a ∈ V_ρ`.

An `ω`-sequence all of whose values lie in one bounded stage `V[G_ζ]`, `ζ < κ`, is definable as
well. Again the rank of the range is a check `ρ̌`, so all values lie in the `ρ̌`-th stage of
`V[G_ζ]`, and that stage is the range of the name evaluation function of `V[G_ζ]` on the checked
set of names of level `ρ`. Choice in the extension picks a name for each value, giving an
`ω`-sequence into a check; the sequence itself is read back from that sequence of names and the
evaluation function by one formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ### Reading a sequence off a sequence of indices and a lookup function -/

section

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `z` is the pair of `n` with the value of the lookup function at the `n`-th index, both read
off the pair parameter `x = ⟨E, g⟩ₖ`. -/
def compositeSequenceFormula : SetTheorySemisentence 2 :=
  f“z x. ∃ n ∈ !isω, z = !kpair.dfn n
    (!value.dfn (!kpair.π₁.dfn x) (!value.dfn (!kpair.π₂.dfn x) n))”

theorem eval_compositeSequenceFormula (z x : M) :
    compositeSequenceFormula.Evalb ![z, x] ↔
      ∃ n ∈ (ω : M), z = ⟨n, (kpair.π₁ x) ‘ ((kpair.π₂ x) ‘ n)⟩ₖ := by
  simp [compositeSequenceFormula]

/-- A function on `ω` is the set of the pairs of its arguments with its values. -/
theorem mem_omega_function_iff {f D : M} (hf : f ∈ D ^ (ω : M)) (z : M) :
    z ∈ f ↔ ∃ n ∈ (ω : M), z = ⟨n, f ‘ n⟩ₖ := by
  haveI : IsFunction f := IsFunction.of_mem hf
  have hd : domain f = (ω : M) := domain_eq_of_mem_function hf
  constructor
  · intro hz
    obtain ⟨n, hn, y, -, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf z hz)
    exact ⟨n, hn, by rw [value_eq_of_kpair_mem hz]⟩
  · rintro ⟨n, hn, rfl⟩
    exact kpair_value_mem (by rw [hd]; exact hn)

/-- The names of a fixed checked set that the evaluation function sends to the `n`-th value of a
sequence. -/
noncomputable def nameChoiceFamily (Nmc E C n : M) : M := {t ∈ Nmc ; E ‘ t = C ‘ n}

theorem mem_nameChoiceFamily_iff (Nmc E C n t : M) :
    t ∈ nameChoiceFamily Nmc E C n ↔ t ∈ Nmc ∧ E ‘ t = C ‘ n := mem_sep_iff

theorem nameChoiceFamily_definable (Nmc E C : M) :
    ℒₛₑₜ-function₁[M] (nameChoiceFamily Nmc E C) := by
  have h : ℒₛₑₜ-relation[M] (fun y n : M ↦ ∀ t, t ∈ y ↔ (t ∈ Nmc ∧ E ‘ t = C ‘ n)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameChoiceFamily Nmc E C (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [nameChoiceFamily, mem_sep_iff]

end

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- An `ω`-sequence of the Levy extension with values in a checked set is definable from ground
sets, reals and ordinals. -/
theorem levy_ordinal_sequence_groundRealDefinable {θ : V} {g : (levyContext κ hG).Model}
    (hg : g ∈ (levyContext κ hG).check θ ^ (ω : (levyContext κ hG).Model)) :
    (levyContext κ hG).IsGroundRealDefinable g := by
  refine groundRealDefinable_of_isLocalized hAC hU hc hω hG
    (levy_sequence_localized (θ := θ) hAC hU hc hω hκ hG g ?_)
  rwa [ForcingContext.check_omega_eq]

include hAC hU hc hω hκ in
/-- An `ω`-sequence of the Levy extension all of whose values are ground sets is definable from
ground sets, reals and ordinals. -/
theorem levy_ground_sequence_groundRealDefinable {D s : (levyContext κ hG).Model}
    (hs : s ∈ D ^ (ω : (levyContext κ hG).Model))
    (hval : ∀ n ∈ (ω : (levyContext κ hG).Model),
      ∃ a : V, s ‘ n = (levyContext κ hG).check a) :
    (levyContext κ hG).IsGroundRealDefinable s := by
  haveI : IsFunction s := IsFunction.of_mem hs
  have hd : domain s = (ω : (levyContext κ hG).Model) := domain_eq_of_mem_function hs
  let B := levyContext κ hG
  -- the rank of the range of the sequence is an ordinal of the extension, hence a check
  obtain ⟨ρ, hρord, hρ⟩ := B.ordinal_eq_check (rank (range s))
  haveI : IsOrdinal ρ := hρord
  have hsub : range s ⊆ B.check (hierarchy ρ) := by
    intro y hy
    obtain ⟨n, hny⟩ := mem_range_iff.mp hy
    have hnd : n ∈ domain s := mem_domain_of_kpair_mem hny
    obtain ⟨a, ha⟩ := hval n (by rw [← hd]; exact hnd)
    have hya : y = B.check a := by rw [← value_eq_of_kpair_mem hny, ha]
    have hrk : rank y ∈ rank (range s) := rank_mem hy
    have hmr : B.check (rank a) = rank (B.check a) := B.checkEmbedding.map_rank a
    rw [hρ, hya, ← hmr] at hrk
    have hra : rank a ∈ ρ := (B.check_mem_iff (rank a) ρ).mp hrk
    rw [hya]
    exact (B.check_mem_iff a (hierarchy ρ)).mpr ((mem_hierarchy_iff_rank_mem a ρ).mpr hra)
  have hsf : s ∈ B.check (hierarchy ρ) ^ (ω : B.Model) :=
    mem_function_of_mem_function_of_subset (function_mem_of_isFunction' hd rfl) hsub
  exact levy_ordinal_sequence_groundRealDefinable hAC hU hc hω hκ hG hsf

include hAC hU hc hω hκ in
/-- An `ω`-sequence of the Levy extension all of whose values lie in one bounded stage `V[G_ζ]`,
`ζ < κ`, is definable from ground sets, reals and ordinals. -/
theorem levy_localized_sequence_groundRealDefinable {ζ : V} [IsOrdinal ζ] (hζ : ζ ∈ κ)
    {D C : (levyContext κ hG).Model} (hC : C ∈ D ^ (ω : (levyContext κ hG).Model))
    (hval : ∀ n ∈ (ω : (levyContext κ hG).Model),
      InLevySubmodel ζ (IsOrdinal.toIsTransitive.transitive ζ hζ) hG (C ‘ n)) :
    (levyContext κ hG).IsGroundRealDefinable C := by
  haveI : IsFunction C := IsFunction.of_mem hC
  have hd : domain C = (ω : (levyContext κ hG).Model) := domain_eq_of_mem_function hC
  have hζsub : ζ ⊆ κ := IsOrdinal.toIsTransitive.transitive ζ hζ
  let B := levyContext κ hG
  let L := levySubRealization ζ hζsub hG
  let N := levySubContext ζ hζsub hG
  let j := L.embedding
  have hjval : ∀ y : N.Model, (j y : B.Model) = L.value y := fun _ ↦ rfl
  have hjcheck : ∀ x : V, (j (N.check x) : B.Model) = B.check x :=
    fun x ↦ (L.value_check x).trans (levySubRealization_ground ζ hζsub hG x)
  -- the rank of the range is a check
  obtain ⟨ρ, hρord, hρ⟩ := B.ordinal_eq_check (rank (range C))
  haveI : IsOrdinal ρ := hρord
  haveI : IsOrdinal (N.check ρ) := (N.check_ordinal_iff ρ).mpr inferInstance
  let Nm : V := forcingNameHierarchy N.P ρ
  let E : B.Model := j (N.hierarchyEvaluation ρ)
  have ht₀dom : domain (N.hierarchyEvaluation ρ) = N.check Nm :=
    domain_eq_of_mem_function (N.hierarchyEvaluation_function ρ)
  -- every value of the sequence is the evaluation of a checked name of level `ρ`
  have hkey : ∀ n ∈ (ω : B.Model), ∃ t : B.Model, t ∈ B.check Nm ∧ E ‘ t = C ‘ n := by
    intro n hn
    obtain ⟨y, hy⟩ := hval n hn
    have hy' : (j y : B.Model) = C ‘ n := hy
    have hCn : C ‘ n ∈ range C := mem_range_iff.mpr ⟨n, kpair_value_mem (by rw [hd]; exact hn)⟩
    have hrk : rank (C ‘ n) ∈ B.check ρ := by rw [← hρ]; exact rank_mem hCn
    rw [← hy', ← j.map_rank y, ← hjcheck ρ] at hrk
    have hry : rank y ∈ N.check ρ := (j.mem_iff (rank y) (N.check ρ)).mp hrk
    have hyh : y ∈ hierarchy (N.check ρ) := (mem_hierarchy_iff_rank_mem y (N.check ρ)).mpr hry
    rw [← N.hierarchyEvaluation_range ρ] at hyh
    obtain ⟨t₀, ht₀⟩ := mem_range_iff.mp hyh
    have ht₀d : t₀ ∈ domain (N.hierarchyEvaluation ρ) := mem_domain_of_kpair_mem ht₀
    refine ⟨j t₀, ?_, ?_⟩
    · rw [← hjcheck Nm]
      exact (j.mem_iff t₀ (N.check Nm)).mpr (by rw [← ht₀dom]; exact ht₀d)
    · calc (E ‘ (j t₀) : B.Model) = j ((N.hierarchyEvaluation ρ) ‘ t₀) :=
            (j.map_value (N.hierarchyEvaluation ρ) t₀ ht₀d).symm
        _ = (j y : B.Model) := by rw [value_eq_of_kpair_mem ht₀]
        _ = C ‘ n := hy'
  -- choose a name for each value
  obtain ⟨g, hgfun, hgdom, hgval⟩ :=
    choice_for_definable_family (B.internalChoice_of_ground hAC) (ω : B.Model)
      (nameChoiceFamily (B.check Nm) E C) (nameChoiceFamily_definable _ _ _)
      (fun n hn ↦ by
        obtain ⟨t, ht, hEt⟩ := hkey n hn
        exact ⟨⟨t, (mem_nameChoiceFamily_iff _ _ _ _ _).mpr ⟨ht, hEt⟩⟩⟩)
  haveI : IsFunction g := hgfun
  have hgmem : ∀ n ∈ (ω : B.Model), g ‘ n ∈ B.check Nm ∧ E ‘ (g ‘ n) = C ‘ n :=
    fun n hn ↦ (mem_nameChoiceFamily_iff _ _ _ _ _).mp (hgval n hn)
  have hgsub : range g ⊆ B.check Nm := by
    intro y hy
    obtain ⟨n, hny⟩ := mem_range_iff.mp hy
    have hnd : n ∈ (ω : B.Model) := by rw [← hgdom]; exact mem_domain_of_kpair_mem hny
    rw [← value_eq_of_kpair_mem hny]
    exact (hgmem n hnd).1
  have hgf : g ∈ B.check Nm ^ (ω : B.Model) :=
    mem_function_of_mem_function_of_subset (function_mem_of_isFunction' hgdom rfl) hgsub
  -- both the evaluation function and the sequence of names are localized
  have hEloc : IsLocalized hG E := ⟨ζ, hζ, ⟨N.hierarchyEvaluation ρ, rfl⟩⟩
  have hgloc : IsLocalized hG g := levy_sequence_localized (θ := Nm) hAC hU hc hω hκ hG g
    (by rwa [ForcingContext.check_omega_eq])
  have hpair : B.IsGroundRealDefinable (⟨E, g⟩ₖ : B.Model) :=
    groundRealDefinable_of_isLocalized hAC hU hc hω hG (isLocalized_kpair hG hEloc hgloc)
  refine ForcingContext.groundRealDefinable_of_definable_from hpair compositeSequenceFormula
    (fun b ↦ ?_)
  rw [eval_compositeSequenceFormula, kpair.π₁_kpair, kpair.π₂_kpair,
    mem_omega_function_iff hC b]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, by rw [(hgmem n hn).2]⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, by rw [(hgmem n hn).2]⟩

end

end ZFVP
