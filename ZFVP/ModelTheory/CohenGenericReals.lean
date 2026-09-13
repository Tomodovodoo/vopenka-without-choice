import ZFVP.SetTheory.BaireCore
import ZFVP.SetTheory.FiniteSequencesCardinality
import ZFVP.SetTheory.MeasurableStrongLimit
import ZFVP.SetTheory.SequenceCollapseAbsorption
import ZFVP.SetTheory.EndExtensionCoding
import ZFVP.SetTheory.EndExtensionFinite
import ZFVP.ModelTheory.LevyCollapseOmegaOne

/-! Cohen reals over the ground model of a forcing extension: reals meeting every ground dense
set of finite binary sequences. When the ground dense sets are enumerated in the extension, a
set of reals decided by a set of finite sequences on the Cohen reals has the Baire property. In
the Levy extension of a measurable the ground dense sets are countable. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A dense set of finite binary sequences. -/
def IsDenseSequences (D : V) : Prop :=
  D ⊆ binarySequences V ∧ ∀ s ∈ binarySequences V, ∃ t ∈ D, s ⊆ t

instance isDenseSequences_definable : ℒₛₑₜ-predicate[V] IsDenseSequences := by
  unfold IsDenseSequences
  definability

theorem binarySequences_isDense : IsDenseSequences (binarySequences V) :=
  ⟨subset_refl _, fun s hs ↦ ⟨s, hs, subset_refl s⟩⟩

/-- The set of dense sets of finite binary sequences. -/
noncomputable def denseSequenceSets (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  {D ∈ ℘ (binarySequences V) ; IsDenseSequences D}

theorem mem_denseSequenceSets_iff (D : V) : D ∈ denseSequenceSets V ↔ IsDenseSequences D := by
  simp only [denseSequenceSets, mem_sep_iff, mem_power_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1, h⟩⟩

theorem binarySequences_cardLE_omega (hAC : InternalChoice V) : binarySequences V ≤# (ω : V) := by
  have hω : IsInitialOrdinal (ω : V) := ⟨IsOrdinal.ω, fun n hn ↦ omega_not_cardLE_natural hn⟩
  refine CardLE.trans (cardLE_of_subset ?_) (finiteSequences_cardLE_initial hAC hω (subset_refl _))
  intro s hs
  obtain ⟨n, hn, hsn⟩ := (mem_binarySequences_iff s).mp hs
  exact (mem_finiteSequences_iff _ _).mpr ⟨n, hn, mem_function_of_mem_function_of_subset hsn
    (IsTransitive.ω.transitive _ (ofNat_mem_ω 2))⟩

namespace ForcingContext

variable (A : ForcingContext V)

theorem check_binarySequences : A.check (binarySequences V) = binarySequences A.Model := by
  have h1 := A.checkEmbedding.map_finiteSequences ((2 : ℕ) : V)
  have h2 := A.checkEmbedding.map_numeral 2
  rw [h2] at h1
  exact h1

theorem check_isDenseSequences {D : V} (hD : IsDenseSequences D) : IsDenseSequences (A.check D) := by
  refine ⟨?_, ?_⟩
  · rw [← A.check_binarySequences]
    exact (A.checkEmbedding.subset_iff D _).mpr hD.1
  · intro s hs
    rw [← A.check_binarySequences] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := (A.mem_check_iff _ _).mp hs
    obtain ⟨t, ht, hst⟩ := hD.2 s₀ hs₀
    exact ⟨A.check t, (A.mem_check_iff _ _).mpr ⟨t, ht, rfl⟩, (A.checkEmbedding.subset_iff _ _).mpr hst⟩

/-- A real of the extension is Cohen over the ground when it meets every ground dense set of
finite binary sequences. -/
def IsCohenOver (x : A.Model) : Prop :=
  x ∈ cantorSpace A.Model ∧ ∀ D : V, IsDenseSequences D → Meets (A.check D) x

/-- A set of reals decided on the Cohen reals by a set of finite sequences has the Baire
property, given an enumeration of the ground dense sets in the extension. -/
theorem baireProperty_of_cohen_decision {X S e : A.Model} (hX : X ⊆ cantorSpace A.Model)
    (hS : S ⊆ binarySequences A.Model) (he : e ∈ (℘ (binarySequences A.Model)) ^ (ω : A.Model))
    (hdense : ∀ n ∈ (ω : A.Model), IsDenseSequences (e ‘ n))
    (henum : ∀ D : V, IsDenseSequences D → ∃ n ∈ (ω : A.Model), e ‘ n = A.check D)
    (hdec : ∀ x, A.IsCohenOver x → (x ∈ X ↔ Meets S x)) : BaireProperty X :=
  baireProperty_of_decision hX hS he (fun n hn ↦ (hdense n hn).2) (fun x hx hall ↦ hdec x ⟨hx,
    fun D hD ↦ by
      obtain ⟨n, hn, hen⟩ := henum D hD
      rw [← hen]
      exact hall n hn⟩)

/-- The ground dense sets are enumerated in the extension as soon as their ground set is
countable there. -/
theorem exists_dense_enumeration (hcount : IsInternallyCountable (A.check (denseSequenceSets V))) :
    ∃ e ∈ (℘ (binarySequences A.Model)) ^ (ω : A.Model),
      (∀ n ∈ (ω : A.Model), IsDenseSequences (e ‘ n)) ∧
      ∀ D : V, IsDenseSequences D → ∃ n ∈ (ω : A.Model), e ‘ n = A.check D := by
  have h0 : A.check (binarySequences V) ∈ A.check (denseSequenceSets V) :=
    (A.mem_check_iff _ _).mpr ⟨_, (mem_denseSequenceSets_iff _).mpr binarySequences_isDense, rfl⟩
  obtain ⟨E, hE, hrange⟩ := exists_surjection_of_cardLE hcount h0
  have hEf : IsFunction E := IsFunction.of_mem hE
  have hval : ∀ D ∈ A.check (denseSequenceSets V), IsDenseSequences D := by
    intro D hD
    obtain ⟨D₀, hD₀, rfl⟩ := (A.mem_check_iff _ _).mp hD
    exact A.check_isDenseSequences ((mem_denseSequenceSets_iff _).mp hD₀)
  refine ⟨E, mem_function_of_mem_function_of_subset hE (fun D hD ↦ mem_power_iff.mpr (hval D hD).1),
    fun n hn ↦ hval _ (function_value_mem hE hn), ?_⟩
  intro D hD
  have hmem : A.check D ∈ range E := by
    rw [hrange]
    exact (A.mem_check_iff _ _).mpr ⟨D, (mem_denseSequenceSets_iff _).mpr hD, rfl⟩
  obtain ⟨n, hn⟩ := mem_range_iff.mp hmem
  have hnω : n ∈ (ω : A.Model) := by
    rw [← domain_eq_of_mem_function hE]
    exact mem_domain_of_kpair_mem hn
  exact ⟨n, hnω, value_eq_of_kpair_mem hn⟩

end ForcingContext

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω in
/-- Below a measurable, the dense sets of finite binary sequences are fewer than `κ`. -/
theorem denseSequenceSets_small : ∃ ν ∈ κ, denseSequenceSets V ≤# ν := by
  obtain ⟨ν, hν, hpow⟩ := power_small_of_measurable hAC hU hc hω (binarySequences_cardLE_omega hAC)
  exact ⟨ν, hν, CardLE.trans (cardLE_of_subset (fun D hD ↦ (mem_sep_iff.mp hD).1)) hpow⟩

include hAC hU hc hω hκ hG in
/-- In the Levy extension of a measurable, the ground dense sets are enumerated. -/
theorem levy_exists_dense_enumeration :
    ∃ e ∈ (℘ (binarySequences (levyContext κ hG).Model)) ^ (ω : (levyContext κ hG).Model),
      (∀ n ∈ (ω : (levyContext κ hG).Model), IsDenseSequences (e ‘ n)) ∧
      ∀ D : V, IsDenseSequences D →
        ∃ n ∈ (ω : (levyContext κ hG).Model), e ‘ n = (levyContext κ hG).check D := by
  apply (levyContext κ hG).exists_dense_enumeration
  obtain ⟨ν, hν, hsmall⟩ := denseSequenceSets_small hAC hU hc hω
  have h1 := (levyContext κ hG).checkEmbedding.map_cardLE hsmall
  have h2 := levy_check_countable hG hν
  exact CardLE.trans h1 h2

end

end ZFVP
