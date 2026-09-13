import ZFVP.ModelTheory.CohenBridgeLemmas
import ZFVP.ModelTheory.LevyCollapseReals
import ZFVP.ModelTheory.LevyCollapseSubmodel
import ZFVP.SetTheory.StandardNaturals
import ZFVP.SetTheory.EndExtensionSets
import ZFVP.ModelTheory.GroundRealsHOD

/-! A Cohen real of the Levy extension lies in a bounded stage `V[G_ξ]`, and its finite initial
segments there form a filter on the checked Cohen poset which meets every ground dense set and
whose union is the real. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable (A : ForcingContext V)

/-- The finite initial segments of a real, as a subset of the checked Cohen poset. -/
noncomputable def initialSegments (y : A.Model) : A.Model := {s ∈ A.check (binarySequences V) ; s ⊆ y}

theorem mem_initialSegments_iff (y s : A.Model) :
    s ∈ A.initialSegments y ↔ s ∈ A.check (binarySequences V) ∧ s ⊆ y := by
  simp only [initialSegments, mem_sep_iff]

theorem initialSegments_subset (y : A.Model) : A.initialSegments y ⊆ A.check (binarySequences V) :=
  fun s hs ↦ ((A.mem_initialSegments_iff y s).mp hs).1

theorem check_mem_initialSegments_iff (y : A.Model) (s : V) :
    A.check s ∈ A.initialSegments y ↔ s ∈ binarySequences V ∧ A.check s ⊆ y := by
  rw [A.mem_initialSegments_iff, A.check_mem_iff]

theorem sUnion_initialSegments_eq {y : A.Model} (hy : y ∈ cantorSpace A.Model) :
    ⋃ˢ (A.initialSegments y) = y := by
  unfold initialSegments
  rw [A.check_binarySequences]
  exact sUnion_initialSegments hy

/-- The initial segments of a real form a filter on the checked Cohen poset. -/
theorem initialSegments_filter {y : A.Model} (hy : y ∈ cantorSpace A.Model) :
    IsForcingFilter (A.check (binarySequences V)) (A.check (sequenceOrder ((2 : ℕ) : V)))
      (A.initialSegments y) := by
  have hyf : IsFunction y := IsFunction.of_mem hy
  rw [A.check_sequenceOrder]
  refine ⟨A.initialSegments_subset y, ⟨A.check ∅, ?_⟩, ?_, ?_⟩
  · rw [A.mem_initialSegments_iff, A.check_empty]
    refine ⟨?_, empty_subset y⟩
    rw [A.check_binarySequences]
    exact empty_mem_finiteSequences _
  · intro s hs t ht hst
    obtain ⟨_, hsy⟩ := (A.mem_initialSegments_iff y s).mp hs
    rw [A.check_binarySequences] at ht
    have hts : t ⊆ s := ((pair_mem_sequenceOrder_iff _ _ _).mp hst).2.2
    exact (A.mem_initialSegments_iff y t).mpr ⟨by rw [A.check_binarySequences]; exact ht, subset_trans hts hsy⟩
  · intro s hs t ht
    obtain ⟨hsB, hsy⟩ := (A.mem_initialSegments_iff y s).mp hs
    obtain ⟨htB, hty⟩ := (A.mem_initialSegments_iff y t).mp ht
    rw [A.check_binarySequences] at hsB htB
    have hsf : IsFunction s := binarySequence_isFunction hsB
    have htf : IsFunction t := binarySequence_isFunction htB
    have hs' : s = y ↾ (domain s) := (restrict_domain_eq_of_subset hsy).symm
    have ht' : t = y ↾ (domain t) := (restrict_domain_eq_of_subset hty).symm
    have hds := binarySequence_domain_mem hsB
    have hdt := binarySequence_domain_mem htB
    have : IsOrdinal (domain s) := IsOrdinal.of_mem hds
    have : IsOrdinal (domain t) := IsOrdinal.of_mem hdt
    rcases IsOrdinal.subset_or_supset (α := domain s) (β := domain t) with h | h
    · refine ⟨t, ht, ?_, (pair_mem_sequenceOrder_iff _ _ _).mpr ⟨htB, htB, subset_refl t⟩⟩
      refine (pair_mem_sequenceOrder_iff _ _ _).mpr ⟨htB, hsB, ?_⟩
      rw [hs', ht', ← restrict_restrict_of_subset h]
      exact restrict_subset _ _
    · refine ⟨s, hs, (pair_mem_sequenceOrder_iff _ _ _).mpr ⟨hsB, hsB, subset_refl s⟩, ?_⟩
      refine (pair_mem_sequenceOrder_iff _ _ _).mpr ⟨hsB, htB, ?_⟩
      rw [hs', ht', ← restrict_restrict_of_subset h]
      exact restrict_subset _ _

/-- If the real is Cohen over the ground in a larger extension realizing `A`, its initial segments
meet every ground dense set. -/
theorem initialSegments_generic {B : ForcingContext V} (L : ForcingRealization A B.Model)
    (hground : ∀ a : V, L.ground a = B.check a)
    {y : A.Model} {x : B.Model} (hval : L.value y = x) (hx : B.IsCohenOver x) :
    ∀ D : V, ForcingDense (binarySequences V) (sequenceOrder ((2 : ℕ) : V)) D →
      ∃ q ∈ D, A.check q ∈ A.initialSegments y := by
  intro D hD
  have hDs := isDenseSequences_of_forcingDense hD
  obtain ⟨s, hs, hsx⟩ := subset_of_meets (B.check_isDenseSequences hDs).1 hx.1 (hx.2 D hDs)
  obtain ⟨q, hq, rfl⟩ := (B.mem_check_iff _ _).mp hs
  refine ⟨q, hq, (A.check_mem_initialSegments_iff y q).mpr ⟨hDs.1 q hq, ?_⟩⟩
  have h : L.value (A.check q) ⊆ L.value y := by
    rw [L.value_check, hground, hval]
    exact hsx
  exact (L.embedding.subset_iff _ _).mp h

theorem check_mem_initialSegments_iff_of_value {B : ForcingContext V} (L : ForcingRealization A B.Model)
    (hground : ∀ a : V, L.ground a = B.check a)
    {y : A.Model} {x : B.Model} (hval : L.value y = x) (s : V) :
    A.check s ∈ A.initialSegments y ↔ s ∈ binarySequences V ∧ B.check s ⊆ x := by
  rw [A.check_mem_initialSegments_iff]
  apply and_congr_right
  intro _
  rw [← hval, ← hground s, ← L.value_check]
  exact (L.embedding.subset_iff _ _).symm

end ForcingContext

theorem realCodePredicate_definable (dω d1 d0 r : V) :
    ℒₛₑₜ-predicate (fun z : V ↦ ∃ n ∈ dω, (z = ⟨n, d1⟩ₖ ∧ n ∈ r) ∨ (z = ⟨n, d0⟩ₖ ∧ n ∉ r)) := by
  definability

/-- A real of an extension whose coding real is the value of an element of a realized smaller
extension is itself the value of a real of the smaller extension. -/
theorem exists_real_copy {A B : ForcingContext V} (L : ForcingRealization A B.Model)
    (hground : ∀ a : V, L.ground a = B.check a) {x : B.Model} (hxc : x ∈ cantorSpace B.Model)
    {r₀ : A.Model} (hr₀ : L.value r₀ = {n ∈ B.check (ω : V) ; ⟨n, B.check ((1 : ℕ) : V)⟩ₖ ∈ x}) :
    ∃ y : A.Model, L.value y = x ∧ y ∈ cantorSpace A.Model := by
  have hxf : IsFunction x := IsFunction.of_mem hxc
  have hxdom : domain x = (ω : B.Model) := domain_eq_of_mem_function hxc
  have hω' : B.check (ω : V) = (ω : B.Model) := B.check_omega_eq
  have hnum : ∀ k : ℕ, B.check ((k : ℕ) : V) = ((k : ℕ) : B.Model) := fun k ↦ B.checkEmbedding.map_numeral k
  have hprod : B.check ((ω : V) ×ˢ ((2 : ℕ) : V)) = (ω : B.Model) ×ˢ ((2 : ℕ) : B.Model) := by
    have h := B.checkEmbedding.map_prod (ω : V) ((2 : ℕ) : V)
    change B.check _ = B.check _ ×ˢ B.check _ at h
    rw [h, hω', hnum 2]
  obtain ⟨r, hr, hrdef⟩ : ∃ r : B.Model, (∀ n, n ∈ r ↔ n ∈ B.check (ω : V) ∧ ⟨n, B.check ((1 : ℕ) : V)⟩ₖ ∈ x) ∧
      r = {n ∈ B.check (ω : V) ; ⟨n, B.check ((1 : ℕ) : V)⟩ₖ ∈ x} :=
    ⟨{n ∈ B.check (ω : V) ; ⟨n, B.check ((1 : ℕ) : V)⟩ₖ ∈ x}, fun n ↦ by simp only [mem_sep_iff], rfl⟩
  have hr₀' : L.value r₀ = r := by rw [hr₀, hrdef]
  -- the values of `x` are `0` or `1`
  have hvalues : ∀ z ∈ x, ∃ n ∈ B.check (ω : V), z = ⟨n, B.check ((1 : ℕ) : V)⟩ₖ ∨ z = ⟨n, B.check ((0 : ℕ) : V)⟩ₖ := by
    intro z hz
    obtain ⟨n, hn, i, hi, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hxc z hz)
    refine ⟨n, by rw [hω']; exact hn, ?_⟩
    obtain ⟨k, rfl⟩ := (mem_natCast_iff i 2).mp hi
    have hk : k.val = 0 ∨ k.val = 1 := by omega
    rcases hk with hk | hk
    · right
      rw [hk, hnum 0]
    · left
      rw [hk, hnum 1]
  have h10 : B.check ((1 : ℕ) : V) ≠ B.check ((0 : ℕ) : V) := by
    rw [hnum 1, hnum 0]
    intro h
    exact absurd ((natCast_eq_iff 1 0).mp h) (by omega)
  -- `x` is recovered from `r`
  have hxeq : x = {z ∈ B.check ((ω : V) ×ˢ ((2 : ℕ) : V)) ; ∃ n ∈ B.check (ω : V),
      (z = ⟨n, B.check ((1 : ℕ) : V)⟩ₖ ∧ n ∈ r) ∨ (z = ⟨n, B.check ((0 : ℕ) : V)⟩ₖ ∧ n ∉ r)} := by
    apply mem_ext
    intro z
    rw [mem_sep_iff, hprod]
    constructor
    · intro hz
      refine ⟨subset_prod_of_mem_function hxc z hz, ?_⟩
      obtain ⟨n, hn, h1 | h0⟩ := hvalues z hz
      · exact ⟨n, hn, Or.inl ⟨h1, (hr n).mpr ⟨hn, h1 ▸ hz⟩⟩⟩
      · refine ⟨n, hn, Or.inr ⟨h0, fun hnr ↦ ?_⟩⟩
        have h1 := ((hr n).mp hnr).2
        rw [h0] at hz
        exact h10 (value_eq_of_kpair_mem h1 ▸ value_eq_of_kpair_mem hz)
    · rintro ⟨_, n, hn, ⟨rfl, hnr⟩ | ⟨rfl, hnr⟩⟩
      · exact ((hr n).mp hnr).2
      · have hndom : n ∈ domain x := by rw [hxdom, ← hω']; exact hn
        have hmem := kpair_value_mem hndom
        obtain ⟨n', _, h1 | h0⟩ := hvalues _ hmem
        · obtain ⟨rfl, hv⟩ := kpair_iff.mp h1
          exact absurd ((hr n).mpr ⟨hn, hv ▸ hmem⟩) hnr
        · obtain ⟨rfl, hv⟩ := kpair_iff.mp h0
          rw [hv] at hmem
          exact hmem
  have hvc : ∀ a : V, L.value (A.check a) = B.check a := fun a ↦ (L.value_check a).trans (hground a)
  have hk : ∀ a b : A.Model, L.value ⟨a, b⟩ₖ = ⟨L.value a, L.value b⟩ₖ := fun a b ↦ L.embedding.map_kpair a b
  have hmem : ∀ a b : A.Model, L.value a ∈ L.value b ↔ a ∈ b := fun a b ↦ L.value_mem_iff a b
  have hend : ∀ (a : V) (z' : B.Model), z' ∈ B.check a → ∃ z, z ∈ A.check a ∧ L.value z = z' := by
    intro a z' hz'
    obtain ⟨b, hb, rfl⟩ := (B.mem_check_iff _ _).mp hz'
    exact ⟨A.check b, (A.check_mem_iff _ _).mpr hb, hvc b⟩
  -- opaque names for the checked parameters
  obtain ⟨cω, hcω⟩ : ∃ c : A.Model, c = A.check (ω : V) := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c : A.Model, c = A.check ((1 : ℕ) : V) := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c : A.Model, c = A.check ((0 : ℕ) : V) := ⟨_, rfl⟩
  obtain ⟨cP, hcP⟩ : ∃ c : A.Model, c = A.check ((ω : V) ×ˢ ((2 : ℕ) : V)) := ⟨_, rfl⟩
  obtain ⟨dω, hdω⟩ : ∃ d : B.Model, d = B.check (ω : V) := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ d : B.Model, d = B.check ((1 : ℕ) : V) := ⟨_, rfl⟩
  obtain ⟨d0, hd0⟩ : ∃ d : B.Model, d = B.check ((0 : ℕ) : V) := ⟨_, rfl⟩
  obtain ⟨dP, hdP⟩ : ∃ d : B.Model, d = B.check ((ω : V) ×ˢ ((2 : ℕ) : V)) := ⟨_, rfl⟩
  have hvω : L.value cω = dω := by rw [hcω, hdω]; exact hvc _
  have hv1 : L.value c1 = d1 := by rw [hc1, hd1]; exact hvc _
  have hv0 : L.value c0 = d0 := by rw [hc0, hd0]; exact hvc _
  have hvP : L.value cP = dP := by rw [hcP, hdP]; exact hvc _
  have hendω : ∀ z' : B.Model, z' ∈ dω → ∃ z, z ∈ cω ∧ L.value z = z' := by
    rw [hcω, hdω]
    exact hend _
  have hxeq' : x = sep dP (fun z ↦ ∃ n ∈ dω, (z = ⟨n, d1⟩ₖ ∧ n ∈ r) ∨ (z = ⟨n, d0⟩ₖ ∧ n ∉ r))
      (realCodePredicate_definable dω d1 d0 r) := by
    rw [hdP, hdω, hd1, hd0]
    exact hxeq
  -- the copy of `x` in the smaller extension
  have hsep := L.embedding.map_separation cP
    (fun z ↦ ∃ n ∈ cω, (z = ⟨n, c1⟩ₖ ∧ n ∈ r₀) ∨ (z = ⟨n, c0⟩ₖ ∧ n ∉ r₀))
    (fun z ↦ ∃ n ∈ dω, (z = ⟨n, d1⟩ₖ ∧ n ∈ r) ∨ (z = ⟨n, d0⟩ₖ ∧ n ∉ r))
    (realCodePredicate_definable cω c1 c0 r₀) (realCodePredicate_definable dω d1 d0 r) (by
      intro z _
      constructor
      · rintro ⟨n, hn, ⟨rfl, hnr⟩ | ⟨rfl, hnr⟩⟩
        · refine ⟨L.value n, by rw [← hvω]; exact (hmem _ _).mpr hn, Or.inl ⟨?_, ?_⟩⟩
          · change L.value _ = _
            rw [hk, hv1]
          · rw [← hr₀']
            exact (hmem _ _).mpr hnr
        · refine ⟨L.value n, by rw [← hvω]; exact (hmem _ _).mpr hn, Or.inr ⟨?_, ?_⟩⟩
          · change L.value _ = _
            rw [hk, hv0]
          · rw [← hr₀', hmem]
            exact hnr
      · rintro ⟨n', hn', ⟨he, hnr⟩ | ⟨he, hnr⟩⟩
        · obtain ⟨n, hn, rfl⟩ := hendω n' hn'
          refine ⟨n, hn, Or.inl ⟨?_, ?_⟩⟩
          · apply L.value_injective
            change L.value z = L.value ⟨n, c1⟩ₖ
            rw [hk, hv1]
            exact he
          · rw [← hr₀', hmem] at hnr
            exact hnr
        · obtain ⟨n, hn, rfl⟩ := hendω n' hn'
          refine ⟨n, hn, Or.inr ⟨?_, ?_⟩⟩
          · apply L.value_injective
            change L.value z = L.value ⟨n, c0⟩ₖ
            rw [hk, hv0]
            exact he
          · rw [← hr₀', hmem] at hnr
            exact hnr)
  have hsep' : L.value (sep cP (fun z ↦ ∃ n ∈ cω, (z = ⟨n, c1⟩ₖ ∧ n ∈ r₀) ∨ (z = ⟨n, c0⟩ₖ ∧ n ∉ r₀))
      (realCodePredicate_definable cω c1 c0 r₀)) =
      sep (L.value cP) (fun z ↦ ∃ n ∈ dω, (z = ⟨n, d1⟩ₖ ∧ n ∈ r) ∨ (z = ⟨n, d0⟩ₖ ∧ n ∉ r))
        (realCodePredicate_definable dω d1 d0 r) := hsep
  rw [hvP, ← hxeq'] at hsep'
  refine ⟨_, hsep', ?_⟩
  -- the copy is a real
  have hAω : A.check (ω : V) = (ω : A.Model) := A.check_omega_eq
  have hA2 : A.check ((2 : ℕ) : V) = ((2 : ℕ) : A.Model) := A.checkEmbedding.map_numeral 2
  have h := (L.embedding.function_iff _ (A.check (ω : V)) (A.check ((2 : ℕ) : V))).mp (by
    change L.value _ ∈ L.value (A.check ((2 : ℕ) : V)) ^ L.value (A.check (ω : V))
    rw [hsep', hvc, hvc, hω', hnum 2]
    exact hxc)
  rw [hAω, hA2] at h
  exact h

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- A real of the Levy extension lies in a bounded stage, as a real there. -/
theorem exists_real_stage {x : (levyContext κ hG).Model} (hxc : x ∈ cantorSpace (levyContext κ hG).Model) :
    ∃ ξ : V, ∃ hξ : ξ ∈ κ,
      haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
      ∃ y : (levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).Model,
        (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value y = x ∧
        y ∈ cantorSpace (levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).Model := by
  have hrω : {n ∈ (levyContext κ hG).check (ω : V) ; ⟨n, (levyContext κ hG).check ((1 : ℕ) : V)⟩ₖ ∈ x} ⊆
      (levyContext κ hG).check (ω : V) := fun n hn ↦ (mem_sep_iff.mp hn).1
  obtain ⟨ξ, hξ, hin⟩ := levy_real_localized hAC hU hc hω hκ hG _ hrω
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  refine ⟨ξ, hξ, ?_⟩
  obtain ⟨r₀, hr₀⟩ := hin
  exact exists_real_copy (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG)
    (levySubRealization_ground ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG) hxc hr₀

end

end ZFVP
