import ZFVP.SetTheory.UltrapowerBase
import ZFVP.SetTheory.UniformCollapse
import ZFVP.SetTheory.DependentChoice

/-! The a.e. membership relation of an internal ultrapower, as an internal set, and its
well-foundedness. The relation `aeMemRelation P U A` holds of a pair of functions from the index
set `P` into `A` when the first one's value belongs to the second one's on a set of indices in the
ultrafilter `U`. If `U` is closed under intersections of `ω`-many of its members, the relation is
internally well founded: an internal descending chain of functions would give one index at which
the real membership chain descends forever, which the foundation axiom forbids. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The a.e. membership relation on the functions from `P` into `A`, as an internal set. -/
noncomputable def aeMemRelation (P U A : V) : V :=
  {q ∈ (A ^ P) ×ˢ (A ^ P) ; AEMem P U (kpair.π₁ q) (kpair.π₂ q)}

instance aeMemRelation_definable : ℒₛₑₜ-function₃[V] aeMemRelation := by
  have hd : ℒₛₑₜ-relation₄[V] (fun R P U A ↦ ∀ q, q ∈ R ↔
      q ∈ (A ^ P) ×ˢ (A ^ P) ∧ AEMem P U (kpair.π₁ q) (kpair.π₂ q)) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = aeMemRelation (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [aeMemRelation, mem_sep_iff]

theorem pair_mem_aeMemRelation_iff (P U A f g : V) :
    ⟨f, g⟩ₖ ∈ aeMemRelation P U A ↔ f ∈ A ^ P ∧ g ∈ A ^ P ∧ AEMem P U f g := by
  simp [aeMemRelation, and_assoc]

theorem aeMemRelation_subset (P U A : V) : aeMemRelation P U A ⊆ (A ^ P) ×ˢ (A ^ P) := by
  intro q hq
  exact (mem_sep_iff.mp hq).1

/-- The a.e. membership relation of an ultrafilter that is complete for intersections of
`ω`-many of its members is internally well founded: an internal descending chain would give a
single index at which the real membership chain descends forever. -/
theorem aeMemRelation_wellFounded (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ]
    (hU : IsSetUltrafilter P U)
    (hcomp : ∀ α ∈ κ, ∀ g ∈ U ^ α, indexedIntersection P α g ∈ U) (hω : (ω : V) ∈ κ) :
    IsInternallyWellFounded (aeMemRelation P U A) (A ^ P) := by
  intro B hB hne
  by_contra hcon
  push Not at hcon
  -- The reversed relation, restricted to `B`.
  have hRd : ℒₛₑₜ-predicate (fun q : V ↦ ⟨kpair.π₂ q, kpair.π₁ q⟩ₖ ∈ aeMemRelation P U A) := by
    definability
  set R' : V := sep (B ×ˢ B) (fun q ↦ ⟨kpair.π₂ q, kpair.π₁ q⟩ₖ ∈ aeMemRelation P U A) hRd
    with hR'def
  have hpairR' : ∀ x y : V, x ∈ B → y ∈ B →
      ⟨y, x⟩ₖ ∈ aeMemRelation P U A → ⟨x, y⟩ₖ ∈ R' := by
    intro x y hx hy hxy
    rw [hR'def, mem_sep_iff]
    refine ⟨mem_prod_iff.mpr ⟨x, hx, y, hy, rfl⟩, ?_⟩
    simpa using hxy
  have hserial : ∀ x ∈ B, ∃ y ∈ B, ⟨x, y⟩ₖ ∈ R' := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hcon x hx
    exact ⟨y, hy, hpairR' x y hx hy hyx⟩
  obtain ⟨s, hsf, hstep⟩ :=
    dependentChoice_of_internalChoice hAC B R' hne hserial
  -- Each step of the chain gives a set of indices in the ultrafilter.
  have hmem : ∀ n ∈ (ω : V), membershipSet P (s ‘ (succ n)) (s ‘ n) ∈ U := by
    intro n hn
    have h := hstep n hn
    rw [hR'def, mem_sep_iff] at h
    have h2 := h.2
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at h2
    exact ((pair_mem_aeMemRelation_iff P U A (s ‘ (succ n)) (s ‘ n)).mp h2).2.2
  have hF : ℒₛₑₜ-function₁ (fun n : V ↦ membershipSet P (s ‘ (succ n)) (s ‘ n)) := by
    definability
  set g : V := definableGraph (ω : V) (fun n ↦ membershipSet P (s ‘ (succ n)) (s ‘ n)) hF
    with hgdef
  have hgf : g ∈ U ^ (ω : V) :=
    definableGraph_mem_function_of_mapsTo _ _ _ hF hmem
  have hint : indexedIntersection P (ω : V) g ∈ U := hcomp (ω : V) hω g hgf
  obtain ⟨p, hp⟩ := (hU.isNonempty_of_mem hint).nonempty
  rw [mem_indexedIntersection_iff] at hp
  have hchain : ∀ n ∈ (ω : V), (s ‘ (succ n)) ‘ p ∈ (s ‘ n) ‘ p := by
    intro n hn
    have h := hp.2 n hn
    rw [hgdef, value_definableGraph _ _ hF hn, mem_membershipSet_iff] at h
    exact h.2
  -- The pointwise values at `p` form a set with no membership-minimal element.
  have hT : ℒₛₑₜ-function₁ (fun n : V ↦ (s ‘ n) ‘ p) := by definability
  set T : V := range (definableGraph (ω : V) (fun n ↦ (s ‘ n) ‘ p) hT) with hTdef
  have hmemT : ∀ t : V, t ∈ T ↔ ∃ n ∈ (ω : V), t = (s ‘ n) ‘ p := by
    intro t
    rw [hTdef, range_definableGraph, repl_spec]
  have hTne : IsNonempty T :=
    ⟨(s ‘ (∅ : V)) ‘ p, (hmemT _).mpr ⟨∅, empty_mem_ω, rfl⟩⟩
  obtain ⟨x, hx, hxmin⟩ := membershipRelation_wellFounded T T (fun _ h ↦ h) hTne
  obtain ⟨n, hn, rfl⟩ := (hmemT x).mp hx
  have hy : (s ‘ (succ n)) ‘ p ∈ T := (hmemT _).mpr ⟨succ n, ω_succ_closed hn, rfl⟩
  exact hxmin _ hy ((pair_mem_membershipRelation T _ _).mpr ⟨hy, hx, hchain n hn⟩)

end ZFVP
