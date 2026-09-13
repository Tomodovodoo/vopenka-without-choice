import ZFVP.ModelTheory.SubalgebraProjection
import ZFVP.SetTheory.EndExtensionAtomicForcing

/-! The quotient forcing `B / (G ∩ D)`: inside the intermediate extension `V[G ∩ D]` by a complete
subalgebra `D` of the Boolean completion `B`, the conditions whose projection to `D` lies in the
generic form a forcing poset, and the Boolean generic is generic for it over `V[G ∩ D]`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem subalgebraProjectionSet_top {P R D : V} (hD : IsCompleteSubalgebra P R D) :
    subalgebraProjectionSet D P = P :=
  SetTheory.subset_antisymm (subalgebraProjectionSet_subset hD.2.1 (fun x hx ↦ hx))
    (subset_subalgebraProjectionSet hD (fun x hx ↦ hx))

theorem subalgebraProjectionSet_subset_poset {P R D b : V} (hD : IsCompleteSubalgebra P R D)
    (hb : b ⊆ P) : subalgebraProjectionSet D b ⊆ P :=
  subalgebraProjectionSet_subset hD.2.1 hb

theorem subalgebraProjectionSet_mem_conditions {P R D b : V} (hD : IsCompleteSubalgebra P R D)
    (hR : IsForcingPreorder P R) (hb : b ∈ booleanConditions P R) :
    subalgebraProjectionSet D b ∈ subalgebraConditions P R D := by
  have hbP := booleanConditions_subset hb
  obtain ⟨p, hp⟩ := booleanConditions_nonempty hb
  exact (mem_subalgebraConditions_iff _ _ _ _).mpr ⟨subalgebraProjectionSet_mem hD hR hbP,
    (mem_booleanConditions_iff _ _ _).mpr ⟨hD.regular (subalgebraProjectionSet_mem hD hR hbP), p,
      subset_subalgebraProjectionSet hD hbP p hp⟩⟩

/-- The projection as a set function on the Boolean conditions. -/
noncomputable def subalgebraProjection (P R D : V) : V :=
  definableGraph (booleanConditions P R) (subalgebraProjectionSet D) (subalgebraProjectionSet_definable D)

theorem subalgebraProjection_value {P R D b : V} (hb : b ∈ booleanConditions P R) :
    (subalgebraProjection P R D) ‘ b = subalgebraProjectionSet D b :=
  value_definableGraph _ _ _ hb

theorem subalgebraProjection_mem_function {P R D : V} (hD : IsCompleteSubalgebra P R D)
    (hR : IsForcingPreorder P R) :
    subalgebraProjection P R D ∈ (subalgebraConditions P R D) ^ (booleanConditions P R) := by
  apply mem_function_of_mem_function_of_subset (definableGraph_mem_function _ _ _)
  intro y hy
  obtain ⟨b, hb, rfl⟩ := (repl_spec _).mp hy
  exact subalgebraProjectionSet_mem_conditions hD hR hb

/-- Conditions lying below some `c` and below some `d ⊆ h(c)` forcing `č ∈ Ḋ`. -/
noncomputable def quotientWitnessSet (P R D Dn : V) : V :=
  sep (booleanConditions P R) (fun b' ↦ ∃ c ∈ booleanConditions P R, b' ⊆ c ∧
    ∃ d ∈ subalgebraConditions P R D, b' ⊆ d ∧ d ⊆ subalgebraProjectionSet D c ∧
      d ∈ atomicMembership (subalgebraConditions P R D)
        (restrictedOrder (booleanOrder P R) (subalgebraConditions P R D)) (checkName P c) Dn)
    (by
      have := atomicMembership_definable (subalgebraConditions P R D)
        (restrictedOrder (booleanOrder P R) (subalgebraConditions P R D))
      have := subalgebraProjectionSet_definable D
      definability)

theorem mem_quotientWitnessSet_iff (P R D Dn b' : V) :
    b' ∈ quotientWitnessSet P R D Dn ↔ b' ∈ booleanConditions P R ∧ ∃ c ∈ booleanConditions P R, b' ⊆ c ∧
      ∃ d ∈ subalgebraConditions P R D, b' ⊆ d ∧ d ⊆ subalgebraProjectionSet D c ∧
        d ∈ atomicMembership (subalgebraConditions P R D)
          (restrictedOrder (booleanOrder P R) (subalgebraConditions P R D)) (checkName P c) Dn :=
  mem_sep_iff

/-- The witness set together with the conditions having no extension in it. -/
noncomputable def quotientDenseSet (P R D Dn : V) : V :=
  quotientWitnessSet P R D Dn ∪
    sep (booleanConditions P R) (fun b ↦ ∀ b' ∈ quotientWitnessSet P R D Dn, ¬ (b' ⊆ b)) (by definability)

theorem mem_quotientDenseSet_iff (P R D Dn b : V) :
    b ∈ quotientDenseSet P R D Dn ↔ b ∈ quotientWitnessSet P R D Dn ∨
      (b ∈ booleanConditions P R ∧ ∀ b' ∈ quotientWitnessSet P R D Dn, ¬ (b' ⊆ b)) := by
  unfold quotientDenseSet
  rw [mem_union_iff, mem_sep_iff]

namespace ForcingContext

variable (A : ForcingContext V) {D : V} (hD : IsCompleteSubalgebra A.P A.R D)

/-- The quotient poset `B / (G ∩ D)` inside `V[G ∩ D]`: Boolean conditions whose projection to
`D` lies in the generic. -/
noncomputable def quotientConditions : (A.subalgebraContext hD).Model :=
  sep ((A.subalgebraContext hD).check (booleanConditions A.P A.R))
    (fun x ↦ ((A.subalgebraContext hD).check (subalgebraProjection A.P A.R D)) ‘ x ∈
      (A.subalgebraContext hD).genericSet)
    (by definability)

theorem quotientConditions_subset :
    A.quotientConditions hD ⊆ (A.subalgebraContext hD).check (booleanConditions A.P A.R) :=
  sep_subset

theorem check_mem_quotientConditions_iff (b : V) :
    (A.subalgebraContext hD).check b ∈ A.quotientConditions hD ↔ b ∈ booleanConditions A.P A.R ∧
      subalgebraProjectionSet D b ∈
        traceGeneric (booleanGeneric A.P A.R A.G) (subalgebraConditions A.P A.R D) := by
  haveI : IsFunction (subalgebraProjection A.P A.R D) :=
    IsFunction.of_mem (subalgebraProjection_mem_function hD A.order)
  unfold quotientConditions
  rw [mem_sep_iff, (A.subalgebraContext hD).check_mem_iff]
  constructor
  · rintro ⟨hb, hx⟩
    rw [(A.subalgebraContext hD).check_value (by
        rw [domain_eq_of_mem_function (subalgebraProjection_mem_function hD A.order)]; exact hb),
      subalgebraProjection_value hb, (A.subalgebraContext hD).check_mem_genericSet_iff] at hx
    exact ⟨hb, hx⟩
  · rintro ⟨hb, hx⟩
    refine ⟨hb, ?_⟩
    rw [(A.subalgebraContext hD).check_value (by
        rw [domain_eq_of_mem_function (subalgebraProjection_mem_function hD A.order)]; exact hb),
      subalgebraProjection_value hb, (A.subalgebraContext hD).check_mem_genericSet_iff]
    exact hx

/-- The quotient order: inclusion of Boolean conditions, transported into `V[G ∩ D]`. -/
noncomputable def quotientOrder : (A.subalgebraContext hD).Model :=
  restrictedOrder ((A.subalgebraContext hD).check (booleanOrder A.P A.R)) (A.quotientConditions hD)

/-- The Boolean generic viewed inside `V[G ∩ D]`. -/
def quotientGeneric : Set (A.subalgebraContext hD).Model :=
  {x | ∃ b ∈ booleanGeneric A.P A.R A.G, x = (A.subalgebraContext hD).check b}

theorem quotientOrder_preorder :
    IsForcingPreorder (A.quotientConditions hD) (A.quotientOrder hD) :=
  restrictedOrder_preorder
    ((A.subalgebraContext hD).checkEmbedding.map_forcingPreorder (booleanOrder_poset A.P A.R).1)
    (A.quotientConditions_subset hD)

theorem check_kpair_mem_quotientOrder_iff {b c : V} :
    ⟨(A.subalgebraContext hD).check b, (A.subalgebraContext hD).check c⟩ₖ ∈ A.quotientOrder hD ↔
      ⟨b, c⟩ₖ ∈ booleanOrder A.P A.R ∧ (A.subalgebraContext hD).check b ∈ A.quotientConditions hD ∧
        (A.subalgebraContext hD).check c ∈ A.quotientConditions hD := by
  unfold quotientOrder
  rw [kpair_mem_restrictedOrder_iff, ← (A.subalgebraContext hD).check_kpair,
    (A.subalgebraContext hD).check_mem_iff]

include hD in
/-- Boolean conditions in the generic have projection in the trace generic. -/
theorem projection_mem_trace_of_mem {b : V} (hb : b ∈ booleanGeneric A.P A.R A.G) :
    subalgebraProjectionSet D b ∈
      traceGeneric (booleanGeneric A.P A.R A.G) (subalgebraConditions A.P A.R D) := by
  obtain ⟨hbB, p, hp, hpb⟩ := (mem_booleanGeneric_iff _ _ _ _).mp hb
  have hbP := booleanConditions_subset hbB
  refine ⟨(mem_booleanGeneric_iff _ _ _ _).mpr ⟨((mem_subalgebraConditions_iff _ _ _ _).mp
      (subalgebraProjectionSet_mem_conditions hD A.order hbB)).2,
    p, hp, subset_subalgebraProjectionSet hD hbP p hpb⟩, subalgebraProjectionSet_mem_conditions hD A.order hbB⟩

theorem check_mem_quotientGeneric_iff (b : V) :
    (A.subalgebraContext hD).check b ∈ A.quotientGeneric hD ↔ b ∈ booleanGeneric A.P A.R A.G := by
  constructor
  · rintro ⟨c, hc, he⟩
    rw [(A.subalgebraContext hD).check_eq_iff] at he
    rw [he]
    exact hc
  · intro hb
    exact ⟨b, hb, rfl⟩

theorem quotientTop : IsForcingTop (A.quotientConditions hD) (A.quotientOrder hD)
    ((A.subalgebraContext hD).check A.P) := by
  have hP : A.P ∈ booleanConditions A.P A.R := top_mem_booleanConditions ⟨A.one, A.top.1⟩
  obtain ⟨p₀, hp₀⟩ := A.generic.1.2.1
  have hPG : A.P ∈ booleanGeneric A.P A.R A.G :=
    (mem_booleanGeneric_iff _ _ _ _).mpr ⟨hP, p₀, hp₀, A.generic.1.1 p₀ hp₀⟩
  have htop : (A.subalgebraContext hD).check A.P ∈ A.quotientConditions hD :=
    (A.check_mem_quotientConditions_iff hD A.P).mpr ⟨hP, A.projection_mem_trace_of_mem hD hPG⟩
  refine ⟨htop, fun x hx ↦ ?_⟩
  obtain ⟨b, hbB, rfl⟩ := ((A.subalgebraContext hD).mem_check_iff _ _).mp
    (A.quotientConditions_subset hD x hx)
  exact (A.check_kpair_mem_quotientOrder_iff hD).mpr
    ⟨(kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hbB, hP, booleanConditions_subset hbB⟩, hx, htop⟩

theorem quotientGeneric_filter :
    IsExternalForcingFilter (A.quotientConditions hD) (A.quotientOrder hD) (A.quotientGeneric hD) := by
  have hGB := booleanGeneric_generic A.order A.generic
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨b, hb, rfl⟩
    exact (A.check_mem_quotientConditions_iff hD b).mpr ⟨hGB.1.1 b hb, A.projection_mem_trace_of_mem hD hb⟩
  · obtain ⟨b, hb⟩ := hGB.1.2.1
    exact ⟨_, b, hb, rfl⟩
  · rintro x ⟨b, hb, rfl⟩ y hy hxy
    obtain ⟨c, hcB, rfl⟩ := ((A.subalgebraContext hD).mem_check_iff _ _).mp
      (A.quotientConditions_subset hD y hy)
    obtain ⟨hbc, _, _⟩ := (A.check_kpair_mem_quotientOrder_iff hD).mp hxy
    exact ⟨c, hGB.1.2.2.1 b hb c hcB hbc, rfl⟩
  · rintro x ⟨b, hb, rfl⟩ y ⟨c, hc, rfl⟩
    obtain ⟨r, hr, hrb, hrc⟩ := hGB.1.2.2.2 b hb c hc
    have hrQ : (A.subalgebraContext hD).check r ∈ A.quotientConditions hD :=
      (A.check_mem_quotientConditions_iff hD r).mpr ⟨hGB.1.1 r hr, A.projection_mem_trace_of_mem hD hr⟩
    have hbQ : (A.subalgebraContext hD).check b ∈ A.quotientConditions hD :=
      (A.check_mem_quotientConditions_iff hD b).mpr ⟨hGB.1.1 b hb, A.projection_mem_trace_of_mem hD hb⟩
    have hcQ : (A.subalgebraContext hD).check c ∈ A.quotientConditions hD :=
      (A.check_mem_quotientConditions_iff hD c).mpr ⟨hGB.1.1 c hc, A.projection_mem_trace_of_mem hD hc⟩
    exact ⟨_, ⟨r, hr, rfl⟩, (A.check_kpair_mem_quotientOrder_iff hD).mpr ⟨hrb, hrQ, hbQ⟩,
      (A.check_kpair_mem_quotientOrder_iff hD).mpr ⟨hrc, hrQ, hcQ⟩⟩

/-- The Boolean generic meets every dense subset of the quotient lying in `V[G ∩ D]`. -/
theorem quotientGeneric_meets (D' : (A.subalgebraContext hD).Model)
    (hD' : ForcingDense (A.quotientConditions hD) (A.quotientOrder hD) D') :
    ∃ x ∈ A.quotientGeneric hD, x ∈ D' := by
  let C := A.subalgebraContext hD
  have hGB := booleanGeneric_generic A.order A.generic
  have hgen := hD.trace_generic A.order A.generic
  obtain ⟨Dname, rfl⟩ := C.ofName_surjective D'
  have hEB : (quotientWitnessSet A.P A.R D Dname.val) ⊆ booleanConditions A.P A.R :=
    fun b hb ↦ ((mem_quotientWitnessSet_iff _ _ _ _ _).mp hb).1
  have hF : ForcingDense (booleanConditions A.P A.R) (booleanOrder A.P A.R) (quotientDenseSet A.P A.R D Dname.val) := by
    refine ⟨fun b hb ↦ ((mem_quotientDenseSet_iff _ _ _ _ _).mp hb).elim (hEB b) (fun h ↦ h.1), fun b hb ↦ ?_⟩
    by_cases hex : ∃ b' ∈ (quotientWitnessSet A.P A.R D Dname.val), b' ⊆ b
    · obtain ⟨b', hb', hb'b⟩ := hex
      exact ⟨b', (mem_quotientDenseSet_iff _ _ _ _ _).mpr (Or.inl hb'),
        (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hEB b' hb', hb, hb'b⟩⟩
    · push Not at hex
      exact ⟨b, (mem_quotientDenseSet_iff _ _ _ _ _).mpr (Or.inr ⟨hb, hex⟩), (booleanOrder_poset _ _).1.2.1 b hb⟩
  obtain ⟨b₀, hb₀G, hb₀F⟩ := hGB.2 (quotientDenseSet A.P A.R D Dname.val) hF
  have hmem_of_forced : ∀ c ∈ booleanConditions A.P A.R, ∀ d ∈ traceGeneric (booleanGeneric A.P A.R A.G)
      (subalgebraConditions A.P A.R D), d ∈ atomicMembership (subalgebraConditions A.P A.R D)
        (restrictedOrder (booleanOrder A.P A.R) (subalgebraConditions A.P A.R D)) (checkName A.P c) Dname.val →
      C.check c ∈ C.ofName Dname := by
    intro c _ d hd hdM
    exact (forcingQuotientMk_mem_iff C.P C.R C.G C.order C.generic.1 ⟨checkName C.one c, checkName_isName C.top.1 c⟩ Dname).mpr
      ⟨d, hd, hdM⟩
  rcases (mem_quotientDenseSet_iff _ _ _ _ _).mp hb₀F with hE | hN
  · obtain ⟨hb₀B, c, hcB, hb₀c, d, hdD, hb₀d, _, hdM⟩ := (mem_quotientWitnessSet_iff _ _ _ _ _).mp hE
    have hcG : c ∈ booleanGeneric A.P A.R A.G :=
      hGB.1.2.2.1 b₀ hb₀G c hcB ((kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hb₀B, hcB, hb₀c⟩)
    have hdG : d ∈ traceGeneric (booleanGeneric A.P A.R A.G) (subalgebraConditions A.P A.R D) :=
      ⟨hGB.1.2.2.1 b₀ hb₀G d (subalgebraConditions_subset _ _ _ d hdD)
        ((kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hb₀B, subalgebraConditions_subset _ _ _ d hdD, hb₀d⟩), hdD⟩
    exact ⟨C.check c, ⟨c, hcG, rfl⟩, hmem_of_forced c hcB d hdG hdM⟩
  · exfalso
    obtain ⟨hb₀B, hnone⟩ := hN
    have hq : C.check b₀ ∈ A.quotientConditions hD :=
      (A.check_mem_quotientConditions_iff hD b₀).mpr ⟨hb₀B, A.projection_mem_trace_of_mem hD hb₀G⟩
    obtain ⟨c, hcD', hcq⟩ := hD'.2 _ hq
    have hcQ : c ∈ A.quotientConditions hD := hD'.1 c hcD'
    obtain ⟨c', hc'B, rfl⟩ := (C.mem_check_iff _ _).mp (A.quotientConditions_subset hD c hcQ)
    obtain ⟨_, hc'proj⟩ := (A.check_mem_quotientConditions_iff hD c').mp hcQ
    have hsub : c' ⊆ b₀ :=
      ((kpair_mem_booleanOrder_iff _ _ _ _).mp ((A.check_kpair_mem_quotientOrder_iff hD).mp hcq).1).2.2
    obtain ⟨d, hdG, hdM⟩ := (forcingQuotientMk_mem_iff C.P C.R C.G C.order C.generic.1
      ⟨checkName C.one c', checkName_isName C.top.1 c'⟩ Dname).mp hcD'
    obtain ⟨r, hrG, hrd, hrp⟩ := hgen.1.2.2.2 d hdG _ hc'proj
    have hrD := hrG.2
    obtain ⟨hrd', _, _⟩ := (kpair_mem_restrictedOrder_iff _ _ _ _).mp hrd
    obtain ⟨hrp', _, _⟩ := (kpair_mem_restrictedOrder_iff _ _ _ _).mp hrp
    have hrsub : r ⊆ subalgebraProjectionSet D c' := ((kpair_mem_booleanOrder_iff _ _ _ _).mp hrp').2.2
    have hrM : r ∈ atomicMembership (subalgebraConditions A.P A.R D)
        (restrictedOrder (booleanOrder A.P A.R) (subalgebraConditions A.P A.R D)) (checkName A.P c') Dname.val :=
      atomicMembership_mono C.order hdM hrD hrd
    have hrB := subalgebraConditions_subset _ _ _ r hrD
    obtain ⟨p, hp⟩ := subalgebraProjectionSet_meets hD A.order (booleanConditions_regular hc'B)
      ((mem_subalgebraConditions_iff _ _ _ _).mp hrD).1 hrsub (booleanConditions_nonempty hrB)
    have hb'B : c' ∩ r ∈ booleanConditions A.P A.R := inter_mem_booleanConditions hc'B hrB hp
    have hb'W : c' ∩ r ∈ quotientWitnessSet A.P A.R D Dname.val :=
      (mem_quotientWitnessSet_iff _ _ _ _ _).mpr ⟨hb'B, c', hc'B, fun x hx ↦ (mem_inter_iff.mp hx).1, r, hrD,
        fun x hx ↦ (mem_inter_iff.mp hx).2, hrsub, hrM⟩
    exact hnone _ hb'W (fun x hx ↦ hsub x (mem_inter_iff.mp hx).1)

/-- The quotient forcing over the intermediate extension, with the Boolean generic. -/
noncomputable def quotientContext : ForcingContext (A.subalgebraContext hD).Model where
  P := A.quotientConditions hD
  R := A.quotientOrder hD
  one := (A.subalgebraContext hD).check A.P
  G := A.quotientGeneric hD
  order := A.quotientOrder_preorder hD
  top := A.quotientTop hD
  generic := ⟨A.quotientGeneric_filter hD, A.quotientGeneric_meets hD⟩

end ForcingContext

end ZFVP
