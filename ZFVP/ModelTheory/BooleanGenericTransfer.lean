import ZFVP.SetTheory.BooleanCompletion
import ZFVP.ModelTheory.ForcingModelGeneric
import ZFVP.ModelTheory.ForcingRealizationGeneration
import ZFVP.ModelTheory.ForcingModelChecks

/-! Forcing with a poset and with its Boolean completion give the same extension: a generic
filter `G` induces the generic `H` of regular sets met by `G`, conditions are recovered from
`H` through their regular cones, and the two extensions realize each other, so they are
isomorphic membership structures over the same ground. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The regular sets met by a generic filter. -/
def booleanGeneric (P R : V) (G : Set V) : Set V :=
  {C | C ∈ booleanConditions P R ∧ ∃ p ∈ G, p ∈ C}

/-- A condition whose regular cone is met by the generic belongs to it. -/
theorem mem_of_meets_coneRegular {P R : V} {G : Set V} (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) {p q : V} (hp : p ∈ P) (hq : q ∈ G)
    (hqc : q ∈ coneRegular P R p) : p ∈ G := by
  have hE : ForcingDense P R {r ∈ P ; ⟨r, p⟩ₖ ∈ R ∨ ¬ForcingCompatible P R r q} := by
    refine ⟨sep_subset, fun r hr ↦ ?_⟩
    by_cases hc : ForcingCompatible P R r q
    · obtain ⟨t, ht, htr, htq⟩ := hc
      obtain ⟨_, hh⟩ := mem_coneRegular_iff.mp hqc
      obtain ⟨s, hs, hsp, hst⟩ := hh t ht htq
      exact ⟨s, mem_sep_iff.mpr ⟨hs, Or.inl hsp⟩, hR.2.2 s hs t ht r hr hst htr⟩
    · exact ⟨r, mem_sep_iff.mpr ⟨hr, Or.inr hc⟩, hR.2.1 r hr⟩
  obtain ⟨r, hrG, hrE⟩ := hG.2 _ hE
  obtain ⟨_, h | h⟩ := mem_sep_iff.mp hrE
  · exact hG.1.2.2.1 r hrG p hp h
  · exact (h (externalForcingFilter_compatible hG.1 hrG hq)).elim

theorem coneRegular_mem_booleanGeneric_iff {P R : V} {G : Set V} (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) {p : V} (hp : p ∈ P) :
    coneRegular P R p ∈ booleanGeneric P R G ↔ p ∈ G := by
  constructor
  · rintro ⟨_, q, hq, hqc⟩
    exact mem_of_meets_coneRegular hR hG hp hq hqc
  · intro hpG
    exact ⟨coneRegular_mem_booleanConditions hR hp, p, hpG, self_mem_coneRegular hR hp⟩

theorem booleanGeneric_generic {P R : V} {G : Set V} (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) :
    IsExternalForcingGeneric (booleanConditions P R) (booleanOrder P R) (booleanGeneric P R G) := by
  refine ⟨⟨fun C hC ↦ hC.1, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨p, hp⟩ := hG.1.2.1
    exact ⟨P, top_mem_booleanConditions ⟨p, hG.1.1 p hp⟩, p, hp, hG.1.1 p hp⟩
  · rintro C ⟨_, p, hp, hpC⟩ D hD hCD
    exact ⟨hD, p, hp, ((kpair_mem_booleanOrder_iff P R C D).mp hCD).2.2 _ hpC⟩
  · rintro C ⟨hC, p, hp, hpC⟩ D ⟨hD, q, hq, hqD⟩
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hp q hq
    have hCreg := ((mem_booleanConditions_iff P R C).mp hC).1
    have hDreg := ((mem_booleanConditions_iff P R D).mp hD).1
    have hrC : r ∈ C := hCreg.2.1 p hpC r (hG.1.1 r hr) hrp
    have hrD : r ∈ D := hDreg.2.1 q hqD r (hG.1.1 r hr) hrq
    have hCD : C ∩ D ∈ booleanConditions P R := (mem_booleanConditions_iff P R _).mpr
      ⟨forcingRegular_inter hCreg hDreg, r, mem_inter_iff.mpr ⟨hrC, hrD⟩⟩
    exact ⟨C ∩ D, ⟨hCD, r, hr, mem_inter_iff.mpr ⟨hrC, hrD⟩⟩,
      (kpair_mem_booleanOrder_iff P R _ C).mpr ⟨hCD, hC, fun z hz ↦ (mem_inter_iff.mp hz).1⟩,
      (kpair_mem_booleanOrder_iff P R _ D).mpr ⟨hCD, hD, fun z hz ↦ (mem_inter_iff.mp hz).2⟩⟩
  · intro D hD
    have hE : ForcingDense P R {p ∈ P ; ∃ C ∈ D, p ∈ C} := by
      refine ⟨sep_subset, fun p hp ↦ ?_⟩
      obtain ⟨C, hCD, hCle⟩ := hD.2 _ (coneRegular_mem_booleanConditions hR hp)
      obtain ⟨hC, _, hCsub⟩ := (kpair_mem_booleanOrder_iff P R C _).mp hCle
      obtain ⟨hCreg, a, haC⟩ := (mem_booleanConditions_iff P R C).mp hC
      have haP : a ∈ P := hCreg.1 a haC
      obtain ⟨_, hh⟩ := mem_coneRegular_iff.mp (hCsub a haC)
      obtain ⟨s, hs, hsp, hsa⟩ := hh a haP (hR.2.1 a haP)
      have hsC : s ∈ C := hCreg.2.1 a haC s hs hsa
      exact ⟨s, mem_sep_iff.mpr ⟨hs, C, hCD, hsC⟩, hsp⟩
    obtain ⟨p, hpG, hpE⟩ := hG.2 _ hE
    obtain ⟨_, C, hCD, hpC⟩ := mem_sep_iff.mp hpE
    exact ⟨C, ⟨hD.1 C hCD, p, hpG, hpC⟩, hCD⟩

namespace ForcingContext

/-- The Boolean completion context of a forcing context. -/
noncomputable def booleanContext (A : ForcingContext V) : ForcingContext V where
  P := booleanConditions A.P A.R
  R := booleanOrder A.P A.R
  one := A.P
  G := booleanGeneric A.P A.R A.G
  order := (booleanOrder_poset _ _).1
  top := booleanOrder_top ⟨A.one, A.top.1⟩
  generic := booleanGeneric_generic A.order A.generic

/-- The Boolean extension realized inside the poset extension. -/
noncomputable def booleanRealization (A : ForcingContext V) :
    ForcingRealization A.booleanContext A.Model where
  ground := A.checkEmbedding
  genericSet := {C ∈ A.check (booleanConditions A.P A.R) ; ∃ p ∈ A.genericSet, p ∈ C}
  generic_subset := fun x hx ↦ (mem_sep_iff.mp hx).1
  generic_mem := fun C ↦ by
    change A.check C ∈ _ ↔ C ∈ booleanGeneric A.P A.R A.G
    rw [mem_sep_iff, A.check_mem_iff]
    constructor
    · rintro ⟨hC, p', hp', hpC⟩
      obtain ⟨p, hp, rfl⟩ := (A.mem_genericSet_iff p').mp hp'
      exact ⟨hC, p, hp, (A.check_mem_iff p C).mp hpC⟩
    · rintro ⟨hC, p, hp, hpC⟩
      exact ⟨hC, A.check p, (A.mem_genericSet_iff _).mpr ⟨p, hp, rfl⟩, (A.check_mem_iff p C).mpr hpC⟩

/-- The conditions recovered from the Boolean generic inside the Boolean extension. -/
noncomputable def recoveredGeneric (A : ForcingContext V) : A.booleanContext.Model :=
  {x ∈ A.booleanContext.check A.P ; ∃ C ∈ A.booleanContext.genericSet,
    ∀ y ∈ C, ∀ z ∈ A.booleanContext.check A.P, ⟨z, y⟩ₖ ∈ A.booleanContext.check A.R →
      ∃ w ∈ A.booleanContext.check A.P, ⟨w, z⟩ₖ ∈ A.booleanContext.check A.R ∧
        ⟨w, x⟩ₖ ∈ A.booleanContext.check A.R}

/-- The cone condition transported through checks. -/
theorem recovered_condition_iff (A : ForcingContext V) (C p : V) :
    (∀ y ∈ A.booleanContext.check C, ∀ z ∈ A.booleanContext.check A.P,
      ⟨z, y⟩ₖ ∈ A.booleanContext.check A.R →
      ∃ w ∈ A.booleanContext.check A.P, ⟨w, z⟩ₖ ∈ A.booleanContext.check A.R ∧
        ⟨w, A.booleanContext.check p⟩ₖ ∈ A.booleanContext.check A.R) ↔
    (∀ y ∈ C, ∀ z ∈ A.P, ⟨z, y⟩ₖ ∈ A.R → ∃ w ∈ A.P, ⟨w, z⟩ₖ ∈ A.R ∧ ⟨w, p⟩ₖ ∈ A.R) := by
  let B := A.booleanContext
  constructor
  · intro h y hy z hz hzy
    have h' := h (B.check y) ((B.check_mem_iff y C).mpr hy) (B.check z) ((B.check_mem_iff z A.P).mpr hz)
      (by rw [← B.check_kpair, B.check_mem_iff]; exact hzy)
    obtain ⟨w', hw', hwz, hwp⟩ := h'
    obtain ⟨w, hw, rfl⟩ := (B.mem_check_iff A.P w').mp hw'
    rw [← B.check_kpair, B.check_mem_iff] at hwz hwp
    exact ⟨w, hw, hwz, hwp⟩
  · intro h y' hy' z' hz' hzy
    obtain ⟨y, hy, rfl⟩ := (B.mem_check_iff C y').mp hy'
    obtain ⟨z, hz, rfl⟩ := (B.mem_check_iff A.P z').mp hz'
    rw [← B.check_kpair, B.check_mem_iff] at hzy
    obtain ⟨w, hw, hwz, hwp⟩ := h y hy z hz hzy
    refine ⟨B.check w, (B.check_mem_iff w A.P).mpr hw, ?_, ?_⟩
    · rw [← B.check_kpair, B.check_mem_iff]; exact hwz
    · rw [← B.check_kpair, B.check_mem_iff]; exact hwp

theorem check_mem_recoveredGeneric_iff (A : ForcingContext V) (p : V) :
    A.booleanContext.check p ∈ A.recoveredGeneric ↔ p ∈ A.G := by
  let B := A.booleanContext
  have hR := A.order
  unfold recoveredGeneric
  rw [mem_sep_iff, B.check_mem_iff]
  constructor
  · rintro ⟨hp, C', hC', hcond⟩
    obtain ⟨C, hC, rfl⟩ := (B.mem_genericSet_iff C').mp hC'
    obtain ⟨hCB, q, hq, hqC⟩ := hC
    have hcond' := (A.recovered_condition_iff C p).mp hcond
    have hqc : q ∈ coneRegular A.P A.R p := by
      rw [mem_coneRegular_iff]
      refine ⟨A.generic.1.1 q hq, fun r hr hrq ↦ ?_⟩
      obtain ⟨w, hw, hwr, hwp⟩ := hcond' q hqC r hr hrq
      exact ⟨w, hw, hwp, hwr⟩
    exact mem_of_meets_coneRegular hR A.generic hp hq hqc
  · intro hpG
    have hp : p ∈ A.P := A.generic.1.1 p hpG
    refine ⟨hp, B.check (coneRegular A.P A.R p), (B.mem_genericSet_iff _).mpr
      ⟨_, (coneRegular_mem_booleanGeneric_iff hR A.generic hp).mpr hpG, rfl⟩, ?_⟩
    apply (A.recovered_condition_iff _ p).mpr
    intro y hy z hz hzy
    obtain ⟨_, hh⟩ := mem_coneRegular_iff.mp hy
    obtain ⟨w, hw, hwp, hwz⟩ := hh z hz hzy
    exact ⟨w, hw, hwz, hwp⟩

/-- The poset extension realized inside the Boolean extension. -/
noncomputable def recoveredRealization (A : ForcingContext V) :
    ForcingRealization A A.booleanContext.Model where
  ground := A.booleanContext.checkEmbedding
  genericSet := A.recoveredGeneric
  generic_subset := fun x hx ↦ (mem_sep_iff.mp hx).1
  generic_mem := A.check_mem_recoveredGeneric_iff

theorem booleanRealization_value_recovered (A : ForcingContext V) :
    A.booleanRealization.value A.recoveredGeneric = A.genericSet := by
  let L := A.booleanRealization
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := L.value_endExtension _ hz
    have hxP : x ∈ A.booleanContext.check A.P := (mem_sep_iff.mp hx).1
    obtain ⟨p, _, rfl⟩ := (A.booleanContext.mem_check_iff A.P x).mp hxP
    have hpG : p ∈ A.G := (A.check_mem_recoveredGeneric_iff p).mp hx
    rw [L.value_check]
    exact (A.check_mem_genericSet_iff p).mpr hpG
  · intro hz
    obtain ⟨p, hp, rfl⟩ := (A.mem_genericSet_iff z).mp hz
    have hx : A.booleanContext.check p ∈ A.recoveredGeneric := (A.check_mem_recoveredGeneric_iff p).mpr hp
    have := (L.value_mem_iff _ _).mpr hx
    rwa [L.value_check] at this

theorem recoveredRealization_value_boolean (A : ForcingContext V) :
    A.recoveredRealization.value A.booleanRealization.genericSet = A.booleanContext.genericSet := by
  let L := A.recoveredRealization
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := L.value_endExtension _ hz
    have hxP : x ∈ A.check (booleanConditions A.P A.R) := A.booleanRealization.generic_subset x hx
    obtain ⟨C, _, rfl⟩ := (A.mem_check_iff _ x).mp hxP
    have hC : C ∈ booleanGeneric A.P A.R A.G := (A.booleanRealization.generic_mem C).mp hx
    rw [L.value_check]
    exact (A.booleanContext.check_mem_genericSet_iff C).mpr hC
  · intro hz
    obtain ⟨C, hC, rfl⟩ := (A.booleanContext.mem_genericSet_iff z).mp hz
    have hx : A.check C ∈ A.booleanRealization.genericSet := (A.booleanRealization.generic_mem C).mpr hC
    have := (L.value_mem_iff _ _).mpr hx
    rwa [L.value_check] at this

theorem booleanRealization_surjective (A : ForcingContext V) :
    Function.Surjective A.booleanRealization.value :=
  ForcingRealization.value_surjective_of_generators A A.booleanRealization
    (fun x ↦ ⟨A.booleanContext.check x, A.booleanRealization.value_check x⟩)
    ⟨A.recoveredGeneric, A.booleanRealization_value_recovered⟩

theorem recoveredRealization_surjective (A : ForcingContext V) :
    Function.Surjective A.recoveredRealization.value :=
  ForcingRealization.value_surjective_of_generators A.booleanContext A.recoveredRealization
    (fun x ↦ ⟨A.check x, A.recoveredRealization.value_check x⟩)
    ⟨A.booleanRealization.genericSet, A.recoveredRealization_value_boolean⟩

/-- The poset extension and the Boolean extension are isomorphic membership structures. -/
noncomputable def booleanEquiv (A : ForcingContext V) : A.Model ≃ A.booleanContext.Model :=
  Equiv.ofBijective A.recoveredRealization.value
    ⟨A.recoveredRealization.value_injective, A.recoveredRealization_surjective⟩

theorem booleanEquiv_mem_iff (A : ForcingContext V) (x y : A.Model) :
    A.booleanEquiv x ∈ A.booleanEquiv y ↔ x ∈ y :=
  A.recoveredRealization.value_mem_iff x y

theorem booleanEquiv_check (A : ForcingContext V) (x : V) :
    A.booleanEquiv (A.check x) = A.booleanContext.check x :=
  A.recoveredRealization.value_check x

end ForcingContext
end ZFVP
