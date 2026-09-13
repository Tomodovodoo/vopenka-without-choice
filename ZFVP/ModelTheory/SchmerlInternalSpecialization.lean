import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.FiniteNaturalSets
import ZFVP.ModelTheory.ForcingModel
import ZFVP.ModelTheory.ForcingQuotientGeneric
import ZFVP.SetTheory.EndExtensionCoding

/-! The corrected specialization poset as an actual set inside a ZF model.
Conditions are internally finite partial functions into the model's omega.
This construction does not identify internal finiteness with external finiteness.
-/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Comparable nodes assigned one color by a condition must coincide. -/
def InternallyStrict (S p : V) : Prop :=
  ∀ x y c, ⟨x, c⟩ₖ ∈ p → ⟨y, c⟩ₖ ∈ p → ⟨x, y⟩ₖ ∈ S → x = y

instance internallyStrict_definable : ℒₛₑₜ-relation[V] InternallyStrict := by
  unfold InternallyStrict
  definability

noncomputable def internalSpecialization (D S : V) : V :=
  {p ∈ finitePartialFunctions D (ω : V) ; InternallyStrict S p}

theorem mem_internalSpecialization (D S p : V) :
    p ∈ internalSpecialization D S ↔
      p ∈ finitePartialFunctions D (ω : V) ∧ InternallyStrict S p := by
  simp only [internalSpecialization, mem_sep_iff]

instance internalSpecialization_definable : ℒₛₑₜ-function₂[V] internalSpecialization := by
  have h : ℒₛₑₜ-relation₃[V] (fun P D S ↦ ∀ p,
      p ∈ P ↔ p ∈ finitePartialFunctions D (ω : V) ∧ InternallyStrict S p) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = internalSpecialization (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_internalSpecialization]

theorem empty_mem_internalSpecialization (D S : V) :
    (∅ : V) ∈ internalSpecialization D S :=
  (mem_internalSpecialization _ _ _).mpr
    ⟨empty_mem_finitePartialFunctions _ _, by simp [InternallyStrict]⟩

theorem internalSpecialization_poset (D S : V) :
    IsForcingPoset (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) :=
  reverseInclusionOrder_poset _

theorem internalSpecialization_top (D S : V) :
    IsForcingTop (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) ∅ := by
  refine ⟨empty_mem_internalSpecialization _ _, fun p hp ↦ ?_⟩
  exact (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hp, empty_mem_internalSpecialization _ _, by simp⟩

theorem internalSpecialization_subset {D S p q : V}
    (hp : p ∈ internalSpecialization D S) (hqp : q ⊆ p) :
    q ∈ internalSpecialization D S := by
  obtain ⟨hpfin, hpstrict⟩ := (mem_internalSpecialization _ _ _).mp hp
  exact (mem_internalSpecialization _ _ _).mpr
    ⟨finitePartialFunction_subset hpfin hqp,
      fun x y c hx hy hxy ↦ hpstrict x y c (hqp _ hx) (hqp _ hy) hxy⟩

theorem internalSpecialization_insert {D S p x c : V}
    (hp : p ∈ internalSpecialization D S) (hx : x ∈ D) (hc : c ∈ (ω : V))
    (hxd : x ∉ domain p) (hcr : c ∉ range p) :
    insert ⟨x, c⟩ₖ p ∈ internalSpecialization D S := by
  obtain ⟨hpfin, hpstrict⟩ := (mem_internalSpecialization _ _ _).mp hp
  refine (mem_internalSpecialization _ _ _).mpr
    ⟨finitePartialFunction_insert hpfin hx hc hxd, ?_⟩
  intro a b d ha hb hab
  rcases mem_insert.mp ha with ha | ha <;> rcases mem_insert.mp hb with hb | hb
  · exact ((kpair_iff.mp ha).1).trans (kpair_iff.mp hb).1.symm
  · exact False.elim (hcr ((kpair_iff.mp ha).2 ▸ mem_range_of_kpair_mem hb))
  · exact False.elim (hcr ((kpair_iff.mp hb).2 ▸ mem_range_of_kpair_mem ha))
  · exact hpstrict a b d ha hb hab

/-- The dense deciding set is itself an internal set, not an external family. -/
theorem internalSpecialization_domain_dense {D S x : V} (hx : x ∈ D) :
    ForcingDense (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S))
      {p ∈ internalSpecialization D S ; x ∈ domain p} := by
  classical
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  by_cases hxd : x ∈ domain p
  · exact ⟨p, mem_sep_iff.mpr ⟨hp, hxd⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hp, subset_refl _⟩⟩
  · have hpfin := (mem_internalSpecialization _ _ _).mp hp |>.1
    have hpf := (mem_finitePartialFunctions _ _ _).mp hpfin
    have : IsFunction p := hpf.2.1
    obtain ⟨c, hc, hcr⟩ := internallyFinite_fresh_natural
      (internallyFinite_range (internallyFinite_function hpf.2.2))
    have hq := internalSpecialization_insert hp hx hc hxd hcr
    refine ⟨insert ⟨x, c⟩ₖ p, mem_sep_iff.mpr ⟨hq, ?_⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr
        ⟨hq, hp, fun z hz ↦ mem_insert.mpr (Or.inr hz)⟩⟩
    exact mem_domain_of_kpair_mem
      (show ⟨x, c⟩ₖ ∈ insert ⟨x, c⟩ₖ p by simp)

/-- A generic for this concrete poset gives the repository's actual ZF quotient. -/
noncomputable abbrev internalSpecializationContext (D S : V) (G : Set V)
    (hG : IsExternalForcingGeneric (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) G) : ForcingContext V :=
  ⟨internalSpecialization D S, reverseInclusionOrder (internalSpecialization D S),
    ∅, G, (internalSpecialization_poset D S).1, internalSpecialization_top D S, hG⟩

noncomputable def internalSpecializationGeneric (D S : V) (G : Set V)
    (hG : IsExternalForcingGeneric (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) G) :
    (internalSpecializationContext D S G hG).Model :=
  (internalSpecializationContext D S G hG).ofName
    ⟨genericName (internalSpecialization D S) ∅,
      genericName_isName (empty_mem_internalSpecialization D S)⟩

theorem mem_internalSpecializationGeneric (D S : V) (G : Set V)
    (hG : IsExternalForcingGeneric (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) G)
    (z : (internalSpecializationContext D S G hG).Model) :
    z ∈ internalSpecializationGeneric D S G hG ↔
      ∃ p ∈ G, z = (internalSpecializationContext D S G hG).check p :=
  forcingGenericSet_mem_iff _ _ G (internalSpecialization_poset D S).1
    hG ∅ (internalSpecialization_top D S) z

/-- The union of the generic conditions is an actual element of the extension. -/
noncomputable def internalSpecializationColor (D S : V) (G : Set V)
    (hG : IsExternalForcingGeneric (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) G) :
    (internalSpecializationContext D S G hG).Model :=
  ⋃ˢ internalSpecializationGeneric D S G hG

theorem mem_internalSpecializationColor (D S : V) (G : Set V)
    (hG : IsExternalForcingGeneric (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) G)
    (z : (internalSpecializationContext D S G hG).Model) :
    z ∈ internalSpecializationColor D S G hG ↔
      ∃ p ∈ G, ∃ a ∈ p, z = (internalSpecializationContext D S G hG).check a := by
  rw [internalSpecializationColor, mem_sUnion_iff]
  constructor
  · rintro ⟨u, hu, hzu⟩
    obtain ⟨p, hpG, rfl⟩ := (mem_internalSpecializationGeneric D S G hG u).mp hu
    obtain ⟨a, ha, he⟩ := (internalSpecializationContext D S G hG).mem_check_iff p z |>.mp hzu
    exact ⟨p, hpG, a, ha, he⟩
  · rintro ⟨p, hpG, a, ha, rfl⟩
    refine ⟨(internalSpecializationContext D S G hG).check p, ?_, ?_⟩
    · exact (mem_internalSpecializationGeneric D S G hG _).mpr ⟨p, hpG, rfl⟩
    · exact ((internalSpecializationContext D S G hG).check_mem_iff a p).mpr ha

theorem pair_mem_internalSpecializationColor (D S : V) (G : Set V)
    (hG : IsExternalForcingGeneric (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) G)
    (x c : (internalSpecializationContext D S G hG).Model) :
    ⟨x, c⟩ₖ ∈ internalSpecializationColor D S G hG ↔
      ∃ a b : V, x = (internalSpecializationContext D S G hG).check a ∧
        c = (internalSpecializationContext D S G hG).check b ∧
        ∃ p ∈ G, ⟨a, b⟩ₖ ∈ p := by
  let A := internalSpecializationContext D S G hG
  constructor
  · intro hx
    obtain ⟨p, hpG, z, hz, he⟩ := (mem_internalSpecializationColor D S G hG _).mp hx
    have : IsFunction p := (mem_finitePartialFunctions _ _ _).mp
      ((mem_internalSpecialization _ _ _).mp (hG.1.1 p hpG)).1 |>.2.1
    obtain ⟨a, b, rfl⟩ := IsFunction.mem_eq_kpair hz
    have hpair : ⟨x, c⟩ₖ = ⟨A.check a, A.check b⟩ₖ :=
      he.trans (A.checkEmbedding.map_kpair a b)
    exact ⟨a, b, (kpair_iff.mp hpair).1, (kpair_iff.mp hpair).2, p, hpG, hz⟩
  · rintro ⟨a, b, rfl, rfl, p, hpG, hab⟩
    exact (mem_internalSpecializationColor D S G hG _).mpr
      ⟨p, hpG, ⟨a, b⟩ₖ, hab, (A.checkEmbedding.map_kpair a b).symm⟩

/-- The actual generic union is total and strictly specializes the checked relation. -/
theorem internalSpecializationColor_spec (D S : V) (G : Set V)
    (hG : IsExternalForcingGeneric (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) G) :
    let A := internalSpecializationContext D S G hG
    internalSpecializationColor D S G hG ∈ A.check (ω : V) ^ A.check D ∧
      InternallyStrict (A.check S) (internalSpecializationColor D S G hG) := by
  let A := internalSpecializationContext D S G hG
  have hfun (p : V) (hp : p ∈ G) : IsFunction p :=
    (mem_finitePartialFunctions _ _ _).mp
      ((mem_internalSpecialization _ _ _).mp (hG.1.1 p hp)).1 |>.2.1
  have hcompat (a b c : V) (p q : V) (hp : p ∈ G) (hq : q ∈ G)
      (hab : ⟨a, b⟩ₖ ∈ p) (hac : ⟨a, c⟩ₖ ∈ q) : b = c := by
    obtain ⟨r, hrG, hrp, hrq⟩ := hG.1.2.2.2 p hp q hq
    have : IsFunction r := hfun r hrG
    exact IsFunction.unique
      (((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2 _ hab)
      (((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2 _ hac)
  refine ⟨mem_function_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨p, hpG, a, ha, rfl⟩ := (mem_internalSpecializationColor D S G hG z).mp hz
    have : IsFunction p := hfun p hpG
    obtain ⟨x, c, rfl⟩ := IsFunction.mem_eq_kpair ha
    have hpc := (mem_finitePartialFunctions _ _ _).mp
      ((mem_internalSpecialization _ _ _).mp (hG.1.1 p hpG)).1 |>.1
    obtain ⟨hx, hc⟩ := kpair_mem_iff.mp (hpc _ ha)
    have he : A.check ⟨x, c⟩ₖ = ⟨A.check x, A.check c⟩ₖ :=
      A.checkEmbedding.map_kpair x c
    change A.check ⟨x, c⟩ₖ ∈ A.check D ×ˢ A.check (ω : V)
    rw [he]
    exact kpair_mem_iff.mpr
      ⟨(A.check_mem_iff _ _).mpr hx, (A.check_mem_iff _ _).mpr hc⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (A.mem_check_iff D x).mp hx
    obtain ⟨p, hpG, hpdec⟩ := hG.2 _ (internalSpecialization_domain_dense (S := S) ha)
    obtain ⟨c, hac⟩ := mem_domain_iff.mp (mem_sep_iff.mp hpdec).2
    refine ⟨A.check c,
      (pair_mem_internalSpecializationColor D S G hG _ _).mpr
        ⟨a, c, rfl, rfl, p, hpG, hac⟩, ?_⟩
    intro y hy
    obtain ⟨b, d, he, rfl, q, hqG, hbd⟩ :=
      (pair_mem_internalSpecializationColor D S G hG _ _).mp hy
    have hab := (A.check_eq_iff a b).mp he
    subst b
    exact congrArg A.check (hcompat a d c q p hqG hpG hbd hac)
  · intro x y c hx hy hxy
    obtain ⟨a, b, rfl, rfl, p, hpG, hab⟩ :=
      (pair_mem_internalSpecializationColor D S G hG _ _).mp hx
    obtain ⟨d, e, rfl, hbe, q, hqG, hde⟩ :=
      (pair_mem_internalSpecializationColor D S G hG _ _).mp hy
    have hbe' := (A.check_eq_iff b e).mp hbe
    subst e
    have he : A.check ⟨a, d⟩ₖ = ⟨A.check a, A.check d⟩ₖ :=
      A.checkEmbedding.map_kpair a d
    have had : ⟨a, d⟩ₖ ∈ S := (A.check_mem_iff _ _).mp (he.symm ▸ hxy)
    obtain ⟨r, hrG, hrp, hrq⟩ := hG.1.2.2.2 p hpG q hqG
    have hstrict := (mem_internalSpecialization _ _ _).mp (hG.1.1 r hrG) |>.2
    exact congrArg A.check (hstrict a d b
      (((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2 _ hab)
      (((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2 _ hde) had)

/-- Existence of this forcing extension for any countable, possibly ill-founded,
ground model. The coloring's codomain is the internal omega of the extension. -/
theorem exists_internalSpecialization_extension [Countable V] (D S : V) :
    ∃ G : Set V, ∃ hG : IsExternalForcingGeneric (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) G,
      let A := internalSpecializationContext D S G hG
      ∃ f : A.Model, f ∈ (ω : A.Model) ^ A.check D ∧ InternallyStrict (A.check S) f := by
  obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric
    (internalSpecialization_poset D S).1 (empty_mem_internalSpecialization D S)
  refine ⟨G, hG, internalSpecializationColor D S G hG, ?_⟩
  have h := internalSpecializationColor_spec D S G hG
  have he : (internalSpecializationContext D S G hG).check (ω : V) = ω :=
    (internalSpecializationContext D S G hG).checkEmbedding.map_omega
  simpa only [he] using h

end ZFVP.Schmerl
