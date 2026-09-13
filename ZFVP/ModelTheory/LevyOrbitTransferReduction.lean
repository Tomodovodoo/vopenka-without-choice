import ZFVP.ModelTheory.BooleanGenericAutomorphism
import ZFVP.ModelTheory.LevyConeIsomorphism

/-! The transfer statement of Karagila and Schilhan, Lemma 9.3, reduced to the cone form of
Jech, Set Theory (3rd ed.), Lemma 25.5.

`ForcingContext.OrbitTransfer` asks, for every filter `H` of the extension satisfying the orbit
clauses, for a ground automorphism of the Boolean completion lying in the forced stabilizer of the
support and carrying the generic onto `H`. Jech's lemma does not produce that automorphism
directly. It produces two conditions `p0` and `q0`, `p0` in the generic and `q0` in `H`, and an
isomorphism of the cone below `p0` with the cone below `q0` that carries the generic below `p0` to
`H` below `q0`, together with an isomorphism of the complementary cones.

This module closes the gap between the two forms in two steps.

* `orbitTransfer_of_cone_automorphism` takes the automorphism together with the two conditions and
  the pointwise statement only below `p0`, and gets `OrbitTransfer`. The argument is upward
  closure on both sides: a condition `b` lies in the generic exactly when `b ∩ p0` does, its image
  lies in `H` exactly when the image meets `q0`, and the automorphism sends `b ∩ p0` to
  `Θ b ∩ q0`.

* `orbitTransfer_of_coneOrbitTransfer` replaces the automorphism by the two cone isomorphisms and
  builds it with `exists_forcedStabilizer_automorphism_of_cone_isomorphisms`.

The cone hypothesis is `ForcingContext.ConeOrbitTransfer`. `solovay_corollary_of_cone_transfer`
is the paper's `cor:Solovay` with that hypothesis in place of the transfer statement. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Automorphisms of the Boolean completion and intersections -/

/-- An automorphism of the Boolean completion is monotone: the order is inclusion. -/
theorem boolAutomorphism_value_mono {P R Θ a b : V}
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    (ha : a ∈ booleanConditions P R) (hb : b ∈ booleanConditions P R) (hab : a ⊆ b) :
    Θ ‘ a ⊆ Θ ‘ b :=
  ((kpair_mem_booleanOrder_iff _ _ _ _).mp
    ((hΘ.2.2.2 a ha b hb).mp ((kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨ha, hb, hab⟩))).2.2

/-- A condition below the image of `a` has its preimage below `a`. -/
theorem boolAutomorphism_inverse_value_subset {P R Θ a d : V}
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    (ha : a ∈ booleanConditions P R) (hd : d ∈ booleanConditions P R) (hda : d ⊆ Θ ‘ a) :
    (converseGraph Θ) ‘ d ⊆ a := by
  have hΘa : Θ ‘ a ∈ booleanConditions P R := function_value_mem hΘ.1 ha
  have hinv := forcingAutomorphism_inverse hΘ
  have h := boolAutomorphism_value_mono hinv hd hΘa hda
  rwa [converseGraph_value_value hΘ.1 hΘ.2.1 ha] at h

/-- An automorphism of the Boolean completion preserves an intersection of two conditions when
that intersection is again a condition. -/
theorem boolAutomorphism_value_inter {P R Θ a b : V}
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    (ha : a ∈ booleanConditions P R) (hb : b ∈ booleanConditions P R)
    (hab : a ∩ b ∈ booleanConditions P R) : Θ ‘ (a ∩ b) = Θ ‘ a ∩ Θ ‘ b := by
  apply SetTheory.subset_antisymm
  · intro z hz
    exact mem_inter_iff.mpr
      ⟨boolAutomorphism_value_mono hΘ hab ha (fun w hw ↦ (mem_inter_iff.mp hw).1) z hz,
        boolAutomorphism_value_mono hΘ hab hb (fun w hw ↦ (mem_inter_iff.mp hw).2) z hz⟩
  · intro z hz
    have hd : Θ ‘ a ∩ Θ ‘ b ∈ booleanConditions P R :=
      inter_mem_booleanConditions (function_value_mem hΘ.1 ha) (function_value_mem hΘ.1 hb) hz
    have hinv := forcingAutomorphism_inverse hΘ
    have hpre : (converseGraph Θ) ‘ (Θ ‘ a ∩ Θ ‘ b) ⊆ a ∩ b := by
      intro w hw
      exact mem_inter_iff.mpr
        ⟨boolAutomorphism_inverse_value_subset hΘ ha hd (fun y hy ↦ (mem_inter_iff.mp hy).1) w hw,
          boolAutomorphism_inverse_value_subset hΘ hb hd (fun y hy ↦ (mem_inter_iff.mp hy).2) w hw⟩
    have hmem : (converseGraph Θ) ‘ (Θ ‘ a ∩ Θ ‘ b) ∈ booleanConditions P R :=
      function_value_mem hinv.1 hd
    have h := boolAutomorphism_value_mono hΘ hmem hab hpre
    have hrange : Θ ‘ a ∩ Θ ‘ b ∈ range Θ := hΘ.2.2.1.symm ▸ hd
    rw [value_converseGraph_value hΘ.1 hΘ.2.1 hrange] at h
    exact h z hz

/-- An automorphism of the Boolean completion sends disjoint conditions to disjoint ones. -/
theorem boolAutomorphism_value_inter_empty {P R Θ a b : V}
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    (ha : a ∈ booleanConditions P R) (hb : b ∈ booleanConditions P R)
    (hab : a ∩ b = (∅ : V)) : Θ ‘ a ∩ Θ ‘ b = (∅ : V) := by
  apply mem_ext
  intro z
  simp only [not_mem_empty, iff_false]
  intro hz
  have hd : Θ ‘ a ∩ Θ ‘ b ∈ booleanConditions P R :=
    inter_mem_booleanConditions (function_value_mem hΘ.1 ha) (function_value_mem hΘ.1 hb) hz
  have hinv := forcingAutomorphism_inverse hΘ
  have hmem : (converseGraph Θ) ‘ (Θ ‘ a ∩ Θ ‘ b) ∈ booleanConditions P R :=
    function_value_mem hinv.1 hd
  obtain ⟨-, w, hw⟩ := (mem_booleanConditions_iff _ _ _).mp hmem
  have hwa : w ∈ a :=
    boolAutomorphism_inverse_value_subset hΘ ha hd (fun y hy ↦ (mem_inter_iff.mp hy).1) w hw
  have hwb : w ∈ b :=
    boolAutomorphism_inverse_value_subset hΘ hb hd (fun y hy ↦ (mem_inter_iff.mp hy).2) w hw
  have : w ∈ a ∩ b := mem_inter_iff.mpr ⟨hwa, hwb⟩
  rw [hab] at this
  exact not_mem_empty this

/-- A cone isomorphism sends the top of its source cone to the top of its target cone. -/
theorem coneIsomorphism_value_top {P R b0 c0 f : V} (hb0 : b0 ∈ booleanConditions P R)
    (hc0 : c0 ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (forcingCone (booleanConditions P R) (booleanOrder P R) b0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b0))
      (forcingCone (booleanConditions P R) (booleanOrder P R) c0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) c0)) f) :
    f ‘ b0 = c0 := by
  have hb0c : b0 ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b0 :=
    (mem_forcingCone_iff _ _ _ _).mpr
      ⟨hb0, (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hb0, hb0, subset_refl _⟩⟩
  have hc0c : c0 ∈ forcingCone (booleanConditions P R) (booleanOrder P R) c0 :=
    (mem_forcingCone_iff _ _ _ _).mpr
      ⟨hc0, (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hc0, hc0, subset_refl _⟩⟩
  apply SetTheory.subset_antisymm
  · have hfb := function_value_mem hf.1 hb0c
    exact ((kpair_mem_booleanOrder_iff _ _ _ _).mp
      ((mem_forcingCone_iff _ _ _ _).mp hfb).2).2.2
  · obtain ⟨x, hx, hxc⟩ := isForcingIsomorphism_surjective hf c0 hc0c
    have hxb0 : x ⊆ b0 :=
      ((kpair_mem_booleanOrder_iff _ _ _ _).mp ((mem_forcingCone_iff _ _ _ _).mp hx).2).2.2
    have := coneIsomorphism_mono hf hx hb0c hxb0
    rwa [hxc] at this

namespace ForcingContext

/-! ### From the cone data with an automorphism -/

variable (A : ForcingContext V)

/-- Checks of conditions are checked regular sets. -/
theorem check_mem_check_regularSets {d : V} (hd : d ∈ booleanConditions A.P A.R) :
    A.check d ∈ A.check (regularSets A.P A.R) :=
  (A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr (booleanConditions_regular hd))

/-- The transfer statement from cone data with the automorphism already built, in the form in
which the lifting lemma delivers it: the image of `p0` need only contain `q0`. -/
theorem orbitTransfer_of_cone_automorphism_subset (Pf : SetTheorySemisentence 2) (s k : V)
    (p : A.Model)
    (h : ∀ H : A.Model, IsOrbitFilter Pf (A.check (regularSets A.P A.R))
        (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
        (A.orbitSupportReal s k) p H →
      ∃ p0 ∈ booleanConditions A.P A.R, ∃ q0 ∈ booleanConditions A.P A.R,
        ∃ Θ ∈ forcedStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R)) (range s),
        (∃ r ∈ A.G, r ∈ p0) ∧ A.check q0 ∈ H ∧ q0 ⊆ Θ ‘ p0 ∧
          ∀ b ∈ booleanConditions A.P A.R, b ⊆ p0 →
            (A.check (Θ ‘ b) ∈ H ↔ A.check b ∈ A.boolGenericSet)) :
    A.OrbitTransfer Pf s k p := by
  rw [A.orbitTransfer_iff_pointwise]
  intro H hH
  obtain ⟨p0, hp0, q0, hq0, Θ, hΘE, hmeet, hq0H, hq0Θ, hpt⟩ := h H hH
  have hΘ : IsForcingAutomorphism (booleanConditions A.P A.R) (booleanOrder A.P A.R) Θ :=
    (mem_forcingAutomorphisms_iff _ _ _).mp (mem_sep_iff.mp hΘE).1
  have hgen := A.boolGenericSet_antichainGeneric
  have hp0G : A.check p0 ∈ A.boolGenericSet :=
    (A.check_mem_boolGenericSet_iff p0).mpr
      ⟨(mem_regularSets_iff _ _ _).mpr (booleanConditions_regular hp0), hmeet⟩
  refine ⟨Θ, hΘE, fun b hb ↦ ?_⟩
  by_cases hne : ∃ z, z ∈ b ∩ p0
  · obtain ⟨z0, hz0⟩ := hne
    have hbp : b ∩ p0 ∈ booleanConditions A.P A.R := inter_mem_booleanConditions hb hp0 hz0
    have hsubp : b ∩ p0 ⊆ p0 := fun z hz ↦ (mem_inter_iff.mp hz).2
    have hsubb : b ∩ p0 ⊆ b := fun z hz ↦ (mem_inter_iff.mp hz).1
    have hkey := hpt (b ∩ p0) hbp hsubp
    have hgeneric : A.check (b ∩ p0) ∈ A.boolGenericSet ↔ A.check b ∈ A.boolGenericSet := by
      constructor
      · intro hmem
        exact hgen.upward _ hmem _ (A.check_mem_check_regularSets hb)
          ((A.checkEmbedding.subset_iff _ _).mpr hsubb)
      · intro hmem
        rw [A.check_inter]
        exact hgen.inter _ hmem _ hp0G
    have hval : Θ ‘ (b ∩ p0) = Θ ‘ b ∩ Θ ‘ p0 := boolAutomorphism_value_inter hΘ hb hp0 hbp
    have hfilter : A.check (Θ ‘ (b ∩ p0)) ∈ H ↔ A.check (Θ ‘ b) ∈ H := by
      constructor
      · intro hmem
        refine hH.2.1 _ hmem _ (A.check_mem_check_regularSets (function_value_mem hΘ.1 hb)) ?_
        exact (A.checkEmbedding.subset_iff _ _).mpr
          (boolAutomorphism_value_mono hΘ hbp hb hsubb)
      · intro hmem
        have hinter : A.check (Θ ‘ b) ∩ A.check q0 ∈ H := hH.2.2.1 _ hmem _ hq0H
        rw [← A.check_inter] at hinter
        refine hH.2.1 _ hinter _
          (A.check_mem_check_regularSets (function_value_mem hΘ.1 hbp)) ?_
        refine (A.checkEmbedding.subset_iff _ _).mpr ?_
        rw [hval]
        intro z hz
        exact mem_inter_iff.mpr
          ⟨(mem_inter_iff.mp hz).1, hq0Θ z (mem_inter_iff.mp hz).2⟩
    rw [← hfilter, ← hgeneric]
    exact hkey
  · have h0 : b ∩ p0 = (∅ : V) :=
      mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hne, fun hz ↦ absurd hz not_mem_empty⟩)
    have hbG : A.check b ∉ A.boolGenericSet := by
      intro hmem
      have hi := hgen.inter _ hmem _ hp0G
      rw [← A.check_inter, h0] at hi
      obtain ⟨-, r, -, hr⟩ := (A.check_mem_boolGenericSet_iff _).mp hi
      exact not_mem_empty hr
    have hΘbH : A.check (Θ ‘ b) ∉ H := by
      intro hmem
      have hi : A.check (Θ ‘ b) ∩ A.check q0 ∈ H := hH.2.2.1 _ hmem _ hq0H
      rw [← A.check_inter] at hi
      obtain ⟨z, hz⟩ := hH.2.2.2.1 _ hi
      obtain ⟨z0, hz0, -⟩ := (A.mem_check_iff _ _).mp hz
      have hmem2 : z0 ∈ Θ ‘ b ∩ Θ ‘ p0 :=
        mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz0).1, hq0Θ z0 (mem_inter_iff.mp hz0).2⟩
      rw [boolAutomorphism_value_inter_empty hΘ hb hp0 h0] at hmem2
      exact not_mem_empty hmem2
    exact ⟨fun hx ↦ absurd hx hΘbH, fun hx ↦ absurd hx hbG⟩

/-- The cone criterion for the transfer statement of Karagila and Schilhan, Lemma 9.3. If for
every filter `H` satisfying the orbit clauses there are a condition `p0` met by the generic, a
condition `q0` in `H`, and an automorphism of the Boolean completion in the forced stabilizer of
the support that sends `p0` to `q0` and matches `H` with the generic below `p0`, then the transfer
statement holds. -/
theorem orbitTransfer_of_cone_automorphism (Pf : SetTheorySemisentence 2) (s k : V) (p : A.Model)
    (h : ∀ H : A.Model, IsOrbitFilter Pf (A.check (regularSets A.P A.R))
        (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
        (A.orbitSupportReal s k) p H →
      ∃ p0 ∈ booleanConditions A.P A.R, ∃ q0 ∈ booleanConditions A.P A.R,
        ∃ Θ ∈ forcedStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R)) (range s),
        (∃ r ∈ A.G, r ∈ p0) ∧ A.check q0 ∈ H ∧ Θ ‘ p0 = q0 ∧
          ∀ b ∈ booleanConditions A.P A.R, b ⊆ p0 →
            (A.check (Θ ‘ b) ∈ H ↔ A.check b ∈ A.boolGenericSet)) :
    A.OrbitTransfer Pf s k p := by
  refine A.orbitTransfer_of_cone_automorphism_subset Pf s k p (fun H hH ↦ ?_)
  obtain ⟨p0, hp0, q0, hq0, Θ, hΘE, hmeet, hq0H, hΘp0, hpt⟩ := h H hH
  exact ⟨p0, hp0, q0, hq0, Θ, hΘE, hmeet, hq0H, hΘp0 ▸ subset_refl _, hpt⟩

/-! ### The cone hypothesis -/

/-- The cone form of the transfer statement, as Jech, Lemma 25.5 delivers it. For every filter `H`
of the extension satisfying the orbit clauses there are a condition `p0` met by the generic and a
condition `q0` in `H`, an isomorphism `f` of the cone below `p0` with the cone below `q0` that
carries the generic to `H` pointwise below `p0` and fixes the base support values of `range s`,
and an isomorphism `g` of the two complementary cones fixing them as well.

The support names are asked to be saturated nice names. That is the standing side condition of the
Solovay system: the names in a support of a hereditarily symmetric name are saturated nice names,
and it is what the lifting step needs in order to place the automorphism it builds in the forced
stabilizer of `range s`. -/
def ConeOrbitTransfer (Pf : SetTheorySemisentence 2) (s k : V) (p : A.Model) : Prop :=
  (∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) σ) →
  ∀ H : A.Model, IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H →
    ∃ p0 ∈ booleanConditions A.P A.R, ∃ q0 ∈ booleanConditions A.P A.R, ∃ f : V, ∃ g : V,
      IsForcingIsomorphism
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p0)
          (restrictedOrder (booleanOrder A.P A.R)
            (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p0))
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q0)
          (restrictedOrder (booleanOrder A.P A.R)
            (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q0)) f ∧
      IsForcingIsomorphism
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (forcingNegation A.P A.R p0))
          (restrictedOrder (booleanOrder A.P A.R)
            (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
              (forcingNegation A.P A.R p0)))
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (forcingNegation A.P A.R q0))
          (restrictedOrder (booleanOrder A.P A.R)
            (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
              (forcingNegation A.P A.R q0))) g ∧
      (∃ r ∈ A.G, r ∈ p0) ∧ A.check q0 ∈ H ∧
      (∀ b ∈ booleanConditions A.P A.R, b ⊆ p0 →
        (A.check (f ‘ b) ∈ H ↔ A.check b ∈ A.boolGenericSet)) ∧
      (∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
        coneImage A.P A.R p0 f (a ∩ p0) = a ∩ q0 ∧
          coneImage A.P A.R (forcingNegation A.P A.R p0) g
              (a ∩ forcingNegation A.P A.R p0) =
            a ∩ forcingNegation A.P A.R q0)

variable {A}

/-- The transfer statement of Karagila and Schilhan, Lemma 9.3, from the cone form of Jech,
Lemma 25.5: the automorphism is the lift of the two cone isomorphisms. -/
theorem orbitTransfer_of_coneOrbitTransfer (Pf : SetTheorySemisentence 2) {s k : V} {p : A.Model}
    (hE : ∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R)
      A.P ((ω : V) ×ˢ (ω : V)) σ)
    (h : A.ConeOrbitTransfer Pf s k p) : A.OrbitTransfer Pf s k p := by
  refine A.orbitTransfer_of_cone_automorphism_subset Pf s k p (fun H hH ↦ ?_)
  obtain ⟨p0, hp0, q0, hq0, f, g, hf, hg, hmeet, hq0H, hpt, hfix⟩ := h hE H hH
  obtain ⟨Θ, hΘE, hΘval⟩ :=
    exists_forcedStabilizer_automorphism_of_cone_isomorphisms ⟨A.one, A.top.1⟩ A.order hp0 hq0
      hf hg hE hfix
  have hΘ : IsForcingAutomorphism (booleanConditions A.P A.R) (booleanOrder A.P A.R) Θ :=
    (mem_forcingAutomorphisms_iff _ _ _).mp (mem_sep_iff.mp hΘE).1
  have hp0p0 : p0 ∩ p0 = p0 := inter_eq_left_of_subset (subset_refl p0)
  -- the image of `p0` contains `q0`
  have hq0Θ : q0 ⊆ Θ ‘ p0 := by
    have h1 := hΘval p0 hp0 (by rw [hp0p0]; exact hp0)
    rw [hp0p0, coneIsomorphism_value_top hp0 hq0 hf] at h1
    intro z hz
    have : z ∈ Θ ‘ p0 ∩ q0 := by rw [h1]; exact hz
    exact (mem_inter_iff.mp this).1
  refine ⟨p0, hp0, q0, hq0, Θ, hΘE, hmeet, hq0H, hq0Θ, fun b hb hbp ↦ ?_⟩
  -- below `p0` the automorphism agrees with the cone isomorphism up to `q0`
  have hbb : b ∩ p0 = b := inter_eq_left_of_subset hbp
  have hvalue : Θ ‘ b ∩ q0 = f ‘ b := by
    have h1 := hΘval b hb (by rw [hbb]; exact hb)
    rwa [hbb] at h1
  have hstep : A.check (Θ ‘ b) ∈ H ↔ A.check (f ‘ b) ∈ H := by
    constructor
    · intro hmem
      have hi : A.check (Θ ‘ b) ∩ A.check q0 ∈ H := hH.2.2.1 _ hmem _ hq0H
      rw [← A.check_inter, hvalue] at hi
      exact hi
    · intro hmem
      refine hH.2.1 _ hmem _ (A.check_mem_check_regularSets (function_value_mem hΘ.1 hb)) ?_
      refine (A.checkEmbedding.subset_iff _ _).mpr ?_
      rw [← hvalue]
      exact fun z hz ↦ (mem_inter_iff.mp hz).1
  rw [hstep]
  exact hpt b hb hbp

/-! ### The value of a symmetric name from the cone hypothesis -/

/-- The value of a hereditarily symmetric name of the Solovay system is definable in the extension
from ground sets, reals and ordinals, given the cone hypothesis. This is
`groundRealDefinable_booleanReal_of_transfer` with the cone hypothesis in place of the transfer
statement: the support of the name consists of saturated nice names, so the cone hypothesis applies
to it. -/
theorem groundRealDefinable_booleanReal_of_cone (A : ForcingContext V)
    (Pf : SetTheorySemisentence 2) {p : A.Model} (hp : A.IsGroundRealDefinable p)
    (hground : ∀ a : V, Pf.Evalb ![A.check a, p])
    (hcone : ∀ s k : V, A.ConeOrbitTransfer Pf s k p) (τ : A.solovayContext.Name) :
    A.IsGroundRealDefinable (A.booleanReal ⟨τ.val, τ.property.1⟩) := by
  obtain ⟨E, hEf, hE, hEs⟩ := A.solovay_exists_support τ
  obtain ⟨s, hsfin, hsrange⟩ := exists_finiteSequence_range hEf
  obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff E s).mp hsfin
  have : IsFunction s := IsFunction.of_mem hsn
  have hsdom : domain s = n := domain_eq_of_mem_function hsn
  have hnω : n ⊆ (ω : V) := IsOrdinal.toIsTransitive.transitive n hn
  have hsval : ∀ i ∈ n, s ‘ i ∈ E := by
    intro i hi
    rw [← hsrange]
    exact mem_range_of_kpair_mem (kpair_value_mem (by rw [hsdom]; exact hi))
  have hs : ∀ i ∈ n, IsNiceName (booleanConditions A.P A.R) A.P ((ω : V) ×ˢ (ω : V)) (s ‘ i) :=
    fun i hi ↦ (hE _ (hsval i hi)).nice
  have hErange : ∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions A.P A.R)
      (booleanOrder A.P A.R) A.P ((ω : V) ×ˢ (ω : V)) σ := by
    rw [hsrange]
    exact hE
  have hsym : forcedStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
      (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R)) (range s) ⊆
      nameStabilizer (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R))
        τ.val := by
    rw [hsrange]
    exact hEs
  set τ' : ForcingName A.booleanContext.P := ⟨τ.val, τ.property.1⟩ with hτ'
  have hsub1 : A.booleanReal τ' ⊆ A.solovayOrbitUnion Pf s n τ.val p :=
    A.booleanReal_subset_solovayOrbitUnion hsdom τ' hs Pf hground
  have hsub2 : A.solovayOrbitUnion Pf s n τ.val p ⊆ A.booleanReal τ' :=
    A.solovayOrbitUnion_subset_booleanReal Pf hsdom τ' hsym
      (orbitTransfer_of_coneOrbitTransfer Pf hErange (hcone s n))
  have heq : A.booleanReal τ' = A.solovayOrbitUnion Pf s n τ.val p :=
    mem_ext (fun z ↦ ⟨fun h ↦ hsub1 z h, fun h ↦ hsub2 z h⟩)
  rw [heq]
  exact A.groundRealDefinable_solovayOrbitUnion Pf s τ.val hnω hp

end ForcingContext

/-! ### The Levy export -/

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

omit [IsOrdinal κ] in
/-- The transfer statement of Karagila and Schilhan, Lemma 9.3, for the Levy collapse, from the
cone hypothesis: for every support sequence whose values are saturated nice names, and every
`k`. -/
theorem levy_orbitTransfer_of_cone
    (hcone : ∀ s k : V,
      (levyContext κ hG).ConeOrbitTransfer groundFormula s k (solovayParam κ hG)) :
    ∀ s k : V, (∀ σ ∈ range s, IsSaturatedNiceName
        (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ) →
      (levyContext κ hG).OrbitTransfer groundFormula s k (solovayParam κ hG) :=
  fun s k hE ↦ ForcingContext.orbitTransfer_of_coneOrbitTransfer groundFormula hE (hcone s k)

include hAC hU hc hω hκ in
/-- The hypothesis `hpt` of `solovay_corollary_final`, from the cone hypothesis. -/
theorem groundRealDefinable_solovayInclusion_of_cone
    (hcone : ∀ s k : V,
      (levyContext κ hG).ConeOrbitTransfer groundFormula s k (solovayParam κ hG))
    (x : (levySolovayContext κ hG).Model) :
    (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x) := by
  obtain ⟨τ, rfl⟩ := (levySolovayContext κ hG).ofName_surjective x
  refine ForcingContext.groundRealDefinable_booleanReal_of_cone (levyContext κ hG) groundFormula
    ?_ ?_ hcone τ
  · rw [solovayParam_eq_check]
    exact ForcingContext.groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
  · intro a
    exact (eval_groundFormula _ _).mpr (levy_isGround_check hAC hU hc hω hκ hG a)

include hAC hU hc hω hκ in
/-- `cor:Solovay` with the cone form of Karagila and Schilhan, Lemma 9.3 (Jech, Lemma 25.5) as its
only open assumption. The clauses are those of `solovay_corollary_of_transfer`. -/
theorem solovay_corollary_of_cone_transfer [Countable V]
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (hcone : ∀ s k : V,
      (levyContext κ hG).ConeOrbitTransfer groundFormula s k (solovayParam κ hG)) :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    (SolovayHOD κ hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 ∧
    (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := SolovayHOD κ hG) φ) ∧
    InternalDependentChoice (SolovayHOD κ hG) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → IsLebesgueMeasurable X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → BaireProperty X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → PerfectSetProperty X) ∧
    ¬ InternalChoice (SolovayHOD κ hG) ∧
    hartogsNumber (ω : SolovayHOD κ hG) = solovayCheck hAC hU hc hω hκ hG κ ∧
    IsNonprincipalSetUltrafilter (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) ∧
    IsOrdinalComplete (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) :=
  solovay_corollary_final hAC hU hc hω hκ hG hVP
    (groundRealDefinable_solovayInclusion_of_cone hAC hU hc hω hκ hG hcone)

end

end ZFVP
