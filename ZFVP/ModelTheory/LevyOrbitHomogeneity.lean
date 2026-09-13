import ZFVP.ModelTheory.SolovayOrbitDefinable
import ZFVP.ModelTheory.LevyGaloisFactor

/-! What an orbit filter of Karagila-Schilhan, Proposition 9.4, gives without a ground
automorphism.

`ZFVP/ModelTheory/SolovayOrbitDefinable.lean` reduces the Solovay corollary to
`ForcingContext.OrbitTransfer`: every internally generic filter `H` of the extension that agrees
with the generic on the finitely many support names is `π"G` for a ground automorphism `π` in the
forced stabilizer of the support. The automorphism is used only for the value it transports,
namely `τ^H = τ^G`.

This module gets that value transport a different way, from the agreement of `H` with the generic
on the support algebra rather than from an automorphism.

The first half is unconditional. For a saturated nice name `σ` over `K`, a checked code `ǩ` is in
`σ^H` exactly when `H` contains the Boolean value `‖ǩ ∈ σ‖` read as a regular set of `P`
(`check_mem_nameValue_iff_booleanValueBase`); this uses only that `H` is an upward closed proper
filter containing the top. The clause of `IsOrbitFilter` that fixes the values of the support
names therefore says exactly that `H` and the generic contain the same base support values
(`orbitFilter_agree_supportValuesBase`), and the uniqueness theorem for generic ultrafilters on a
generated subalgebra lifts that to the whole support algebra
(`orbitFilter_agree_supportAlgebraBase`).

The second half turns agreement into equal values. Two filters that contain the same conditions of
`Q` give the same value to every name over `Q` (`nameValue_eq_of_agree`), by induction on names and
with no genericity. The reduct `nameReduct P R τ` replaces each condition of `τ` by the Boolean
value of the membership statement it forces, so when all those values lie in the support algebra
`D`, the reduct is a name over `D` and `H` and the generic give it the same value
(`nameValue_nameReduct_orbitFilter`). The hypothesis that they do lie in `D` is exactly what the
Galois step of Lemma 9.3 delivers, through `closureValuesInSupportAlgebra_of_galois` and
`isHereditarilyInAlgebra_of_closureValues`; it is unconditional for nice names.

What is left open is the truth lemma for `H` itself: that the value at `H` of a name is contained
in the value at `H` of its reduct (`ReductValues`). The generic satisfies it, because the reduct is
forced equal to the name (`reductValues_boolGenericSet`), and the induction proving it for a
general filter needs the two atomic truth lemmas for that filter, which in turn need the
antichain-genericity clause of `IsOrbitFilter`. The repository has the truth lemma only for the
external generic of a forcing context, and the induction cannot be run in the ground model because
the statement is about elements of the extension. With `ReductValues` for the orbit filters as a
hypothesis, `solovayOrbitUnion_subset_booleanReal_of_algebra` proves the hard half of Proposition
9.4 with no automorphism anywhere. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable {A : ForcingContext V}

/-! ### Values of saturated nice names read off the Boolean values -/

/-- For a saturated nice name `σ` over `K`, a checked code `ǩ` lies in the value of `σ` at a
filter `H` exactly when `H` contains the Boolean value `‖ǩ ∈ σ‖` read as a regular set of `P`.
Only the filter clauses are used: upward closure inside the checked regular sets, no empty member,
and the checked top. -/
theorem check_mem_nameValue_iff_booleanValueBase {K σ : V}
    (hσ : IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P K σ)
    {H : A.Model}
    (hup : ∀ d ∈ H, ∀ d' ∈ A.check (regularSets A.P A.R), d ⊆ d' → d' ∈ H)
    (hprop : ∀ d ∈ H, ∃ z, z ∈ d) (htop : A.check A.P ∈ H) {k : V} (hk : k ∈ K) :
    A.check k ∈ nameValue H (A.check σ) ↔
      A.check (booleanValueBase A.P A.R (checkName A.P k) σ) ∈ H := by
  have hbreg : ∀ ν μ : V, A.check (booleanValueBase A.P A.R ν μ) ∈
      A.check (regularSets A.P A.R) := fun ν μ ↦
    (A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr
      (booleanValueBase_regular A.order ν μ))
  constructor
  · intro h
    obtain ⟨ν, C, hCH, hpair, heq⟩ := (mem_nameValue_iff H (A.check σ) _).mp h
    obtain ⟨w, hw, hweq⟩ := (A.mem_check_iff σ _).mp hpair
    rw [hσ] at hw
    obtain ⟨k', hk', p, hp, rfl, hpm⟩ := (mem_niceName_iff _ _ _ _ _ _).mp hw
    rw [A.check_kpair] at hweq
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hweq
    rw [A.nameValue_check_checkName htop k'] at heq
    obtain rfl : k = k' := (A.check_eq_iff k k').mp heq
    refine hup _ hCH _ (hbreg _ _) ?_
    exact (A.checkEmbedding.subset_iff _ _).mpr (subset_booleanValueBase A.order hpm)
  · intro h
    obtain ⟨z, hz⟩ := hprop _ h
    obtain ⟨z₀, hz₀, -⟩ := (A.mem_check_iff _ _).mp hz
    have hbB : booleanValueBase A.P A.R (checkName A.P k) σ ∈ booleanConditions A.P A.R :=
      (mem_booleanConditions_iff _ _ _).mpr
        ⟨booleanValueBase_regular A.order _ _, z₀, hz₀⟩
    have hbm : booleanValueBase A.P A.R (checkName A.P k) σ ∈
        atomicMembership (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (checkName A.P k) σ :=
      mem_atomicMembership_of_subset_booleanValueBase A.order hbB (subset_refl _)
    have hmem : (⟨checkName A.P k, booleanValueBase A.P A.R (checkName A.P k) σ⟩ₖ : V) ∈ σ := by
      have h1 : (⟨checkName A.P k, booleanValueBase A.P A.R (checkName A.P k) σ⟩ₖ : V) ∈
          niceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P K σ :=
        (mem_niceName_iff _ _ _ _ _ _).mpr ⟨k, hk, _, hbB, rfl, hbm⟩
      rwa [← hσ] at h1
    refine (mem_nameValue_iff H (A.check σ) _).mpr
      ⟨A.check (checkName A.P k), _, h, ?_, (A.nameValue_check_checkName htop k).symm⟩
    rw [← A.check_kpair]
    exact (A.check_mem_iff _ _).mpr hmem

/-! ### Two filters with the same values on the support names agree on the support values -/

/-- If two filters give the names of `E` the same values, they contain the same base support
values of `E`. -/
theorem agree_supportValuesBase_of_nameValue_eq {K E : V}
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P K σ)
    {H H' : A.Model}
    (hup : ∀ d ∈ H, ∀ d' ∈ A.check (regularSets A.P A.R), d ⊆ d' → d' ∈ H)
    (hprop : ∀ d ∈ H, ∃ z, z ∈ d) (htop : A.check A.P ∈ H)
    (hup' : ∀ d ∈ H', ∀ d' ∈ A.check (regularSets A.P A.R), d ⊆ d' → d' ∈ H')
    (hprop' : ∀ d ∈ H', ∃ z, z ∈ d) (htop' : A.check A.P ∈ H')
    (hval : ∀ σ ∈ E, nameValue H (A.check σ) = nameValue H' (A.check σ)) :
    ∀ b ∈ A.check (supportValuesBase A.P A.R A.P K E), (b ∈ H ↔ b ∈ H') := by
  intro b hb
  obtain ⟨b₀, hb₀, rfl⟩ := (A.mem_check_iff _ _).mp hb
  obtain ⟨k, hk, σ, hσ, rfl⟩ := (mem_supportValuesBase_iff _ _ _ _ _ _).mp hb₀
  rw [← check_mem_nameValue_iff_booleanValueBase (hE σ hσ) hup hprop htop hk,
    ← check_mem_nameValue_iff_booleanValueBase (hE σ hσ) hup' hprop' htop' hk, hval σ hσ]

/-! ### The support values an orbit filter contains -/

/-- An orbit filter gives the support names the same values as the generic does. -/
theorem orbitFilter_nameValue_eq {Pf : SetTheorySemisentence 2} {s k : V} [IsFunction s]
    (hsdom : domain s = k)
    (hs : ∀ i ∈ k, IsNiceName (booleanConditions A.P A.R) A.P ((ω : V) ×ˢ (ω : V)) (s ‘ i))
    {p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H) :
    ∀ i₀ ∈ k, nameValue H (A.check (s ‘ i₀)) =
      nameValue A.boolGenericSet (A.check (s ‘ i₀)) := by
  have hsupp := hH.2.2.2.2.2.2.2
  have hone : A.check A.P ∈ A.boolGenericSet := A.check_top_mem_boolGenericSet
  intro i₀ hi₀
  have hvi : (A.check s) ‘ (A.check i₀) = A.check (s ‘ i₀) :=
    A.check_value (by rw [hsdom]; exact hi₀)
  apply mem_ext
  intro z
  have h := hsupp (A.check i₀) ((A.check_mem_iff _ _).mpr hi₀) z
  rw [hvi] at h
  rw [h, A.mem_orbitSupportReal_iff]
  constructor
  · rintro ⟨-, i', z', he, hz'⟩
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    rwa [hvi] at hz'
  · intro hz
    have hzK : z ∈ A.check ((ω : V) ×ˢ (ω : V)) :=
      nameValue_check_subset_check_of_nice (hs i₀ hi₀) hone z hz
    refine ⟨?_, A.check i₀, z, rfl, by rw [hvi]; exact hz⟩
    rw [show A.check (k ×ˢ ((ω : V) ×ˢ (ω : V)))
        = A.check k ×ˢ A.check ((ω : V) ×ˢ (ω : V)) from A.checkEmbedding.map_prod _ _]
    exact mem_prod_iff.mpr ⟨A.check i₀, (A.check_mem_iff _ _).mpr hi₀, z, hzK, rfl⟩

/-- An orbit filter contains exactly the base support values of the support names that the
generic contains. -/
theorem orbitFilter_agree_supportValuesBase {Pf : SetTheorySemisentence 2} {s k : V}
    [IsFunction s] (hsdom : domain s = k)
    (hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) (s ‘ i))
    {p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H) :
    ∀ b ∈ A.check (supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s)),
      (b ∈ A.boolGenericSet ↔ b ∈ H) := by
  have hup := hH.2.1
  have hprop := hH.2.2.2.1
  have htop := hH.2.2.2.2.2.1
  have hgen := A.boolGenericSet_antichainGeneric
  have hgprop : ∀ d ∈ A.boolGenericSet, ∃ z, z ∈ d := by
    intro u hu
    obtain ⟨-, q, -, hq⟩ := mem_sep_iff.mp hu
    exact ⟨q, hq⟩
  have hrange : ∀ σ ∈ range s, ∃ i₀ ∈ k, σ = s ‘ i₀ := by
    intro σ hσ
    obtain ⟨i₀, hi₀⟩ := mem_range_iff.mp hσ
    exact ⟨i₀, hsdom ▸ mem_domain_of_kpair_mem hi₀, (value_eq_of_kpair_mem hi₀).symm⟩
  refine agree_supportValuesBase_of_nameValue_eq (fun σ hσ ↦ ?_) hgen.upward hgprop
    A.check_top_mem_boolGenericSet hup hprop htop (fun σ hσ ↦ ?_)
  · obtain ⟨i₀, hi₀, rfl⟩ := hrange σ hσ
    exact hs i₀ hi₀
  · obtain ⟨i₀, hi₀, rfl⟩ := hrange σ hσ
    exact (orbitFilter_nameValue_eq hsdom (fun i hi ↦ (hs i hi).nice) hH i₀ hi₀).symm

/-- An orbit filter agrees with the generic on the whole support algebra of the support names,
read as a complete subalgebra of `RO(P)`. This is the part of Karagila-Schilhan, Lemma 9.3 that
needs no ground automorphism: the two filters trace the same subalgebra. -/
theorem orbitFilter_agree_supportAlgebraBase (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {s k : V} [IsFunction s] (hsdom : domain s = k)
    (hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) (s ‘ i))
    {p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H) :
    ∀ d ∈ A.check (supportAlgebraBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s)),
      (d ∈ A.boolGenericSet ↔ d ∈ H) := by
  rw [supportAlgebraBase_eq_generatedSubalgebra A.order ⟨A.one, A.top.1⟩ _ _ _]
  exact A.generatedSubalgebra_generic_unique hAC
    (supportValuesBase_subset_regularSets A.order _ _ _)
    (antichainGeneric_of_clauses hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2.1)
    (orbitFilter_agree_supportValuesBase hsdom hs hH)

end ForcingContext

/-! ### Values of a name over a set of conditions on which two filters agree -/

section

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem isForcingName_mono {Q Q' τ : M} (hQ : Q ⊆ Q') (hτ : IsForcingName Q τ) :
    IsForcingName Q' τ := by
  intro σ hσ z hz
  obtain ⟨υ, p, hp, he⟩ := hτ σ hσ z hz
  exact ⟨υ, p, hQ p hp, he⟩

/-- Two filters that contain the same conditions of `Q` give the same value to every name over
`Q`. No genericity is used. -/
theorem nameValue_eq_of_agree {Q U U' ρ : M} (hagree : ∀ d ∈ Q, (d ∈ U ↔ d ∈ U'))
    (hρ : IsForcingName Q ρ) : nameValue U ρ = nameValue U' ρ := by
  apply forcingName_induction Q (fun ρ ↦ nameValue U ρ = nameValue U' ρ) (by definability) ?_ ρ hρ
  intro τ hτ ih
  apply mem_ext
  intro z
  rw [mem_nameValue_iff, mem_nameValue_iff]
  constructor
  · rintro ⟨σ, p, hp, hσp, rfl⟩
    exact ⟨σ, p, (hagree p (forcingName_condition hτ hσp)).mp hp, hσp, ih σ p hσp⟩
  · rintro ⟨σ, p, hp, hσp, rfl⟩
    exact ⟨σ, p, (hagree p (forcingName_condition hτ hσp)).mpr hp, hσp, (ih σ p hσp).symm⟩

end

namespace ForcingContext

variable {A : ForcingContext V}

/-- The reduct of a name whose Boolean values lie in `D` is a name over the checked conditions
of `D`. -/
theorem check_nameReduct_isForcingName {D τ : V}
    (hτ : IsHereditarilyInAlgebra A.P A.R D τ) :
    IsForcingName (A.check (subalgebraConditions A.P A.R D)) (A.check (nameReduct A.P A.R τ)) :=
  A.checkEmbedding.map_forcingName (nameReduct_isForcingName A.order hτ)

/-- Two filters of the extension that agree on the checked subalgebra `D` give the same value to
the reduct of any name whose Boolean values lie in `D`. -/
theorem nameValue_check_nameReduct_eq_of_agree {D τ : V}
    (hτ : IsHereditarilyInAlgebra A.P A.R D τ) {U U' : A.Model}
    (hagree : ∀ d ∈ A.check D, (d ∈ U ↔ d ∈ U')) :
    nameValue U (A.check (nameReduct A.P A.R τ)) =
      nameValue U' (A.check (nameReduct A.P A.R τ)) := by
  refine nameValue_eq_of_agree (fun d hd ↦ ?_) (check_nameReduct_isForcingName hτ)
  rw [show subalgebraConditions A.P A.R D = D ∩ booleanConditions A.P A.R from rfl,
    A.check_inter] at hd
  exact hagree d (mem_inter_iff.mp hd).1

/-- The value of the reduct at the generic is the value of the name: the reduct is forced equal
to the name. -/
theorem booleanReal_nameReduct (A : ForcingContext V) (τ : ForcingName A.booleanContext.P)
    (hred : IsForcingName A.booleanContext.P (nameReduct A.P A.R τ.val)) :
    A.booleanReal ⟨nameReduct A.P A.R τ.val, hred⟩ = A.booleanReal τ := by
  unfold booleanReal
  refine congrArg _ ?_
  obtain ⟨q, hqG⟩ := A.booleanContext.generic.1.2.1
  exact (forcingQuotientMk_eq_iff _ _ _ _ _ _ _).mpr
    ⟨q, hqG, forcedEqual_nameReduct A.order τ.val q (A.booleanContext.generic.1.1 q hqG)⟩

/-! ### The value of the reduct at an orbit filter -/

/-- The value at an orbit filter of the reduct of a name whose Boolean values all lie in the
support algebra of the support names is the value of the name at the generic. The hypothesis
`IsHereditarilyInAlgebra` is what the Galois step of Karagila-Schilhan, Lemma 9.3 delivers, by
`closureValuesInSupportAlgebra_of_galois` and `isHereditarilyInAlgebra_of_closureValues`. -/
theorem nameValue_nameReduct_orbitFilter (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {s k : V} [IsFunction s] (hsdom : domain s = k)
    (hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) (s ‘ i))
    {p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H)
    (τ : ForcingName A.booleanContext.P)
    (hτ : IsHereditarilyInAlgebra A.P A.R
      (supportAlgebraBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s)) τ.val) :
    nameValue H (A.check (nameReduct A.P A.R τ.val)) = A.booleanReal τ := by
  have hname : IsForcingName A.booleanContext.P (nameReduct A.P A.R τ.val) :=
    isForcingName_mono (fun z hz ↦ (mem_inter_iff.mp hz).2)
      (nameReduct_isForcingName A.order hτ)
  rw [nameValue_check_nameReduct_eq_of_agree hτ
      (fun d hd ↦ (orbitFilter_agree_supportAlgebraBase hAC hsdom hs hH d hd).symm),
    ← A.booleanReal_eq_nameValue ⟨nameReduct A.P A.R τ.val, hname⟩]
  exact A.booleanReal_nameReduct τ hname

/-! ### The step that is not closed -/

/-- The truth lemma for an internally generic filter, in the only form the orbit union needs: the
value at `H` of a name is contained in the value at `H` of its reduct. Membership in the value of
the reduct is membership in a name whose conditions are the full Boolean values `‖ν ∈ μ‖`, so the
inclusion is the statement that `H` respects the passage from a condition forcing a membership to
the Boolean value of that membership, hereditarily. The repository proves this for the external
generic of a forcing context, not for a filter of the extension. -/
def ReductValues (A : ForcingContext V) (H : A.Model) : Prop :=
  ∀ τ : V, IsForcingName (booleanConditions A.P A.R) τ →
    nameValue H (A.check τ) ⊆ nameValue H (A.check (nameReduct A.P A.R τ))

/-- Every name has its reduct a name over the completion. -/
theorem nameReduct_isForcingName_boolean (A : ForcingContext V) (τ : V) :
    IsForcingName A.booleanContext.P (nameReduct A.P A.R τ) :=
  isForcingName_mono (fun _ hz ↦ (mem_inter_iff.mp hz).2)
    (nameReduct_isForcingName A.order
      (fun μ _ ν _ ↦ (mem_regularSets_iff _ _ _).mpr (booleanValueBase_regular A.order ν μ)))

/-- The generic itself satisfies the truth lemma: passing to the reduct does not change the value
of a name at the generic, because the reduct is forced equal to the name. So `ReductValues` is not
a vacuous hypothesis; what is open is that the other orbit filters satisfy it too. -/
theorem reductValues_boolGenericSet (A : ForcingContext V) : A.ReductValues A.boolGenericSet := by
  intro τ hτ
  have hname := A.nameReduct_isForcingName_boolean τ
  rw [← A.booleanReal_eq_nameValue ⟨τ, hτ⟩,
    ← A.booleanReal_eq_nameValue ⟨nameReduct A.P A.R τ, hname⟩,
    A.booleanReal_nameReduct ⟨τ, hτ⟩ hname]

/-- The value at an orbit filter of a name whose Boolean values lie in the support algebra is
contained in its value at the generic, given the truth lemma for that filter. This is the
inclusion that `solovayOrbitUnion_subset_booleanReal` extracts from `OrbitTransfer`, obtained
here without a ground automorphism. -/
theorem nameValue_orbitFilter_subset_booleanReal (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {s k : V} [IsFunction s] (hsdom : domain s = k)
    (hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) (s ‘ i))
    {p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H)
    (hred : A.ReductValues H)
    (τ : ForcingName A.booleanContext.P)
    (hτ : IsHereditarilyInAlgebra A.P A.R
      (supportAlgebraBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s)) τ.val) :
    nameValue H (A.check τ.val) ⊆ A.booleanReal τ := by
  rw [← nameValue_nameReduct_orbitFilter hAC hsdom hs hH τ hτ]
  exact hred τ.val τ.property

/-- The hard half of Karagila-Schilhan, Proposition 9.4 with the Galois step and the truth lemma
for orbit filters in place of `OrbitTransfer`: no ground automorphism is produced. -/
theorem solovayOrbitUnion_subset_booleanReal_of_algebra (hAC : InternalChoice V)
    (Pf : SetTheorySemisentence 2) {p : A.Model} {s k : V} [IsFunction s] (hsdom : domain s = k)
    (hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) (s ‘ i))
    (hred : ∀ H : A.Model, IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H → A.ReductValues H)
    (τ : ForcingName A.booleanContext.P)
    (hτ : IsHereditarilyInAlgebra A.P A.R
      (supportAlgebraBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s)) τ.val) :
    A.solovayOrbitUnion Pf s k τ.val p ⊆ A.booleanReal τ := by
  have hN : IsSubnameClosed (A.check (orbitClosure s τ.val)) :=
    transitive_subnameClosed (check_transitive_of_ground (orbitClosure_transitive s τ.val))
  have hct : A.check τ.val ∈ A.check (orbitClosure s τ.val) :=
    (A.check_mem_iff _ _).mpr (mem_orbitClosure_self s τ.val)
  have hcs : ∀ i ∈ A.check k, (A.check s) ‘ i ∈ A.check (orbitClosure s τ.val) := by
    intro i hi
    obtain ⟨i₀, hi₀, rfl⟩ := (A.mem_check_iff _ _).mp hi
    rw [A.check_value (f := s) (by rw [hsdom]; exact hi₀)]
    exact (A.check_mem_iff _ _).mpr (mem_orbitClosure_of_mem_range
      (mem_range_of_kpair_mem (kpair_value_mem (by rw [hsdom]; exact hi₀))))
  intro b hb
  rw [A.mem_solovayOrbitUnion_iff] at hb
  have he : (b :> A.solovayOrbitParams s k τ.val p) =
      ![b, A.orbitBound τ.val, A.check (regularSets A.P A.R),
        A.check (boolMaximalAntichains A.P A.R), A.check A.P, A.check (orbitClosure s τ.val),
        A.check τ.val, A.check s, A.check k, A.orbitSupportReal s k, p] := rfl
  rw [he, eval_solovayOrbitFormula Pf hN hct hcs] at hb
  obtain ⟨-, H, hH, hbH⟩ := hb
  exact nameValue_orbitFilter_subset_booleanReal hAC hsdom hs hH (hred H hH) τ hτ b hbH

end ForcingContext

end ZFVP
