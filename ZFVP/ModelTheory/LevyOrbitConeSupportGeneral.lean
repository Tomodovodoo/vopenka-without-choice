import ZFVP.ModelTheory.LevySwapConeResidue

/-! Lemma 25.5 with the cone isomorphism and the support clause available at every shrinking of the
pair on the side of the generic.

`ForcingContext.exists_orbitConeData_cone_isomorphism_support` of
`ZFVP/ModelTheory/LevySwapConeResidue.lean` produces the quadruple `τ σ p₀ q₀` of Jech, Set Theory,
Lemma 25.5 together with the cone isomorphism `ψ`, the value formula `ψ ‘ b = ‖b̌ ∈ τ‖ ∩ p₀`, the
filter clause and the support clause in `coneImage` form, but only at the one pair it builds, whose
left condition is the regular cone of a condition met by the generic.

A caller that wants to move to a smaller pair, say by shrinking the right side to the regular cone
of a condition of a dense set and then the left side to the regular cone of a condition of the
generic, can shrink the data with `orbitConeData_shrink_right` and `orbitConeData_shrink_left`, but
then has to rebuild the isomorphism and, more to the point, the support clause. Rebuilding the
support clause needs the fact that the value map is the identity on the support algebra below the
left condition, and that fact is internal to the proof of the theorem above: it comes from
`exists_condition_booleanMemValue_eq_on_supportAlgebra` and is discarded once the one pair has been
built.

`exists_orbitConeData_cone_isomorphism_support_general` keeps it, in the form of a clause that
supplies the isomorphism, the value formula, the filter clause and the support clause for every
pair `(p', q')` carrying the clauses of Lemma 25.5 whose left condition lies below `p₀` and is met
by the generic. Since both shrinking lemmas produce a pair whose left condition lies below the old
one, an arbitrary chain of shrinkings stays inside the clause. The map `ψ'` is again the value map
`b ↦ ‖b̌ ∈ τ‖ ∩ p'`, so the caller can recompute the right condition after shrinking.

The clause `‖č ∈ σ‖`-side of `exists_orbitConeData` is exported as well, because
`check_orbitInverseValue_inter_mem` needs it to see that the right condition of a left shrinking is
still in the filter. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable {A : ForcingContext V}

/-- The value map is the identity on the base support values relative to a condition below which it
is the identity on the support algebra. This is the step of
`exists_orbitConeData_cone_isomorphism_support` that produces the support clause, stated on its own
for a pair `(p', q')` carrying the clauses of Lemma 25.5 with `p'` below the condition `p₁` of
`exists_condition_booleanMemValue_eq_on_supportAlgebra`. -/
theorem coneImage_support_of_booleanMemValue_eq {τ σ p₁ p' q' ψ' E : V}
    (hdata : A.IsOrbitConeData τ σ p' q') (hp'p₁ : p' ⊆ p₁)
    (hp₁ : ∀ d ∈ supportAlgebraBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) E,
      d ∈ booleanConditions A.P A.R → A.booleanMemValue τ d ∩ p₁ = d ∩ p₁)
    (hiso : IsForcingIsomorphism
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q')
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q'))
      (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p')
      (restrictedOrder (booleanOrder A.P A.R)
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p')) ψ')
    (hψ' : ∀ b ∈ booleanConditions A.P A.R, b ⊆ q' → ψ' ‘ b = A.booleanMemValue τ b ∩ p')
    {a : V} (ha : a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) E) :
    coneImage A.P A.R q' ψ' (a ∩ q') = a ∩ p' := by
  refine coneImage_of_support_clause hdata.2.1 hdata.1 hiso (fun dd hdd hddq ↦ ?_) ha
  have hddB : dd ∈ booleanConditions A.P A.R := by
    refine (mem_booleanConditions_iff _ _ _).mpr
      ⟨((mem_algebraPreimage_iff _ _ _ _).mp hdd).1, ?_⟩
    obtain ⟨z, hz⟩ := booleanConditions_nonempty hddq
    exact ⟨z, (mem_inter_iff.mp hz).1⟩
  have hfix : A.booleanMemValue τ dd ∩ p' = dd ∩ p' := by
    have h := hp₁ dd hdd hddB
    rw [SetTheory.mem_ext_iff] at h
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨hzv, hzp⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp ((h z).mp (mem_inter_iff.mpr ⟨hzv, hp'p₁ z hzp⟩))).1, hzp⟩
    · intro hz
      obtain ⟨hzd, hzp⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp ((h z).mpr (mem_inter_iff.mpr ⟨hzd, hp'p₁ z hzp⟩))).1, hzp⟩
  rw [hψ' _ hddq (fun z hz ↦ (mem_inter_iff.mp hz).2),
    A.orbitConeData_inter_eq hdata hddB hdata.2.1]
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨hzi, hzp⟩ := mem_inter_iff.mp hz
    have hz' : z ∈ A.booleanMemValue τ dd ∩ p' :=
      mem_inter_iff.mpr ⟨(mem_inter_iff.mp hzi).1, hzp⟩
    rw [hfix] at hz'
    exact mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz').1, hzp⟩
  · intro hz
    obtain ⟨hzd, hzp⟩ := mem_inter_iff.mp hz
    have hz' : z ∈ dd ∩ p' := mem_inter_iff.mpr ⟨hzd, hzp⟩
    rw [← hfix] at hz'
    exact mem_inter_iff.mpr
      ⟨mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz').1, hdata.2.2.2.2.2.2.1 z hzp⟩, hzp⟩

/-- `exists_orbitConeData_cone_isomorphism_support` with the isomorphism, the value formula, the
filter clause and the support clause available not only at the pair that is built but at every pair
carrying the clauses of Lemma 25.5 whose left condition lies below the one that is built and is met
by the generic.

The last clause is the generalization. Its left condition `p'` is an arbitrary nonzero condition
met by the generic below `p₀ = coneRegular r`, not necessarily a regular cone, and its right
condition `q'` is whatever condition the clauses of Lemma 25.5 pair with it; both shrinking lemmas
`orbitConeData_shrink_left` and `orbitConeData_shrink_right` produce such a pair, so the clause
applies after any chain of shrinkings. The map is the value map `b ↦ ‖b̌ ∈ τ‖ ∩ p'` there too.

The clause on `σ` is the one of `exists_orbitConeData`; `check_orbitInverseValue_inter_mem` uses it
to keep the right condition inside the filter when the left one shrinks. -/
theorem exists_orbitConeData_cone_isomorphism_support_general (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {s k : V} [IsFunction s] (hsdom : domain s = k)
    (hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) (s ‘ i))
    {p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ τ σ : V, ∃ r ∈ A.G, ∃ q₀ ∈ booleanConditions A.P A.R, ∃ ψ : V,
      (∀ b : V, (A.check b ∈ H ↔ ∃ t ∈ A.G, t ∈ A.booleanMemValue τ b)) ∧
      (∀ c ∈ booleanConditions A.P A.R,
        (A.check c ∈ A.boolGenericSet ↔ A.check (A.orbitInverseValue σ c) ∈ H)) ∧
      A.IsOrbitConeData τ σ (coneRegular A.P A.R r) q₀ ∧
      A.check q₀ ∈ H ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R r))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r))) ψ ∧
      (∀ b ∈ booleanConditions A.P A.R, b ⊆ q₀ →
        ψ ‘ b = A.booleanMemValue τ b ∩ coneRegular A.P A.R r) ∧
      (∀ c ∈ booleanConditions A.P A.R, c ⊆ q₀ →
        (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet)) ∧
      (∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
        coneImage A.P A.R q₀ ψ (a ∩ q₀) = a ∩ coneRegular A.P A.R r) ∧
      (∀ p' q' : V, A.IsOrbitConeData τ σ p' q' → p' ⊆ coneRegular A.P A.R r →
        (∃ t ∈ A.G, t ∈ p') →
        ∃ ψ' : V,
          IsForcingIsomorphism
            (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q')
            (restrictedOrder (booleanOrder A.P A.R)
              (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q'))
            (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p')
            (restrictedOrder (booleanOrder A.P A.R)
              (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p')) ψ' ∧
          (∀ b ∈ booleanConditions A.P A.R, b ⊆ q' →
            ψ' ‘ b = A.booleanMemValue τ b ∩ p') ∧
          (∀ c ∈ booleanConditions A.P A.R, c ⊆ q' →
            (A.check c ∈ H ↔ A.check (ψ' ‘ c) ∈ A.boolGenericSet)) ∧
          (∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
            coneImage A.P A.R q' ψ' (a ∩ q') = a ∩ p')) := by
  classical
  obtain ⟨τ, σ, p₀, q₀, hval, hd, hp₀G, hq₀H, hdata⟩ := exists_orbitConeData hAC hH hPf
  obtain ⟨p₁, hp₁B, hp₁G, hp₁⟩ :=
    exists_condition_booleanMemValue_eq_on_supportAlgebra hAC hsdom hs hH hval
  obtain ⟨w, hwG, hw⟩ := meets_inter (booleanConditions_regular hdata.1)
    (booleanConditions_regular hp₁B) hp₀G hp₁G
  have hwP : w ∈ A.P := A.generic.1.1 w hwG
  have hp'B : coneRegular A.P A.R w ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hwP
  have hp'G : ∃ t ∈ A.G, t ∈ coneRegular A.P A.R w :=
    ⟨w, hwG, self_mem_coneRegular A.order hwP⟩
  have hp'p₀ : coneRegular A.P A.R w ⊆ p₀ := coneRegular_subset_of_mem A.order
    (booleanConditions_regular hdata.1) (mem_inter_iff.mp hw).1
  have hp'p₁ : coneRegular A.P A.R w ⊆ p₁ := coneRegular_subset_of_mem A.order
    (booleanConditions_regular hp₁B) (mem_inter_iff.mp hw).2
  have hdata' := A.orbitConeData_shrink_left hdata hp'B hp'p₀
  have hq'H : A.check (A.orbitInverseValue σ (coneRegular A.P A.R w) ∩ q₀) ∈ H :=
    A.check_orbitInverseValue_inter_mem hH.2.2.1 hd hp'B hp'G hq₀H
  -- the general clause: every pair below the built one gets its own isomorphism
  have hgen : ∀ p' q' : V, A.IsOrbitConeData τ σ p' q' → p' ⊆ coneRegular A.P A.R w →
      (∃ t ∈ A.G, t ∈ p') →
      ∃ ψ' : V,
        IsForcingIsomorphism
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q')
          (restrictedOrder (booleanOrder A.P A.R)
            (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q'))
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p')
          (restrictedOrder (booleanOrder A.P A.R)
            (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p')) ψ' ∧
        (∀ b ∈ booleanConditions A.P A.R, b ⊆ q' →
          ψ' ‘ b = A.booleanMemValue τ b ∩ p') ∧
        (∀ c ∈ booleanConditions A.P A.R, c ⊆ q' →
          (A.check c ∈ H ↔ A.check (ψ' ‘ c) ∈ A.boolGenericSet)) ∧
        (∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
          coneImage A.P A.R q' ψ' (a ∩ q') = a ∩ p') := by
    intro p' q' hdp hpw hpG
    obtain ⟨ψ', hiso', htr', hψ'⟩ := A.exists_cone_isomorphism_of_data hdp hval hpG
    exact ⟨ψ', hiso', hψ', htr', fun a ha ↦ coneImage_support_of_booleanMemValue_eq hdp
      (subset_trans hpw hp'p₁) hp₁ hiso' hψ' ha⟩
  obtain ⟨ψ, hiso, hψ, htr, hsupp⟩ := hgen _ _ hdata' (fun z hz ↦ hz) hp'G
  exact ⟨τ, σ, w, hwG, _, hdata'.2.1, ψ, hval, hd, hdata', hq'H, hiso, hψ, htr, hsupp, hgen⟩

end ForcingContext

end ZFVP
