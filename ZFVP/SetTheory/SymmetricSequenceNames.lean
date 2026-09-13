import ZFVP.SetTheory.ForcingSequenceNames
import ZFVP.SetTheory.SymmetricPairNames
import ZFVP.SetTheory.HereditarySymmetry

/-! A sequence name built from hereditarily symmetric names is hereditarily symmetric
once one member of the filter fixes every entry. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameAction_sequenceName_fixed {P R Γ one t π : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hone : IsForcingTop P R one) (hπ : π ∈ Γ)
    (ht : IsNameSequence P t) (hfix : ∀ i ∈ domain t, nameAction π (t ‘ i) = t ‘ i) :
    nameAction π (sequenceName one t) = sequenceName one t := by
  have ha := hΓ.1 π hπ
  have htop : π ‘ one = one := forcingAutomorphism_top hR hone ha
  have hc (i : V) : nameAction π (checkName one i) = checkName one i :=
    nameAction_checkName hone.1 htop i
  have hentry (i : V) (hi : i ∈ domain t) :
      nameAction π (orderedPairName one (checkName one i) (t ‘ i)) =
        orderedPairName one (checkName one i) (t ‘ i) := by
    rw [nameAction_orderedPairName hone.1 (checkName_isName hone.1 i) (ht i hi), htop, hc, hfix i hi]
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨σ, p, hσp, rfl⟩ := (mem_nameAction_iff (sequenceName_isName hone.1 ht) π z).mp hz
    obtain ⟨i, hi, he⟩ := (mem_sequenceName one t _).mp hσp
    obtain ⟨hσ, hp⟩ := kpair_iff.mp he
    rw [hσ, hp, hentry i hi, htop]
    exact (mem_sequenceName one t _).mpr ⟨i, hi, rfl⟩
  · intro hz
    obtain ⟨i, hi, rfl⟩ := (mem_sequenceName one t z).mp hz
    refine (mem_nameAction_iff (sequenceName_isName hone.1 ht) π _).mpr
      ⟨orderedPairName one (checkName one i) (t ‘ i), one,
        (mem_sequenceName one t _).mpr ⟨i, hi, rfl⟩, ?_⟩
    rw [hentry i hi, htop]

theorem hereditarilySymmetric_sequenceName {P R Γ F one t : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hF : IsNormalSubgroupFilter P Γ F)
    (hone : IsForcingTop P R one)
    (ht : ∀ i ∈ domain t, IsHereditarilySymmetricName P Γ F (t ‘ i))
    (hstab : ∃ H ∈ F, ∀ π ∈ H, ∀ i ∈ domain t, nameAction π (t ‘ i) = t ‘ i) :
    IsHereditarilySymmetricName P Γ F (sequenceName one t) := by
  have hN : IsNameSequence P t := fun i hi ↦ (hereditarilySymmetric_symmetric (ht i hi)).1
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨sequenceName_isName hone.1 hN, ?_⟩, ?_⟩
  · obtain ⟨H, hH, hHfix⟩ := hstab
    apply hF.2.2.1 H hH _ (nameStabilizer_subgroup hΓ (sequenceName_isName hone.1 hN))
    intro π hπ
    have hπΓ : π ∈ Γ := (hF.1 H hH).1 π hπ
    exact mem_sep_iff.mpr ⟨hπΓ, nameAction_sequenceName_fixed hR hΓ hone hπΓ hN (hHfix π hπ)⟩
  · intro σ p hσp
    obtain ⟨i, hi, he⟩ := (mem_sequenceName one t _).mp hσp
    rw [(kpair_iff.mp he).1]
    exact hereditarilySymmetric_orderedPairName hR hΓ hF hone
      (hereditarilySymmetric_checkName hR hΓ hF hone i) (ht i hi)

end ZFVP
