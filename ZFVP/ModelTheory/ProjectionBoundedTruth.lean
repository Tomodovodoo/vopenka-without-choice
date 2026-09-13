import ZFVP.ModelTheory.GenericBoundedTruth
import ZFVP.ModelTheory.ProjectionNameTransport
import ZFVP.SetTheory.DeltaOneBoundedTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace MembershipEndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem boundedPartialTruth_iff (j : MembershipEndExtension V W) (n φ b : V) :
    BoundedPartialTruth n φ b ↔ BoundedPartialTruth (j n) (j φ) (j b) :=
  j.deltaOne_defined (sigmaOneBoundedTruthFormula_sigmaOne true)
    piOneBoundedTruthFormula_piOne
    (fun v ↦ BoundedPartialTruth (v 0) (v 1) (v 2))
    (fun v ↦ BoundedPartialTruth (v 0) (v 1) (v 2)) ![n, φ, b]

end MembershipEndExtension

namespace ForcingContext
variable (A B : ForcingContext V)

theorem genericInclusion_sequenceValue (hP : A.P ⊆ B.P)
    (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)
    (b : V) (hb : IsNameSequence A.P b) (hb' : IsNameSequence B.P b) :
    A.genericInclusion B hG (A.sequenceValue b hb) = B.sequenceValue b hb' := by
  let j := A.genericInclusion B hG
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := j.endExtension _ z hz
    obtain ⟨i, hi, rfl⟩ := (A.mem_sequenceValue b hb x).mp hx
    rw [j.map_kpair, A.genericInclusion_check B hG,
      A.genericInclusion_ofName B hP hG]
    exact (B.mem_sequenceValue b hb' _).mpr ⟨i, hi, rfl⟩
  · intro hz
    obtain ⟨i, hi, rfl⟩ := (B.mem_sequenceValue b hb' z).mp hz
    have h := (j.mem_iff _ _).mpr ((A.mem_sequenceValue b hb _).mpr ⟨i, hi, rfl⟩)
    rw [j.map_kpair] at h
    change ⟨A.genericInclusion B hG (A.check i),
      A.genericInclusion B hG (A.ofName ⟨b ‘ i, hb i hi⟩)⟩ₖ ∈ _ at h
    rw [A.genericInclusion_check B hG, A.genericInclusion_ofName B hP hG] at h
    exact h

theorem genericInclusion_boundedTruth (hP : A.P ⊆ B.P)
    (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)
    {n φ b : V} (hφ : IsBoundedFormulaCode n φ)
    (hb : IsNameSequence A.P b) (hb' : IsNameSequence B.P b) (hd : domain b = n) :
    BoundedTruth (A.check n) (A.check φ) (A.sequenceValue b hb) ↔
      BoundedTruth (B.check n) (B.check φ) (B.sequenceValue b hb') := by
  have h := (A.genericInclusion B hG).boundedPartialTruth_iff
    (A.check n) (A.check φ) (A.sequenceValue b hb)
  rw [A.genericInclusion_check B hG, A.genericInclusion_check B hG,
    A.genericInclusion_sequenceValue B hP hG b hb hb'] at h
  have ha := (A.checkEmbedding.boundedFormulaCode_iff n φ).mp hφ
  have hbcode := (B.checkEmbedding.boundedFormulaCode_iff n φ).mp hφ
  constructor
  · intro ht
    exact (h.mp ⟨ha, inferInstance, by rw [sequenceValue_domain, hd], ht⟩).2.2.2
  · intro ht
    exact (h.mpr ⟨hbcode, inferInstance, by rw [sequenceValue_domain, hd], ht⟩).2.2.2

theorem genericInclusion_boundedForcing_meets (hP : A.P ⊆ B.P)
    (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)
    {D0 D1 n φ b : V}
    (hD0 : ∀ τ ∈ D0, IsForcingName A.P τ)
    (hD1 : ∀ τ ∈ D1, IsForcingName B.P τ)
    (hne0 : IsNonempty D0) (hne1 : IsNonempty D1)
    (hc0 : ∀ τ ∈ D0, ∀ u p, ⟨u, p⟩ₖ ∈ τ → u ∈ D0)
    (hc1 : ∀ τ ∈ D1, ∀ u p, ⟨u, p⟩ₖ ∈ τ → u ∈ D1)
    (hφ : IsBoundedFormulaCode n φ) (hb0 : b ∈ D0 ^ n) (hb1 : b ∈ D1 ^ n) :
    GenericMeets A.G (internalForcingSet A.P A.R D0 n φ b) ↔
      GenericMeets B.G (internalForcingSet B.P B.R D1 n φ b) := by
  rw [← A.bounded_internalGenericTruth D0 hD0 hne0 hc0 hφ hb0,
    ← B.bounded_internalGenericTruth D1 hD1 hne1 hc1 hφ hb1]
  exact A.genericInclusion_boundedTruth B hP hG hφ
    (A.nameSequence_of_mem_function hD0 hb0) (B.nameSequence_of_mem_function hD1 hb1)
    (domain_eq_of_mem_function hb0)

end ForcingContext
end ZFVP
