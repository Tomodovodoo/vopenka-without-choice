import ZFVP.SetTheory.CohenRepresentativeIntersection
import ZFVP.SetTheory.FiniteIntersectionMinimum

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A finite support of some hereditarily symmetric representative equal to `τ` below `p`. -/
def IsCohenRepresentativeSupport (τ p E : V) : Prop :=
  ∃ ν, IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) ν ∧
    p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) ν τ ∧
    IsCohenNameSupport ν E

instance isCohenRepresentativeSupport_definable :
    ℒₛₑₜ-relation₃[V] IsCohenRepresentativeSupport := by
  unfold IsCohenRepresentativeSupport
  definability

theorem IsCohenRepresentativeSupport.finite {τ p E : V}
    (hE : IsCohenRepresentativeSupport τ p E) : IsInternallyFinite E := by
  obtain ⟨_, _, _, hE⟩ := hE
  exact hE.2.1

theorem IsCohenRepresentativeSupport.subset_omega {τ p E : V}
    (hE : IsCohenRepresentativeSupport τ p E) : E ⊆ (ω : V) := by
  obtain ⟨_, _, _, hE⟩ := hE
  exact hE.1

theorem IsCohenRepresentativeSupport.inter {τ p E F : V}
    (hE : IsCohenRepresentativeSupport τ p E)
    (hF : IsCohenRepresentativeSupport τ p F) :
    IsCohenRepresentativeSupport τ p (E ∩ F) := by
  obtain ⟨ν, hν, heν, hE⟩ := hE
  obtain ⟨μ, hμ, heμ, hF⟩ := hF
  have heμ' := heμ
  rw [atomicEquality_symm _ _ μ τ] at heμ'
  have he := atomicEquality_trans (cohen_poset (ω : V)).1 ν τ μ p heν heμ'
  obtain ⟨ρ, hρ, heρ, hρs⟩ := cohen_representative_intersection_below hν hμ hE hF he
  exact ⟨ρ, hρ, atomicEquality_trans (cohen_poset (ω : V)).1 ρ ν τ p heρ heν, hρs⟩

theorem IsCohenNameSupport.representative {τ p E : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hE : IsCohenNameSupport τ E) (hp : p ∈ cohenConditions (ω : V)) :
    IsCohenRepresentativeSupport τ p E := by
  refine ⟨τ, hτ, ?_, hE⟩
  rwa [atomicEquality_refl (cohen_poset (ω : V)).1]

theorem IsCohenRepresentativeSupport.mono {τ p q E : V}
    (hE : IsCohenRepresentativeSupport τ p E)
    (hqp : ⟨q, p⟩ₖ ∈ cohenOrder (ω : V)) :
    IsCohenRepresentativeSupport τ q E := by
  obtain ⟨ν, hν, heν, hE⟩ := hE
  exact ⟨ν, hν, atomicEquality_mono (cohen_poset (ω : V)).1 heν
    ((pair_mem_cohenOrder _ _ _).mp hqp).1 hqp, hE⟩

theorem cohenRepresentative_exists_least_support {τ p : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hp : p ∈ cohenConditions (ω : V)) :
    ∃ E, IsCohenRepresentativeSupport τ p E ∧
      ∀ F, IsCohenRepresentativeSupport τ p F → E ⊆ F := by
  obtain ⟨D, hDω, hDf, hDs⟩ := cohenName_finiteSupport hτ
  have hD : IsCohenNameSupport τ D := ⟨hDω, hDf, hDs⟩
  exact finite_intersection_minimum (IsCohenRepresentativeSupport τ p) (by definability)
    ⟨D, hD.representative hτ hp, hDf⟩ (fun _ _ hE hF ↦ hE.inter hF)

noncomputable def cohenRepresentativeLeastSupport (τ p : V) : V :=
  {i ∈ (ω : V) ; ∀ F, IsCohenRepresentativeSupport τ p F → i ∈ F}

instance cohenRepresentativeLeastSupport_definable :
    ℒₛₑₜ-function₂[V] cohenRepresentativeLeastSupport := by
  have h : ℒₛₑₜ-relation₃[V] (fun E τ p ↦
      ∀ i, i ∈ E ↔ i ∈ (ω : V) ∧ ∀ F, IsCohenRepresentativeSupport τ p F → i ∈ F) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cohenRepresentativeLeastSupport (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [cohenRepresentativeLeastSupport, mem_sep_iff]

theorem cohenRepresentativeLeastSupport_subset {τ p F : V}
    (hF : IsCohenRepresentativeSupport τ p F) :
    cohenRepresentativeLeastSupport τ p ⊆ F := fun _ hi ↦ (mem_sep_iff.mp hi).2 F hF

theorem cohenRepresentativeLeastSupport_isSupport {τ p : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hp : p ∈ cohenConditions (ω : V)) :
    IsCohenRepresentativeSupport τ p (cohenRepresentativeLeastSupport τ p) := by
  obtain ⟨E, hE, hmin⟩ := cohenRepresentative_exists_least_support hτ hp
  have he : cohenRepresentativeLeastSupport τ p = E := by
    apply SetTheory.subset_antisymm (cohenRepresentativeLeastSupport_subset hE)
    intro i hi
    exact mem_sep_iff.mpr ⟨hE.subset_omega i hi, fun F hF ↦ hmin F hF i hi⟩
  rwa [he]

theorem cohenRepresentativeLeastSupport_mono {τ p q : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hqp : ⟨q, p⟩ₖ ∈ cohenOrder (ω : V)) :
    cohenRepresentativeLeastSupport τ q ⊆ cohenRepresentativeLeastSupport τ p :=
  cohenRepresentativeLeastSupport_subset ((cohenRepresentativeLeastSupport_isSupport hτ
    ((pair_mem_cohenOrder _ _ _).mp hqp).2.1).mono hqp)

end ZFVP
