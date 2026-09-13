import ZFVP.SetTheory.ForcingAutomorphisms
import ZFVP.SetTheory.NameActionClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingAutomorphismGroup (P R Γ : V) : Prop :=
  (∀ π ∈ Γ, IsForcingAutomorphism P R π) ∧ identity P ∈ Γ ∧
    (∀ π ∈ Γ, ∀ ρ ∈ Γ, compose π ρ ∈ Γ) ∧ ∀ π ∈ Γ, converseGraph π ∈ Γ

def IsForcingSubgroup (P Γ H : V) : Prop :=
  H ⊆ Γ ∧ identity P ∈ H ∧
    (∀ π ∈ H, ∀ ρ ∈ H, compose π ρ ∈ H) ∧ ∀ π ∈ H, converseGraph π ∈ H

instance isForcingAutomorphismGroup_definable : ℒₛₑₜ-relation₃[V] IsForcingAutomorphismGroup := by
  unfold IsForcingAutomorphismGroup
  definability

instance isForcingSubgroup_definable : ℒₛₑₜ-relation₃[V] IsForcingSubgroup := by
  unfold IsForcingSubgroup
  definability

theorem forcingAutomorphisms_group (P R : V) : IsForcingAutomorphismGroup P R (forcingAutomorphisms P R) := by
  refine ⟨fun π hπ ↦ (mem_forcingAutomorphisms_iff P R π).mp hπ,
    (mem_forcingAutomorphisms_iff _ _ _).mpr (forcingAutomorphism_identity P R), ?_, ?_⟩
  · intro π hπ ρ hρ
    exact (mem_forcingAutomorphisms_iff _ _ _).mpr
      (forcingAutomorphism_compose ((mem_forcingAutomorphisms_iff _ _ _).mp hπ)
        ((mem_forcingAutomorphisms_iff _ _ _).mp hρ))
  · intro π hπ
    exact (mem_forcingAutomorphisms_iff _ _ _).mpr
      (forcingAutomorphism_inverse ((mem_forcingAutomorphisms_iff _ _ _).mp hπ))

theorem forcingGroup_subgroup_self {P R Γ : V} (hΓ : IsForcingAutomorphismGroup P R Γ) :
    IsForcingSubgroup P Γ Γ := ⟨fun _ h ↦ h, hΓ.2⟩

theorem forcingSubgroup_inter {P Γ H K : V} (hH : IsForcingSubgroup P Γ H)
    (hK : IsForcingSubgroup P Γ K) : IsForcingSubgroup P Γ (H ∩ K) := by
  refine ⟨fun π hπ ↦ hH.1 π (mem_inter_iff.mp hπ).1, mem_inter_iff.mpr ⟨hH.2.1, hK.2.1⟩, ?_, ?_⟩
  · intro π hπ ρ hρ
    exact mem_inter_iff.mpr ⟨hH.2.2.1 π (mem_inter_iff.mp hπ).1 ρ (mem_inter_iff.mp hρ).1,
      hK.2.2.1 π (mem_inter_iff.mp hπ).2 ρ (mem_inter_iff.mp hρ).2⟩
  · intro π hπ
    exact mem_inter_iff.mpr ⟨hH.2.2.2 π (mem_inter_iff.mp hπ).1, hK.2.2.2 π (mem_inter_iff.mp hπ).2⟩

noncomputable def conjugateSubgroup (π H : V) : V :=
  repl (fun ρ ↦ compose (compose (converseGraph π) ρ) π) (by definability) H

instance conjugateSubgroup_definable : ℒₛₑₜ-function₂[V] conjugateSubgroup := by
  have h : ℒₛₑₜ-relation₃ (fun C π H : V ↦ ∀ θ, θ ∈ C ↔
      ∃ ρ ∈ H, θ = compose (compose (converseGraph π) ρ) π) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = conjugateSubgroup (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp [conjugateSubgroup, repl_spec]

def IsNormalSubgroupFilter (P Γ F : V) : Prop :=
  (∀ H ∈ F, IsForcingSubgroup P Γ H) ∧ Γ ∈ F ∧
    (∀ H ∈ F, ∀ K : V, IsForcingSubgroup P Γ K → H ⊆ K → K ∈ F) ∧
    (∀ H ∈ F, ∀ K ∈ F, H ∩ K ∈ F) ∧
    ∀ π ∈ Γ, ∀ H ∈ F, conjugateSubgroup π H ∈ F

instance isNormalSubgroupFilter_definable : ℒₛₑₜ-relation₃[V] IsNormalSubgroupFilter := by
  unfold IsNormalSubgroupFilter
  definability

def IsSymmetricSystem (P R Γ F : V) : Prop :=
  IsForcingPoset P R ∧ (∃ one : V, IsForcingTop P R one) ∧
    IsForcingAutomorphismGroup P R Γ ∧ IsNormalSubgroupFilter P Γ F

instance isSymmetricSystem_definable : ℒₛₑₜ-relation₄[V] IsSymmetricSystem := by
  unfold IsSymmetricSystem
  definability

noncomputable def nameStabilizer (Γ τ : V) : V := {π ∈ Γ ; nameAction π τ = τ}

instance nameStabilizer_definable : ℒₛₑₜ-function₂[V] nameStabilizer := by
  have h : ℒₛₑₜ-relation₃ (fun H Γ τ : V ↦ ∀ π, π ∈ H ↔ π ∈ Γ ∧ nameAction π τ = τ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameStabilizer (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp [nameStabilizer]

theorem nameStabilizer_subgroup {P R Γ τ : V} (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hτ : IsForcingName P τ) : IsForcingSubgroup P Γ (nameStabilizer Γ τ) := by
  refine ⟨fun π hπ ↦ (mem_sep_iff.mp hπ).1,
    mem_sep_iff.mpr ⟨hΓ.2.1, nameAction_identity hτ⟩, ?_, ?_⟩
  · intro π hπ ρ hρ
    obtain ⟨hπΓ, hπτ⟩ := mem_sep_iff.mp hπ
    obtain ⟨hρΓ, hρτ⟩ := mem_sep_iff.mp hρ
    refine mem_sep_iff.mpr ⟨hΓ.2.2.1 π hπΓ ρ hρΓ, ?_⟩
    rw [← nameAction_compose (hΓ.1 π hπΓ).1 (hΓ.1 ρ hρΓ).1 hτ, hπτ, hρτ]
  · intro π hπ
    obtain ⟨hπΓ, hπτ⟩ := mem_sep_iff.mp hπ
    have ha := hΓ.1 π hπΓ
    refine mem_sep_iff.mpr ⟨hΓ.2.2.2 π hπΓ, ?_⟩
    calc
      nameAction (converseGraph π) τ = nameAction (converseGraph π) (nameAction π τ) := congrArg _ hπτ.symm
      _ = nameAction (compose π (converseGraph π)) τ := nameAction_compose ha.1 (forcingAutomorphism_inverse ha).1 hτ
      _ = τ := by rw [forcingAutomorphism_compose_inverse ha, nameAction_identity hτ]

def IsSymmetricName (P Γ F τ : V) : Prop := IsForcingName P τ ∧ nameStabilizer Γ τ ∈ F

def IsHereditarilySymmetricName (P Γ F τ : V) : Prop :=
  IsForcingName P τ ∧ ∀ σ ∈ nameClosure τ, nameStabilizer Γ σ ∈ F

instance isSymmetricName_definable : ℒₛₑₜ-relation₄[V] IsSymmetricName := by
  unfold IsSymmetricName
  definability

instance isHereditarilySymmetricName_definable : ℒₛₑₜ-relation₄[V] IsHereditarilySymmetricName := by
  unfold IsHereditarilySymmetricName
  definability

theorem hereditarilySymmetric_symmetric {P Γ F τ : V} (hτ : IsHereditarilySymmetricName P Γ F τ) :
    IsSymmetricName P Γ F τ := ⟨hτ.1, hτ.2 τ (mem_nameClosure_self τ)⟩

theorem hereditarilySymmetric_mem_closure {P Γ F τ σ : V}
    (hτ : IsHereditarilySymmetricName P Γ F τ) (hσ : σ ∈ nameClosure τ) :
    IsHereditarilySymmetricName P Γ F σ :=
  ⟨forcingName_mem_closure hτ.1 hσ, fun υ hυ ↦ hτ.2 υ (nameClosure_mem_mono hσ υ hυ)⟩

end ZFVP
