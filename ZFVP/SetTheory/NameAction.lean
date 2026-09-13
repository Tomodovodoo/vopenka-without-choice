import ZFVP.SetTheory.SubnameRecursion
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def nameActionStep (π τ g : V) : V :=
  repl (fun z ↦ ⟨g ‘ (kpair.π₁ z), π ‘ (kpair.π₂ z)⟩ₖ) (by definability) τ

instance nameActionStep_definable : ℒₛₑₜ-function₃[V] nameActionStep := by
  have h : ℒₛₑₜ-relation₄ (fun C π τ g : V ↦ ∀ z, z ∈ C ↔
      ∃ w ∈ τ, z = ⟨g ‘ (kpair.π₁ w), π ‘ (kpair.π₂ w)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameActionStep (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp [nameActionStep, repl_spec]

noncomputable def nameAction (π τ : V) : V :=
  subnameRecursion (nameActionStep π) (by definability) τ

theorem nameAction_eq_iff (π τ y : V) : y = nameAction π τ ↔
    ∃ f, IsSubnameRecursion (nameClosure τ) (nameActionStep π) f ∧ y = f ‘ τ := by
  constructor
  · rintro rfl
    exact ⟨subnameRecursionTable (nameActionStep π) (by definability) τ,
      subnameRecursionTable_spec _ _ _, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    have he := (subnameRecursionTable_eq_iff (nameActionStep π) (by definability) τ f).mpr hf
    exact congrArg (fun g ↦ g ‘ τ) he

instance nameAction_definable : ℒₛₑₜ-function₂[V] nameAction := by
  have h : ℒₛₑₜ-relation₃ (fun y π τ : V ↦
      ∃ f, IsSubnameRecursion (nameClosure τ) (nameActionStep π) f ∧ y = f ‘ τ) := by
    unfold IsSubnameRecursion
    definability
  apply Language.Definable.of_iff h
  intro v
  exact nameAction_eq_iff (v 1) (v 2) (v 0)

theorem mem_nameAction_iff {P τ : V} (hτ : IsForcingName P τ) (π z : V) :
    z ∈ nameAction π τ ↔ ∃ σ : V, ∃ p : V, ⟨σ, p⟩ₖ ∈ τ ∧ z = ⟨nameAction π σ, π ‘ p⟩ₖ := by
  rw [nameAction, subnameRecursion_equation]
  change z ∈ nameActionStep π τ (definableGraph (domain τ) (nameAction π) (by definability)) ↔ _
  simp only [nameActionStep, repl_spec]
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨σ, p, _, rfl⟩ := hτ τ (mem_nameClosure_self τ) w hw
    exact ⟨σ, p, hw, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair,
      value_definableGraph _ _ _ (mem_domain_of_kpair_mem hw)] using he⟩
  · rintro ⟨σ, p, hp, he⟩
    refine ⟨(⟨σ, p⟩ₖ : V), hp, ?_⟩
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair,
      value_definableGraph _ _ _ (mem_domain_of_kpair_mem hp)] using he

theorem nameAction_isName {P Q π : V} (hπ : π ∈ Q ^ P) {τ : V} (hτ : IsForcingName P τ) :
    IsForcingName Q (nameAction π τ) := by
  apply forcingName_induction P (fun τ ↦ IsForcingName Q (nameAction π τ)) (by definability) ?_ τ hτ
  intro τ hτ ih
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨σ, p, hp, rfl⟩ := (mem_nameAction_iff hτ π z).mp hz
  exact ⟨nameAction π σ, π ‘ p, function_value_mem hπ (forcingName_condition hτ hp), rfl, ih σ p hp⟩

theorem nameAction_identity {P τ : V} (hτ : IsForcingName P τ) : nameAction (identity P) τ = τ := by
  have hi (p : V) (hp : p ∈ P) : (identity P) ‘ p = p :=
    value_eq_of_kpair_mem (kpair_mem_identity_iff.mpr ⟨hp, rfl⟩)
  apply forcingName_induction P (fun τ ↦ nameAction (identity P) τ = τ) (by definability) ?_ τ hτ
  intro τ hτ ih
  apply SetTheory.mem_ext_iff.mpr
  intro z
  rw [mem_nameAction_iff hτ]
  constructor
  · rintro ⟨σ, p, hp, rfl⟩
    simpa only [ih σ p hp, hi p (forcingName_condition hτ hp)] using hp
  · intro hz
    obtain ⟨σ, p, hp, rfl⟩ := hτ τ (mem_nameClosure_self τ) z hz
    exact ⟨σ, p, hz, by rw [ih σ p hz, hi p hp]⟩

theorem nameAction_compose {P Q S π ρ : V} (hπ : π ∈ Q ^ P) (hρ : ρ ∈ S ^ Q)
    {τ : V} (hτ : IsForcingName P τ) :
    nameAction ρ (nameAction π τ) = nameAction (compose π ρ) τ := by
  have : IsFunction π := IsFunction.of_mem hπ
  have : IsFunction ρ := IsFunction.of_mem hρ
  have : IsFunction (compose π ρ) := IsFunction.of_mem (compose_function hπ hρ)
  have hc (p : V) (hp : p ∈ P) : (compose π ρ) ‘ p = ρ ‘ (π ‘ p) := by
    apply value_eq_of_kpair_mem
    apply kpair_mem_compose_iff.mpr
    exact ⟨π ‘ p, kpair_value_mem (by simpa only [domain_eq_of_mem_function hπ] using hp),
      kpair_value_mem (by simpa only [domain_eq_of_mem_function hρ] using function_value_mem hπ hp)⟩
  apply forcingName_induction P (fun τ ↦ nameAction ρ (nameAction π τ) = nameAction (compose π ρ) τ)
    (by definability) ?_ τ hτ
  intro τ hτ ih
  apply SetTheory.mem_ext_iff.mpr
  intro z
  rw [mem_nameAction_iff (nameAction_isName hπ hτ), mem_nameAction_iff hτ]
  constructor
  · rintro ⟨υ, q, hυq, hz⟩
    obtain ⟨σ, p, hp, he⟩ := (mem_nameAction_iff hτ π _).mp hυq
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨σ, p, hp, by simpa only [ih σ p hp, hc p (forcingName_condition hτ hp)] using hz⟩
  · rintro ⟨σ, p, hp, hz⟩
    refine ⟨nameAction π σ, π ‘ p, (mem_nameAction_iff hτ π _).mpr ⟨σ, p, hp, rfl⟩, ?_⟩
    simpa only [ih σ p hp, hc p (forcingName_condition hτ hp)] using hz

end ZFVP
