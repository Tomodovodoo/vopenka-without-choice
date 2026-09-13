import ZFVP.SetTheory.SubnameRecursion
import ZFVP.SetTheory.CheckNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The filter parameter belongs to the ambient model, which can contain a
smaller transitive ground model. -/
noncomputable def nameValueStep (G τ f : V) : V :=
  repl (fun σ ↦ f ‘ σ) (by definability) {σ ∈ domain τ ; ∃ p ∈ G, ⟨σ, p⟩ₖ ∈ τ}

theorem mem_nameValueStep_iff (G τ f z : V) :
    z ∈ nameValueStep G τ f ↔ ∃ σ : V, ∃ p ∈ G, ⟨σ, p⟩ₖ ∈ τ ∧ z = f ‘ σ := by
  simp only [nameValueStep, repl_spec, mem_sep_iff]
  constructor
  · rintro ⟨σ, ⟨_, p, hp, hσp⟩, he⟩
    exact ⟨σ, p, hp, hσp, he⟩
  · rintro ⟨σ, p, hp, hσp, he⟩
    exact ⟨σ, ⟨mem_domain_of_kpair_mem hσp, p, hp, hσp⟩, he⟩

instance nameValueStep_definable : ℒₛₑₜ-function₃[V] nameValueStep := by
  have h : ℒₛₑₜ-relation₄ (fun C G τ f : V ↦ ∀ z, z ∈ C ↔
      ∃ σ : V, ∃ p ∈ G, ⟨σ, p⟩ₖ ∈ τ ∧ z = f ‘ σ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameValueStep (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [mem_nameValueStep_iff]

noncomputable def nameValue (G τ : V) : V :=
  subnameRecursion (nameValueStep G) (by definability) τ

theorem nameValue_eq_iff (G τ y : V) : y = nameValue G τ ↔
    ∃ f, IsSubnameRecursion (nameClosure τ) (nameValueStep G) f ∧ y = f ‘ τ := by
  constructor
  · rintro rfl
    exact ⟨subnameRecursionTable (nameValueStep G) (by definability) τ,
      subnameRecursionTable_spec _ _ _, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    have he := (subnameRecursionTable_eq_iff (nameValueStep G) (by definability) τ f).mpr hf
    exact congrArg (fun g ↦ g ‘ τ) he

instance nameValue_definable : ℒₛₑₜ-function₂[V] nameValue := by
  have h : ℒₛₑₜ-relation₃ (fun y G τ : V ↦
      ∃ f, IsSubnameRecursion (nameClosure τ) (nameValueStep G) f ∧ y = f ‘ τ) := by
    unfold IsSubnameRecursion
    definability
  apply Language.Definable.of_iff h
  intro v
  exact nameValue_eq_iff (v 1) (v 2) (v 0)

theorem mem_nameValue_iff (G τ z : V) :
    z ∈ nameValue G τ ↔ ∃ σ : V, ∃ p ∈ G, ⟨σ, p⟩ₖ ∈ τ ∧ z = nameValue G σ := by
  rw [nameValue, subnameRecursion_equation]
  change z ∈ nameValueStep G τ (definableGraph (domain τ) (nameValue G) (by definability)) ↔ _
  rw [mem_nameValueStep_iff]
  constructor
  · rintro ⟨σ, p, hp, hσp, he⟩
    exact ⟨σ, p, hp, hσp, by simpa only [value_definableGraph _ _ _ (mem_domain_of_kpair_mem hσp)] using he⟩
  · rintro ⟨σ, p, hp, hσp, he⟩
    exact ⟨σ, p, hp, hσp, by simpa only [value_definableGraph _ _ _ (mem_domain_of_kpair_mem hσp)] using he⟩

theorem nameValue_empty (G : V) : nameValue G ∅ = ∅ := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  simp [mem_nameValue_iff]

theorem nameValue_checkName {one G : V} (hone : one ∈ G) (x : V) :
    nameValue G (checkName one x) = x := by
  apply set_induction (fun x ↦ nameValue G (checkName one x) = x) (by definability) ?_ x
  intro x ih
  apply SetTheory.mem_ext_iff.mpr
  intro z
  rw [mem_nameValue_iff]
  constructor
  · rintro ⟨σ, p, _, hσp, he⟩
    obtain ⟨y, hy, hpair⟩ := (mem_checkName_iff one x _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hpair
    rw [ih y hy] at he
    exact he ▸ hy
  · intro hz
    exact ⟨checkName one z, one, hone, (mem_checkName_iff one x _).mpr ⟨z, hz, rfl⟩, (ih z hz).symm⟩

theorem nameValue_pair {G p : V} (hp : p ∈ G) (σ τ : V) :
    nameValue G ({⟨σ, p⟩ₖ, ⟨τ, p⟩ₖ} : V) = ({nameValue G σ, nameValue G τ} : V) := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  simp only [mem_nameValue_iff, mem_insert, mem_singleton_iff, kpair_iff]
  constructor
  · rintro ⟨υ, q, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨σ, p, hp, Or.inl ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨τ, p, hp, Or.inr ⟨rfl, rfl⟩, rfl⟩

end ZFVP
