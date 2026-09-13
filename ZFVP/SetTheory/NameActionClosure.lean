import ZFVP.SetTheory.NameAction
import ZFVP.SetTheory.CheckNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameClosure_nameAction {P τ : V} (hτ : IsForcingName P τ) (π : V) :
    nameClosure (nameAction π τ) = repl (nameAction π) (by definability) (nameClosure τ) := by
  let I := repl (nameAction π) (by definability) (nameClosure τ)
  have hi : nameAction π τ ∈ I := (repl_spec (by definability)).mpr ⟨τ, mem_nameClosure_self τ, rfl⟩
  have hI : IsSubnameClosed I := by
    intro υ hυ ν hν
    obtain ⟨σ, hσ, rfl⟩ := (repl_spec (by definability)).mp hυ
    obtain ⟨q, hνq⟩ := mem_domain_iff.mp hν
    obtain ⟨ξ, p, hξp, he⟩ := (mem_nameAction_iff (forcingName_mem_closure hτ hσ) π _).mp hνq
    exact (repl_spec (by definability)).mpr
      ⟨ξ, nameClosure_closed τ σ hσ ξ (mem_domain_of_kpair_mem hξp), (kpair_iff.mp he).1⟩
  apply SetTheory.subset_antisymm (nameClosure_minimal hI hi)
  let C := nameClosure (nameAction π τ)
  let X : V := {σ ∈ nameClosure τ ; nameAction π σ ∈ C}
  have hτX : τ ∈ X := mem_sep_iff.mpr ⟨mem_nameClosure_self τ, mem_nameClosure_self _⟩
  have hX : IsSubnameClosed X := by
    intro σ hσ ν hν
    obtain ⟨hσC, hσA⟩ := mem_sep_iff.mp hσ
    obtain ⟨p, hp⟩ := mem_domain_iff.mp hν
    have hn : ⟨nameAction π ν, π ‘ p⟩ₖ ∈ nameAction π σ :=
      (mem_nameAction_iff (forcingName_mem_closure hτ hσC) π _).mpr ⟨ν, p, hp, rfl⟩
    exact mem_sep_iff.mpr ⟨nameClosure_closed τ σ hσC ν (mem_domain_of_kpair_mem hp),
      nameClosure_closed _ _ hσA _ (mem_domain_of_kpair_mem hn)⟩
  intro ν hν
  obtain ⟨σ, hσ, rfl⟩ := (repl_spec (by definability)).mp hν
  exact (mem_sep_iff.mp (nameClosure_minimal hX hτX σ hσ)).2

theorem nameAction_empty (π : V) : nameAction π ∅ = ∅ := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  simp [mem_nameAction_iff (empty_forcingName (∅ : V))]

theorem nameAction_pair {P σ τ p : V} (hσ : IsForcingName P σ)
    (hτ : IsForcingName P τ) (hp : p ∈ P) (π : V) :
    nameAction π ({⟨σ, p⟩ₖ, ⟨τ, p⟩ₖ} : V) =
      ({⟨nameAction π σ, π ‘ p⟩ₖ, ⟨nameAction π τ, π ‘ p⟩ₖ} : V) := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  simp only [mem_nameAction_iff (forcingName_pair hσ hτ hp), mem_insert, mem_singleton_iff, kpair_iff]
  constructor
  · rintro ⟨υ, q, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨σ, p, Or.inl ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨τ, p, Or.inr ⟨rfl, rfl⟩, rfl⟩

theorem nameAction_checkName {P one π : V} (hone : one ∈ P) (hfix : π ‘ one = one) (x : V) :
    nameAction π (checkName one x) = checkName one x := by
  apply set_induction (fun x ↦ nameAction π (checkName one x) = checkName one x) (by definability) ?_ x
  intro x ih
  apply SetTheory.mem_ext_iff.mpr
  intro z
  rw [mem_nameAction_iff (checkName_isName hone x), mem_checkName_iff]
  constructor
  · rintro ⟨σ, p, hp, hz⟩
    obtain ⟨y, hy, he⟩ := (mem_checkName_iff one x _).mp hp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨y, hy, by simpa only [ih y hy, hfix] using hz⟩
  · rintro ⟨y, hy, hz⟩
    refine ⟨checkName one y, one, (mem_checkName_iff one x _).mpr ⟨y, hy, rfl⟩, ?_⟩
    simpa only [ih y hy, hfix] using hz

end ZFVP
