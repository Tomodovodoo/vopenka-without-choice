import ZFVP.SetTheory.NameClosure
import ZFVP.SetTheory.MeasuredWellFounded

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingName (P τ : V) : Prop :=
  ∀ σ ∈ nameClosure τ, ∀ z ∈ σ, ∃ υ : V, ∃ p ∈ P, z = ⟨υ, p⟩ₖ

instance isForcingName_definable : ℒₛₑₜ-relation[V] IsForcingName := by
  unfold IsForcingName
  definability

theorem forcingName_mem_closure {P τ σ : V} (hτ : IsForcingName P τ)
    (hσ : σ ∈ nameClosure τ) : IsForcingName P σ :=
  fun υ hυ ↦ hτ υ (nameClosure_mem_mono hσ υ hυ)

theorem forcingName_subname {P τ σ p : V} (hτ : IsForcingName P τ)
    (hσ : ⟨σ, p⟩ₖ ∈ τ) : IsForcingName P σ :=
  forcingName_mem_closure hτ (subname_mem_nameClosure hσ)

theorem forcingName_condition {P τ σ p : V} (hτ : IsForcingName P τ)
    (hσ : ⟨σ, p⟩ₖ ∈ τ) : p ∈ P := by
  obtain ⟨υ, q, hq, he⟩ := hτ τ (mem_nameClosure_self τ) _ hσ
  have heq : σ = υ ∧ p = q := kpair_iff.mp he
  exact heq.2 ▸ hq

theorem forcingName_iff (P τ : V) : IsForcingName P τ ↔
    ∀ z ∈ τ, ∃ σ : V, ∃ p ∈ P, z = ⟨σ, p⟩ₖ ∧ IsForcingName P σ := by
  constructor
  · intro h z hz
    obtain ⟨σ, p, hp, he⟩ := h τ (mem_nameClosure_self τ) z hz
    exact ⟨σ, p, hp, he, forcingName_subname h (he ▸ hz)⟩
  · intro h
    let C := nameClosure τ
    let X : V := {σ ∈ C ; σ = τ ∨ IsForcingName P σ}
    have hτX : τ ∈ X := mem_sep_iff.mpr ⟨mem_nameClosure_self τ, Or.inl rfl⟩
    have hXC : IsSubnameClosed X := by
      intro σ hσ υ hυ
      obtain ⟨hσC, hσN⟩ := mem_sep_iff.mp hσ
      obtain ⟨p, hυp⟩ := mem_domain_iff.mp hυ
      refine mem_sep_iff.mpr ⟨nameClosure_closed τ σ hσC υ (mem_domain_of_kpair_mem hυp), Or.inr ?_⟩
      rcases hσN with rfl | hσN
      · obtain ⟨ν, q, _, he, hν⟩ := h _ hυp
        exact (kpair_iff.mp he).1 ▸ hν
      · exact forcingName_subname hσN hυp
    have hCX := nameClosure_minimal hXC hτX
    intro σ hσ z hz
    rcases (mem_sep_iff.mp (hCX σ hσ)).2 with rfl | hσN
    · obtain ⟨υ, p, hp, he, _⟩ := h z hz
      exact ⟨υ, p, hp, he⟩
    · exact hσN σ (mem_nameClosure_self σ) z hz

theorem empty_forcingName (P : V) : IsForcingName P ∅ := by
  apply (forcingName_iff P ∅).mpr
  intro z hz
  exact False.elim (not_mem_empty hz)

theorem forcingName_pair {P σ τ p : V} (hσ : IsForcingName P σ)
    (hτ : IsForcingName P τ) (hp : p ∈ P) :
    IsForcingName P ({⟨σ, p⟩ₖ, ⟨τ, p⟩ₖ} : V) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  rcases show z = ⟨σ, p⟩ₖ ∨ z = ⟨τ, p⟩ₖ from by simpa using hz with rfl | rfl
  · exact ⟨σ, p, hp, rfl, hσ⟩
  · exact ⟨τ, p, hp, rfl, hτ⟩

theorem forcingName_induction (P : V) (Q : V → Prop) (hQ : ℒₛₑₜ-predicate Q)
    (step : ∀ τ : V, IsForcingName P τ →
      (∀ σ : V, ∀ p : V, ⟨σ, p⟩ₖ ∈ τ → Q σ) → Q τ) :
    ∀ τ : V, IsForcingName P τ → Q τ := by
  intro τ hτ
  have hi := projectedRank_induction (nameClosure τ) (fun x : V ↦ x) (by definability)
    Q hQ (fun σ hσ ih ↦ step σ (forcingName_mem_closure hτ hσ)
      (fun υ p hυ ↦ ih υ (nameClosure_closed τ σ hσ υ (mem_domain_of_kpair_mem hυ))
        (rank_subname_lt hυ)))
  exact hi τ (mem_nameClosure_self τ)

end ZFVP
