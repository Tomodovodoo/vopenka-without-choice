import ZFVP.SetTheory.PathDependentChoice
import ZFVP.SetTheory.ChoiceDictionary

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def InternalCountableChoice (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ C : V, IsFunction C → domain C = (ω : V) →
    (∀ n ∈ (ω : V), IsNonempty (C ‘ n)) →
    ∃ f ∈ (⋃ˢ range C) ^ (ω : V), ∀ n ∈ (ω : V), f ‘ n ∈ C ‘ n

theorem countableChoice_of_dependentChoice (hDC : InternalDependentChoice V) : InternalCountableChoice V := by
  intro C hC hdC hnC
  have : IsFunction C := hC
  have hCtyped : C ∈ (range C) ^ (ω : V) := by simpa only [hdC] using IsFunction.mem_function C
  let A : V := {p ∈ (ω : V) ×ˢ (⋃ˢ range C) ; kpair.π₂ p ∈ C ‘ (kpair.π₁ p)}
  have hA (n x : V) : ⟨n, x⟩ₖ ∈ A ↔ n ∈ (ω : V) ∧ x ∈ C ‘ n := by
    simp only [A, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    constructor
    · rintro ⟨⟨hn, _⟩, hx⟩
      exact ⟨hn, hx⟩
    · rintro ⟨hn, hx⟩
      exact ⟨⟨hn, mem_sUnion_iff.mpr ⟨C ‘ n, value_mem_range hCtyped hn, hx⟩⟩, hx⟩
  have hcoords (p : V) (hp : p ∈ A) : kpair.π₁ p ∈ (ω : V) ∧ kpair.π₂ p ∈ C ‘ (kpair.π₁ p) := by
    obtain ⟨n, hn, x, _, heq⟩ := mem_prod_iff.mp (mem_sep_iff.mp hp).1
    subst p
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using (hA n x).mp hp
  let R : V := {p ∈ A ×ˢ A ; kpair.π₁ (kpair.π₂ p) = succ (kpair.π₁ (kpair.π₁ p))}
  have hR (p q : V) : ⟨p, q⟩ₖ ∈ R ↔ p ∈ A ∧ q ∈ A ∧ kpair.π₁ q = succ (kpair.π₁ p) := by
    simp only [R, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  have hserial : ∀ p ∈ A, ∃ q ∈ A, ⟨p, q⟩ₖ ∈ R := by
    intro p hp
    have hn := ω_succ_closed (hcoords p hp).1
    obtain ⟨x, hx⟩ := (hnC _ hn).nonempty
    have hq : ⟨succ (kpair.π₁ p), x⟩ₖ ∈ A := (hA _ _).mpr ⟨hn, hx⟩
    exact ⟨_, hq, (hR _ _).mpr ⟨hp, hq, by simp⟩⟩
  obtain ⟨a, ha⟩ := (hnC 0 (by simp)).nonempty
  obtain ⟨g, hg, hg0, hsteps⟩ := pointedDependentChoice_of_unpointed hDC A R ⟨0, a⟩ₖ
    ((hA _ _).mpr ⟨by simp, ha⟩) hserial
  have hindex : ∀ n ∈ (ω : V), kpair.π₁ (g ‘ n) = n := by
    apply naturalNumber_induction (fun n ↦ kpair.π₁ (g ‘ n) = n) (by definability)
    · rw [hg0, kpair.π₁_kpair]
    · intro n hn ih
      rw [((hR _ _).mp (hsteps n hn)).2.2, ih]
  let f := definableGraph (ω : V) (fun n ↦ kpair.π₂ (g ‘ n)) (by definability)
  have hchoice (n : V) (hn : n ∈ (ω : V)) : kpair.π₂ (g ‘ n) ∈ C ‘ n := by
    have h := (hcoords _ (function_value_mem hg hn)).2
    simpa only [hindex n hn] using h
  refine ⟨f, definableGraph_mem_function_of_mapsTo _ _ _ _ (fun n hn ↦
    mem_sUnion_iff.mpr ⟨C ‘ n, value_mem_range hCtyped hn, hchoice n hn⟩), ?_⟩
  intro n hn
  rw [show f ‘ n = kpair.π₂ (g ‘ n) from value_definableGraph _ _ _ hn]
  exact hchoice n hn

theorem countableChoice_of_internalChoice (hAC : InternalChoice V) : InternalCountableChoice V :=
  countableChoice_of_dependentChoice (dependentChoice_of_internalChoice hAC)

theorem not_dependentChoice_of_not_countableChoice (h : ¬InternalCountableChoice V) :
    ¬InternalDependentChoice V := fun hDC ↦ h (countableChoice_of_dependentChoice hDC)

def countableChoiceSentence : SetTheorySentence :=
  f“∀ C, !IsFunction.dfn C → !domain.dfn C = !isω →
    (∀ n ∈ !isω, !isNonempty (!value.dfn C n)) →
    ∃ f ∈ !function.dfn (!sUnion.dfn (!range.dfn C)) (!isω),
      ∀ n ∈ !isω, !value.dfn f n ∈ !value.dfn C n”

instance countableChoiceSentence_defined :
    Defined (fun _ : Fin 0 → V ↦ InternalCountableChoice V) countableChoiceSentence :=
  ⟨fun v ↦ by simp [countableChoiceSentence, InternalCountableChoice]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem countableChoice_iff (j : ElementaryMap V W) : InternalCountableChoice V ↔ InternalCountableChoice W :=
  j.map_defined countableChoiceSentence (fun _ ↦ InternalCountableChoice V)
    (fun _ ↦ InternalCountableChoice W) ![]

end ElementaryMap
end ZFVP
