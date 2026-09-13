import ZFVP.SetTheory.ForcingClosure
import ZFVP.SetTheory.DependentChoiceSerialPaths
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Dependent choice with a prescribed stage bound for each value. Closure
is used at the current stage; the next witness may belong to the next stage.
All carriers, orders and witness sets are internal sets. -/
theorem stagedForcingDependentChoice {A R B D α p : V} [IsOrdinal α]
    (hR : IsForcingPreorder A R) (hDC : InternalDependentChoiceAt α)
    (hB : ∀ β, IsOrdinal β → β ⊆ α → B ‘ β ⊆ A)
    (hmono : ∀ β γ, IsOrdinal β → IsOrdinal γ → β ⊆ γ → γ ⊆ α → B ‘ β ⊆ B ‘ γ)
    (hp : p ∈ B ‘ ∅)
    (hclosed : ∀ β, IsOrdinal β → β ⊆ α → IsForcingClosedAt (B ‘ β) R β)
    (hnext : ∀ β ∈ α, ∀ q ∈ B ‘ β,
      ∃ r ∈ B ‘ (succ β), r ∈ D ‘ β ∧ ⟨r, q⟩ₖ ∈ R) :
    ∃ f, f ∈ A ^ α ∧
      (∀ β ∈ α, f ‘ β ∈ B ‘ (succ β) ∧ f ‘ β ∈ D ‘ β) ∧
      IsForcingDescending A R α f ∧
      ∃ q ∈ B ‘ α, ⟨q, p⟩ₖ ∈ R ∧ ∀ β ∈ α, ⟨q, f ‘ β⟩ₖ ∈ R := by
  classical
  have hpA := hB ∅ inferInstance (empty_subset _) p hp
  have hsle {β γ : V} [IsOrdinal γ] (h : β ∈ γ) : succ β ⊆ γ := by
    intro x hx
    rcases mem_succ_iff.mp hx with rfl | hx
    · exact h
    · exact IsOrdinal.toIsTransitive.mem_trans hx h
  let Q : V := {z ∈ shorterSequences α A ×ˢ A ;
    kpair.π₂ z ∈ B ‘ (succ (domain (kpair.π₁ z))) ∧
    kpair.π₂ z ∈ D ‘ (domain (kpair.π₁ z)) ∧
    ⟨kpair.π₂ z, p⟩ₖ ∈ R ∧
    ∀ ξ ∈ domain (kpair.π₁ z), ⟨kpair.π₂ z, (kpair.π₁ z) ‘ ξ⟩ₖ ∈ R}
  have hQ (s q : V) : ⟨s, q⟩ₖ ∈ Q ↔ s ∈ shorterSequences α A ∧ q ∈ A ∧
      q ∈ B ‘ (succ (domain s)) ∧ q ∈ D ‘ (domain s) ∧ ⟨q, p⟩ₖ ∈ R ∧
      ∀ ξ ∈ domain s, ⟨q, s ‘ ξ⟩ₖ ∈ R := by
    simp only [Q, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  have progress {β s : V} [IsOrdinal β] (hs : IsDependentChoicePath A Q β s) :
      ∀ ξ ∈ β, s ‘ ξ ∈ B ‘ (succ ξ) ∧ s ‘ ξ ∈ D ‘ ξ ∧ ⟨s ‘ ξ, p⟩ₖ ∈ R ∧
        ∀ η ∈ ξ, ⟨s ‘ ξ, s ‘ η⟩ₖ ∈ R := by
    let := IsFunction.of_mem hs.1
    intro ξ hξ
    have hξβ := IsOrdinal.toIsTransitive.transitive _ hξ
    have hsf := function_restrict_mem hs.1 hξβ
    have hh := ((hQ _ _).mp (hs.2 ξ hξ)).2.2
    rw [domain_eq_of_mem_function hsf] at hh
    refine ⟨hh.1, hh.2.1, hh.2.2.1, ?_⟩
    intro η hη
    simpa only [value_restrict (by rw [domain_eq_of_mem_function hs.1]; exact hξβ η hη) hη]
      using hh.2.2.2 η hη
  have lower {β s : V} [IsOrdinal β] (hβα : β ⊆ α)
      (hs : IsDependentChoicePath A Q β s) :
      ∃ q ∈ B ‘ β, ⟨q, p⟩ₖ ∈ R ∧ ∀ ξ ∈ β, ⟨q, s ‘ ξ⟩ₖ ∈ R := by
    have hg := progress hs
    let := IsFunction.of_mem hs.1
    have hmap : s ∈ (B ‘ β) ^ β := by
      have h := restrict_mem_function_of_values
        (f := s) (A := β) (by rw [domain_eq_of_mem_function hs.1]) (B := B ‘ β) (fun ξ hξ ↦ by
        have : IsOrdinal ξ := IsOrdinal.of_mem hξ
        exact hmono (succ ξ) β inferInstance inferInstance (hsle hξ) hβα _ (hg ξ hξ).1)
      simpa only [IsFunction.restrict_eq_self s β (by rw [domain_eq_of_mem_function hs.1])] using h
    by_cases hn : ∃ ξ, ξ ∈ β
    · obtain ⟨ξ, hξ⟩ := hn
      obtain ⟨q, hq, hqs⟩ := hclosed β inferInstance hβα s ⟨hmap, fun ξ hξ ↦ (hg ξ hξ).2.2.2⟩
      exact ⟨q, hq, hR.2.2 q (hB β inferInstance hβα q hq)
        (s ‘ ξ) (function_value_mem hs.1 hξ) p hpA (hqs ξ hξ) (hg ξ hξ).2.2.1, hqs⟩
    · exact ⟨p, hmono ∅ β inferInstance inferInstance (empty_subset _) hβα p hp,
        hR.2.1 p hpA, fun ξ hξ ↦ False.elim (hn ⟨ξ, hξ⟩)⟩
  have serial : ∀ s ∈ shorterSequences α A,
      IsDependentChoicePath A Q (domain s) s → ∃ q ∈ A, ⟨s, q⟩ₖ ∈ Q := by
    intro s hs hpath
    have hd := ((mem_shorterSequences_domain _ _ _).mp hs).1
    have : IsOrdinal (domain s) := IsOrdinal.of_mem hd
    obtain ⟨q, hq, hqp, hqs⟩ := lower (IsOrdinal.toIsTransitive.transitive _ hd) hpath
    obtain ⟨r, hr, hrD, hrq⟩ := hnext _ hd q hq
    have hrA := hB _ inferInstance (hsle hd) r hr
    have hqA := hB _ inferInstance (IsOrdinal.toIsTransitive.transitive _ hd) q hq
    exact ⟨r, hrA, (hQ s r).mpr ⟨hs, hrA, hr, hrD,
      hR.2.2 r hrA q hqA p hpA hrq hqp, fun ξ hξ ↦
        hR.2.2 r hrA q hqA (s ‘ ξ) (function_value_mem hpath.1 hξ) hrq (hqs ξ hξ)⟩⟩
  obtain ⟨f, hf⟩ := dependentChoicePath_of_serial_paths hDC ⟨p, hpA⟩ serial
  have hg := progress hf
  exact ⟨f, hf.1, fun β hβ ↦ ⟨(hg β hβ).1, (hg β hβ).2.1⟩,
    ⟨hf.1, fun β hβ ↦ (hg β hβ).2.2.2⟩, lower (subset_refl _) hf⟩

end ZFVP
