import ZFVP.ModelTheory.SchmerlCodedInfinitarySemantics
import ZFVP.ModelTheory.SchmerlInternalInfinitaryTransport
import ZFVP.Syntax.EndExtensionFoundationEncoding

/-! A membership end extension preserves actual represented infinitary
fragments, including every internal conjunction entry. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace EndExtension
variable (j : MembershipEndExtension V W)

theorem node_map {L H n φ : V} (hL : IsLanguageCode L) (hφ : IsNode L H n φ) :
    IsNode (j L) (j H) (j n) (j φ) := by
  refine ⟨(j.natural_iff n).mpr hφ.1, ?_⟩
  rcases hφ.2 with ⟨ψ, hψ, rfl⟩ | ⟨ψ, rfl, hψ⟩ | ⟨f, hf, hd, rfl, hψ⟩ |
    ⟨ψ, rfl, hψ⟩ | ⟨ψ, rfl, hψ⟩
  · refine Or.inl ⟨j ψ, ?_, map_foCode j ψ⟩
    rw [← j.map_empty, ← j.map_formulaSet hL, j.mem_iff]
    exact hψ
  · refine Or.inr (Or.inl ⟨j ψ, map_negCode j ψ, ?_⟩)
    rw [← j.map_kpair, j.mem_iff]
    exact hψ
  · let := hf
    refine Or.inr (Or.inr (Or.inl ⟨j f, j.map_function f, ?_, map_conjCode j f, ?_⟩))
    · rw [← j.map_domain, hd, j.map_omega]
    · intro i hi
      rw [← j.map_omega] at hi
      obtain ⟨k, hk, rfl⟩ := j.endExtension ω i hi
      rw [← j.map_value_total, ← j.map_kpair, j.mem_iff]
      exact hψ k hk
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨j ψ, map_exsCode j ψ, ?_⟩)))
    rw [← j.map_succ, ← j.map_kpair, j.mem_iff]
    exact hψ
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨j ψ, map_qCode j ψ, ?_⟩)))
    rw [← j.map_succ, ← j.map_kpair, j.mem_iff]
    exact hψ

theorem fragment_map {L H : V} (h : IsFragment L H) : IsFragment (j L) (j H) := by
  refine ⟨(j.languageCode_iff L).mpr h.1, ?_⟩
  intro q hq
  obtain ⟨p, hp, rfl⟩ := j.endExtension H q hq
  have he := (h.2 p hp).1
  have hn := (h.2 p hp).2
  rw [← j.map_first, ← j.map_second]
  exact ⟨(congrArg j he).trans (j.map_kpair _ _), node_map j h.1 hn⟩

end EndExtension

variable {Λ : Language} {L H : V} {F : ∀ {k}, Λ.Func k → V} {R : ∀ {k}, Λ.Rel k → V}
  {C : {n : ℕ} → Formula Λ n → V} {A : Set (Σ n, Formula Λ n)}

theorem IsFragmentCoding.map_endExtension (h : IsFragmentCoding L H F R C A)
    (j : MembershipEndExtension V W) :
    IsFragmentCoding (j L) (j H) (fun f ↦ j (F f)) (fun r ↦ j (R r))
      (fun φ ↦ j (C φ)) A where
  fragment := EndExtension.fragment_map j h.fragment
  closed := h.closed
  node φ hφ := by
    rw [← j.map_numeral, ← j.map_kpair, j.mem_iff]
    exact h.node φ hφ
  fo φ hφ := by
    rw [h.fo φ hφ, EndExtension.map_foCode, j.map_encodeSemiformula]
    congr 2
    funext x
    exact x.elim
  neg φ hφ := by rw [h.neg φ hφ, EndExtension.map_negCode]
  conj φ hφ := by
    obtain ⟨f, hf, hd, he, hv⟩ := h.conj φ hφ
    let := hf
    refine ⟨j f, j.map_function f, ?_, ?_, ?_⟩
    · rw [← j.map_domain, hd, j.map_omega]
    · rw [he, EndExtension.map_conjCode]
    · intro i
      rw [← j.map_numeral, ← j.map_value_total, hv]
  exs φ hφ := by rw [h.exs φ hφ, EndExtension.map_exsCode]
  q φ hφ := by rw [h.q φ hφ, EndExtension.map_qCode]

end ZFVP.Infinitary.Internal

