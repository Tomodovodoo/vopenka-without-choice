import ZFVP.ModelTheory.SchmerlCodedInfinitarySemantics
import ZFVP.ModelTheory.SchmerlUniformInfinitaryTruth
import ZFVP.Syntax.ElementaryFoundationEncoding

/-! Elementary transport of represented fragment constructors. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ElementaryMap
variable (j : ZFVP.ElementaryMap V W)
@[simp] theorem map_foCode (φ : V) : j (foCode φ) = foCode (j φ) :=
  j.map_definedFunction₁ foCodeFormula foCode foCode φ
@[simp] theorem map_negCode (φ : V) : j (negCode φ) = negCode (j φ) :=
  j.map_definedFunction₁ negCodeFormula negCode negCode φ
@[simp] theorem map_conjCode (φ : V) : j (conjCode φ) = conjCode (j φ) :=
  j.map_definedFunction₁ conjCodeFormula conjCode conjCode φ
@[simp] theorem map_exsCode (φ : V) : j (exsCode φ) = exsCode (j φ) :=
  j.map_definedFunction₁ exsCodeFormula exsCode exsCode φ
@[simp] theorem map_qCode (φ : V) : j (qCode φ) = qCode (j φ) :=
  j.map_definedFunction₁ qCodeFormula qCode qCode φ
end ElementaryMap

variable {Λ : Language} {L H : V} {F : ∀ {k}, Λ.Func k → V} {R : ∀ {k}, Λ.Rel k → V}
  {C : {n : ℕ} → Formula Λ n → V} {A : Set (Σ n, Formula Λ n)}

theorem IsFragmentCoding.map_elementary (h : IsFragmentCoding L H F R C A)
    (j : ZFVP.ElementaryMap V W) :
    IsFragmentCoding (j L) (j H) (fun f ↦ j (F f)) (fun r ↦ j (R r)) (fun φ ↦ j (C φ)) A where
  fragment := (ElementaryMap.fragment_iff j L H).mpr h.fragment
  closed := h.closed
  node φ hφ := by
    rw [← j.map_numeral, ← j.map_kpair, j.map_mem_iff]
    exact h.node φ hφ
  fo φ hφ := by
    rw [h.fo φ hφ, ElementaryMap.map_foCode, j.map_encodeSemiformula]
    congr 2
    funext x
    exact x.elim
  neg φ hφ := by rw [h.neg φ hφ, ElementaryMap.map_negCode]
  conj φ hφ := by
    obtain ⟨f, hf, hd, he, hv⟩ := h.conj φ hφ
    refine ⟨j f, (j.function_iff f).mpr hf, ?_, ?_, ?_⟩
    · rw [← j.map_domain, hd, j.map_omega]
    · rw [he, ElementaryMap.map_conjCode]
    · intro i
      rw [← j.map_numeral, ← j.map_value, hv]
  exs φ hφ := by rw [h.exs φ hφ, ElementaryMap.map_exsCode]
  q φ hφ := by rw [h.q φ hφ, ElementaryMap.map_qCode]

theorem IsFragmentCoding.of_map_elementary (j : ZFVP.ElementaryMap V W)
    (h : IsFragmentCoding (j L) (j H) (fun f ↦ j (F f)) (fun r ↦ j (R r)) (fun φ ↦ j (C φ)) A) :
    IsFragmentCoding L H F R C A where
  fragment := (ElementaryMap.fragment_iff j L H).mp h.fragment
  closed := h.closed
  node φ hφ := by
    have hn := h.node φ hφ
    rw [← j.map_numeral, ← j.map_kpair, j.map_mem_iff] at hn
    exact hn
  fo φ hφ := by
    apply j.injective
    rw [ElementaryMap.map_foCode, j.map_encodeSemiformula]
    convert h.fo φ hφ using 2
    congr 1
    funext x
    exact x.elim
  neg φ hφ := by
    apply j.injective
    rw [ElementaryMap.map_negCode]
    exact h.neg φ hφ
  conj φ hφ := by
    obtain ⟨f, hf, hd, he, hv⟩ := h.conj φ hφ
    let g : V := kpair.π₂ (C (.conj φ))
    have hg : j g = f := by dsimp [g]; rw [j.map_second, he]; simp [conjCode]
    refine ⟨g, ?_, ?_, ?_, ?_⟩
    · apply (j.function_iff g).mp
      rwa [hg]
    · apply j.injective
      rw [j.map_domain, hg, hd, j.map_omega]
    · apply j.injective
      rw [ElementaryMap.map_conjCode, hg]
      exact he
    · intro i
      apply j.injective
      rw [j.map_value, hg, j.map_numeral]
      exact hv i
  exs φ hφ := by
    apply j.injective
    rw [ElementaryMap.map_exsCode]
    exact h.exs φ hφ
  q φ hφ := by
    apply j.injective
    rw [ElementaryMap.map_qCode]
    exact h.q φ hφ

theorem IsFragmentCoding.congrCode (h : IsFragmentCoding L H F R C A)
    {C' : {n : ℕ} → Formula Λ n → V}
    (he : ∀ {n} (φ : Formula Λ n), ⟨n, φ⟩ ∈ A → C' φ = C φ) :
    IsFragmentCoding L H F R C' A where
  fragment := h.fragment
  closed := h.closed
  node φ hφ := by rw [he φ hφ]; exact h.node φ hφ
  fo φ hφ := by rw [he (.fo φ) hφ]; exact h.fo φ hφ
  neg φ hφ := by rw [he (.neg φ) hφ, he φ (h.neg_mem hφ)]; exact h.neg φ hφ
  conj φ hφ := by
    obtain ⟨f, hf, hd, hc, hv⟩ := h.conj φ hφ
    refine ⟨f, hf, hd, ?_, ?_⟩
    · rw [he (.conj φ) hφ]; exact hc
    · intro i
      rw [he (φ i) (h.conj_mem hφ i)]
      exact hv i
  exs φ hφ := by rw [he (.exs φ) hφ, he φ (h.exs_mem hφ)]; exact h.exs φ hφ
  q φ hφ := by rw [he (.q φ) hφ, he φ (h.q_mem hφ)]; exact h.q φ hφ

end ZFVP.Infinitary.Internal


