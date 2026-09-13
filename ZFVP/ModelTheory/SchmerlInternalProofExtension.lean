import ZFVP.ModelTheory.SchmerlInternalProofs
import ZFVP.SetTheory.CountableSets

/-! Actual proof-set extension and union. These operations retain every premise
code and the exact syntactic axiom witnesses; they do not appeal to soundness. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsNode.mono {L F G n φ : V} (h : IsNode L F n φ) (hFG : F ⊆ G) :
    IsNode L G n φ := by
  obtain ⟨hn, h⟩ := h
  refine ⟨hn, ?_⟩
  rcases h with h | ⟨ψ, he, hp⟩ | ⟨f, hf, hd, he, hp⟩ | ⟨ψ, he, hp⟩ | ⟨ψ, he, hp⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨ψ, he, hFG _ hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, hd, he, fun i hi ↦ hFG _ (hp i hi)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ, he, hFG _ hp⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ψ, he, hFG _ hp⟩)))

theorem IsFragment.union {L F G : V} (hF : IsFragment L F) (hG : IsFragment L G) :
    IsFragment L (F ∪ G) := by
  refine ⟨hF.1, ?_⟩
  intro t ht
  rcases mem_union_iff.mp ht with ht | ht
  · exact ⟨(hF.2 t ht).1, (hF.2 t ht).2.mono (fun x hx ↦ mem_union_iff.mpr (Or.inl hx))⟩
  · exact ⟨(hG.2 t ht).1, (hG.2 t ht).2.mono (fun x hx ↦ mem_union_iff.mpr (Or.inr hx))⟩

theorem IsBooleanProofNode.mono {Γ Δ F G D E d : V} (h : IsBooleanProofNode Γ F D d)
    (hΓ : Γ ⊆ Δ) (hF : F ⊆ G) (hD : D ⊆ E) : IsBooleanProofNode Δ G E d := by
  obtain ⟨n, φ, hφ, h⟩ := h
  refine ⟨n, φ, hF _ hφ, ?_⟩
  rcases h with ⟨he, hp⟩ | h | ⟨p, hp, q, hq, ψ, he, hlp, hlq⟩ |
    ⟨f, g, hf, hfd, hg, hgd, he, hφ, hp⟩
  · exact Or.inl ⟨he, hΓ _ hp⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨p, hD _ hp, q, hD _ hq, ψ, he, hlp, hlq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨f, g, hf, hfd, hg, hgd, he, hφ,
      fun i hi ↦ ⟨hD _ (hp i hi).1, (hp i hi).2⟩⟩))

theorem IsCoreProofNode.mono {Γ Δ F G D E d : V} (h : IsCoreProofNode Γ F D d)
    (hΓ : Γ ⊆ Δ) (hF : F ⊆ G) (hD : D ⊆ E) : IsCoreProofNode Δ G E d := by
  rcases h with h | ⟨n, φ, hφ, he, ha⟩ | ⟨n, φ, p, hφ, hp, he, hl⟩
  · exact Or.inl (h.mono hΓ hF hD)
  · exact Or.inr (Or.inl ⟨n, φ, hF _ hφ, he, ha⟩)
  · exact Or.inr (Or.inr ⟨n, φ, p, hF _ hφ, hD _ hp, he, hl⟩)

theorem IsSubstitutionProofNode.mono {L F G D E d : V} (h : IsSubstitutionProofNode L F D d)
    (hF : F ⊆ G) (hD : D ⊆ E) : IsSubstitutionProofNode L G E d := by
  obtain ⟨H, s, φ, p, hH, hs, hφ, ht, hp, hl, he⟩ := h
  exact ⟨H, s, φ, p, hH, hs, hφ, hF _ ht, hD _ hp, hl, he⟩

theorem IsInternalProofNode.mono {L Γ Δ F G D E d : V} (h : IsInternalProofNode L Γ F D d)
    (hΓ : Γ ⊆ Δ) (hF : F ⊆ G) (hD : D ⊆ E) : IsInternalProofNode L Δ G E d := by
  rcases h with h | ⟨n, φ, hφ, he, ha⟩ | ⟨n, φ, hφ, he, ha⟩ | ⟨n, φ, hφ, he, ha⟩ |
    h | ⟨n, φ, hφ, he, ha⟩ | ⟨n, φ, hφ, he, ha⟩ | ⟨n, φ, hφ, he, ha⟩ | ⟨n, φ, hφ, he, ha⟩
  · exact Or.inl (h.mono hΓ hF hD)
  · exact Or.inr (Or.inl ⟨n, φ, hF _ hφ, he, ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, φ, hF _ hφ, he, ha⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hF _ hφ, he, ha⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.mono hF hD)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hF _ hφ, he, ha⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hF _ hφ, he, ha⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hF _ hφ, he, ha⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, φ, hF _ hφ, he, ha⟩)))))))

theorem IsInternalProof.weaken {L Γ Δ F G D : V} (h : IsInternalProof L Γ F D)
    (hG : IsFragment L G) (hΓ : Γ ⊆ Δ) (hΔ : Δ ⊆ G) (hFG : F ⊆ G) :
    IsInternalProof L Δ G D :=
  ⟨hG, hΔ, fun d hd ↦ (h.2.2 d hd).mono hΓ hFG (fun _ hx ↦ hx)⟩

theorem IsInternalProof.union {L Γ F G D E : V} (h : IsInternalProof L Γ F D)
    (k : IsInternalProof L Γ G E) : IsInternalProof L Γ (F ∪ G) (D ∪ E) := by
  have hFl : F ⊆ F ∪ G := fun _ hx ↦ mem_union_iff.mpr (Or.inl hx)
  have hGr : G ⊆ F ∪ G := fun _ hx ↦ mem_union_iff.mpr (Or.inr hx)
  refine ⟨h.1.union k.1, fun x hx ↦ hFl x (h.2.1 x hx), ?_⟩
  intro d hd
  rcases mem_union_iff.mp hd with hd | hd
  · exact (h.2.2 d hd).mono (fun _ hx ↦ hx) hFl (fun _ hx ↦ mem_union_iff.mpr (Or.inl hx))
  · exact (k.2.2 d hd).mono (fun _ hx ↦ hx) hGr (fun _ hx ↦ mem_union_iff.mpr (Or.inr hx))

end ZFVP.Infinitary.Internal
