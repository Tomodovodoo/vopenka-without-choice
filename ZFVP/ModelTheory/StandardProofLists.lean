import ZFVP.ModelTheory.OpenCodedSequentSoundness
import ZFVP.Syntax.StandardLists

/-! Finite proof lists and their exact realization by the internal proof checker. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCodedSequentRule.mono {T P Q n Γ : V} (h : IsCodedSequentRule T P n Γ)
    (hPQ : P ⊆ Q) : IsCodedSequentRule T Q n Γ := by
  rcases h with h | h | h | ⟨Δ, φ, ψ, hφ, hψ, he, hp⟩ |
    ⟨Δ, φ, ψ, hφ, hψ, he, hp, hq⟩ | ⟨Δ, Ξ, φ, hφ, he, hp, hq⟩ |
    ⟨Δ, φ, hΔ, hφ, he, hp⟩ | ⟨Δ, φ, i, hi, hφ, he, hp⟩ |
    ⟨Δ, hΔ, hp⟩ | ⟨m, r, Δ, hm, hr, hΔ, he, hp⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Δ, φ, ψ, hφ, hψ, he, hPQ _ hp⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Δ, φ, ψ, hφ, hψ, he, hPQ _ hp, hPQ _ hq⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Δ, Ξ, φ, hφ, he, hPQ _ hp, hPQ _ hq⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Δ, φ, hΔ, hφ, he, hPQ _ hp⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Δ, φ, i, hi, hφ, he, hPQ _ hp⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Δ, hΔ, hPQ _ hp⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, r, Δ, hm, hr, hΔ, he, hPQ _ hp⟩))))))))

theorem IsOpenCodedSequentRule.mono {T P Q n Γ : V} (h : IsOpenCodedSequentRule T P n Γ)
    (hPQ : P ⊆ Q) : IsOpenCodedSequentRule T Q n Γ := by
  rcases h with h | h
  · exact Or.inl (h.mono hPQ)
  · exact Or.inr h

def IsOpenCodedProofList (T : V) (xs : List V) : Prop :=
  ∀ i : Fin xs.length, ∃ n Γ, xs.get i = ⟨n, Γ⟩ₖ ∧ IsCodedSequent n Γ ∧
    IsOpenCodedSequentRule T (standardListSet (xs.take i.val)) n Γ

theorem IsOpenCodedProofList.append {T : V} {xs ys : List V}
    (hx : IsOpenCodedProofList T xs) (hy : IsOpenCodedProofList T ys) :
    IsOpenCodedProofList T (xs ++ ys) := by
  intro i
  by_cases hi : i.val < xs.length
  · obtain ⟨n, Γ, he, hv, hr⟩ := hx ⟨i.val, hi⟩
    refine ⟨n, Γ, ?_, hv, hr.mono (standardListSet_mono ?_)⟩
    · simpa [List.get_eq_getElem, List.getElem_append_left hi] using he
    · intro x hx
      rw [List.take_append]
      exact List.mem_append_left _ hx
  · have hj : i.val - xs.length < ys.length := by have := i.isLt; simp only [List.length_append] at this; omega
    obtain ⟨n, Γ, he, hv, hr⟩ := hy ⟨i.val - xs.length, hj⟩
    refine ⟨n, Γ, ?_, hv, hr.mono (standardListSet_mono ?_)⟩
    · simpa [List.get_eq_getElem, List.getElem_append_right (Nat.le_of_not_gt hi)] using he
    · intro x hx
      rw [List.take_append]
      exact List.mem_append_right _ hx

theorem isOpenCodedProofList_nil (T : V) : IsOpenCodedProofList T [] := by
  intro i
  exact Fin.elim0 i

theorem IsOpenCodedProofList.snoc {T n Γ : V} {xs : List V}
    (hx : IsOpenCodedProofList T xs) (hv : IsCodedSequent n Γ)
    (hr : IsOpenCodedSequentRule T (standardListSet xs) n Γ) :
    IsOpenCodedProofList T (xs ++ [⟨n, Γ⟩ₖ]) := by
  intro i
  by_cases hi : i.val < xs.length
  · obtain ⟨m, Δ, he, hvalid, hstep⟩ := hx ⟨i.val, hi⟩
    refine ⟨m, Δ, ?_, hvalid, hstep.mono (standardListSet_mono ?_)⟩
    · simpa [List.get_eq_getElem, List.getElem_append_left hi] using he
    · intro x hx
      rw [List.take_append]
      exact List.mem_append_left _ hx
  · have heq : i.val = xs.length := by have := i.isLt; simp only [List.length_append, List.length_singleton] at this; omega
    refine ⟨n, Γ, ?_, hv, ?_⟩
    · simp [List.get_eq_getElem, heq]
    · simpa [heq] using hr

theorem IsOpenCodedProofList.to_internal {T n Γ : V} {xs : List V}
    (hx : IsOpenCodedProofList T (xs ++ [⟨n, Γ⟩ₖ])) :
    IsOpenCodedSequentProof T (standardList (xs ++ [⟨n, Γ⟩ₖ])) n Γ := by
  refine ⟨inferInstance, (xs.length : V), by simp, ?_, ?_, ?_⟩
  · simp [num_succ_def]
  · have h := value_standardList (xs ++ [⟨n, Γ⟩ₖ]) ⟨xs.length, by simp⟩
    simpa using h
  · intro i hi
    rw [domain_standardList, mem_natCast_iff] at hi
    obtain ⟨j, rfl⟩ := hi
    obtain ⟨m, Δ, he, hv, hr⟩ := hx j
    exact ⟨m, Δ, (value_standardList _ j).trans he, hv,
      (range_restrict_standardList (xs ++ [⟨n, Γ⟩ₖ]) j.val).symm ▸ hr⟩

end ZFVP
