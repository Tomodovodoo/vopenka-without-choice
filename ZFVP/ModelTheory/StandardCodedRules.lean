import ZFVP.ModelTheory.StandardCodedDerivations

/-! Constructors for each inference rule of a standard finite coded proof. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem StandardCodedProvable.weaken {T n Γ Δ : V} (h : StandardCodedProvable T n Δ)
    (hv : IsCodedSequent n Γ) (hsub : Δ ⊆ Γ) : StandardCodedProvable T n Γ := by
  apply h.unary hv
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨Δ, hsub, by simp⟩)))))))))

theorem StandardCodedProvable.disj {T n Γ φ ψ : V}
    (h : StandardCodedProvable T n (insert φ (insert ψ Γ)))
    (hv : IsCodedSequent n (insert (orCode φ ψ) Γ))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    StandardCodedProvable T n (insert (orCode φ ψ) Γ) := by
  apply h.unary hv
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨Γ, φ, ψ, hφ, hψ, rfl, by simp⟩))))

theorem StandardCodedProvable.conj {T n Γ φ ψ : V}
    (hp : StandardCodedProvable T n (insert φ Γ)) (hq : StandardCodedProvable T n (insert ψ Γ))
    (hv : IsCodedSequent n (insert (andCode φ ψ) Γ))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    StandardCodedProvable T n (insert (andCode φ ψ) Γ) := by
  apply hp.binary hq hv
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Γ, φ, ψ, hφ, hψ, rfl, by simp, by simp⟩)))))

theorem StandardCodedProvable.cut {T n Γ Δ φ : V}
    (hp : StandardCodedProvable T n (insert φ Γ))
    (hq : StandardCodedProvable T n (insert (negateFormula membershipLanguageCode ∅ n φ) Δ))
    (hv : IsCodedSequent n (Γ ∪ Δ)) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    StandardCodedProvable T n (Γ ∪ Δ) := by
  apply hp.binary hq hv
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨Γ, Δ, φ, hφ, rfl, by simp, by simp⟩))))))

theorem StandardCodedProvable.all {T n Γ φ : V}
    (h : StandardCodedProvable T (succ n) (insert φ (shiftCodedSequent n Γ)))
    (hv : IsCodedSequent n (insert (allCode φ) Γ))
    (hΓ : Γ ⊆ formulaSet membershipLanguageCode ∅ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) :
    StandardCodedProvable T n (insert (allCode φ) Γ) := by
  apply h.unary hv
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨Γ, φ, hΓ, hφ, rfl, by simp⟩)))))))

theorem StandardCodedProvable.exists {T n Γ φ i : V}
    (h : StandardCodedProvable T n (insert (instantiateMembershipFormula n i φ) Γ))
    (hv : IsCodedSequent n (insert (existsCode φ) Γ))
    (hi : i ∈ n) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) :
    StandardCodedProvable T n (insert (existsCode φ) Γ) := by
  apply h.unary hv
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨Γ, φ, i, hi, hφ, rfl, by simp⟩))))))))

theorem StandardCodedProvable.rename {T m n r Δ : V} (h : StandardCodedProvable T m Δ)
    (hv : IsCodedSequent n (renameCodedSequent m n r Δ)) (hr : r ∈ n ^ m) :
    StandardCodedProvable T n (renameCodedSequent m n r Δ) := by
  apply h.unary hv
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr ⟨m, r, Δ, h.valid.1, hr, h.valid.2.2, rfl, by simp⟩)))))))))

end ZFVP
