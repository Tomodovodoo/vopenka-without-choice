import ZFVP.Syntax.StandardTuples
import ZFVP.Syntax.Formulas

/-! Constructor-preserving encoding of Foundation's standard finite syntax.
Symbol maps specify the representation of the external language in an internal
language code. No surjectivity onto a nonstandard model's syntax is asserted. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language} {ξ : Type*}

noncomputable def encodeSemiterm (F : ∀ {k}, Λ.Func k → V) (e : ξ → V)
    {n : ℕ} : Semiterm Λ ξ n → V
  | .bvar i => boundVarCode (i.val : V)
  | .fvar x => freeVarCode (e x)
  | .func f ts => functionTermCode (F f) (standardTuple (fun i ↦ encodeSemiterm F e (ts i)))

theorem encodeSemiterm_mem {L Γ : V} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → V) (e : ξ → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V))
    (he : ∀ x, e x ∈ Γ) {n : ℕ} (t : Semiterm Λ ξ n) :
    encodeSemiterm F e t ∈ termSet L Γ (n : V) := by
  have hc := termSet_closed hL (show (n : V) ∈ (ω : V) by simp) Γ
  induction t with
  | bvar i => exact hc.1 _ (natCast_mem_of_lt i.isLt)
  | fvar x => exact hc.2.1 _ (he x)
  | @func k f ts ih =>
    apply hc.2.2 _ (hF k f).1
    rw [(hF k f).2]
    exact standardTuple_mem_function _ ih

noncomputable def encodeSemiformula (F : ∀ {k}, Λ.Func k → V)
    (R : ∀ {k}, Λ.Rel k → V) (e : ξ → V) {n : ℕ} : Semiformula Λ ξ n → V
  | .verum => truthCode
  | .falsum => falsityCode
  | .rel r ts => atomCode (relationToken (R r)) (standardTuple (fun i ↦ encodeSemiterm F e (ts i)))
  | .nrel r ts => negAtomCode (relationToken (R r)) (standardTuple (fun i ↦ encodeSemiterm F e (ts i)))
  | .and φ ψ => andCode (encodeSemiformula F R e φ) (encodeSemiformula F R e ψ)
  | .or φ ψ => orCode (encodeSemiformula F R e φ) (encodeSemiformula F R e ψ)
  | .all φ => allCode (encodeSemiformula F R e φ)
  | .exs φ => existsCode (encodeSemiformula F R e φ)

theorem encodeSemiformula_mem_family {L Γ : V} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V) (e : ξ → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧
      (relationArities L) ‘ (R r) = (k : V))
    (he : ∀ x, e x ∈ Γ) {n : ℕ} (φ : Semiformula Λ ξ n) :
    ⟨(n : V), encodeSemiformula F R e φ⟩ₖ ∈ formulaFamily L Γ := by
  have ha : ∀ n k (r : Λ.Rel k) (ts : Fin k → Semiterm Λ ξ n),
      IsAtomicArguments L Γ (n : V) (relationToken (R r))
        (standardTuple (fun i ↦ encodeSemiterm F e (ts i))) := by
    intro n k r ts
    refine Or.inr ⟨R r, (hR k r).1, rfl, ?_⟩
    rw [(hR k r).2]
    exact standardTuple_mem_function _ (fun i ↦ encodeSemiterm_mem hL F e hF he (ts i))
  induction φ with
  | verum => exact (formulaFamily_closed hL Γ _ (by simp)).1.1
  | falsum => exact (formulaFamily_closed hL Γ _ (by simp)).1.2
  | rel r ts => exact ((formulaFamily_closed hL Γ _ (by simp)).2.1 _ _ (ha _ _ r ts)).1
  | nrel r ts => exact ((formulaFamily_closed hL Γ _ (by simp)).2.1 _ _ (ha _ _ r ts)).2
  | and φ ψ ihφ ihψ => exact ((formulaFamily_closed hL Γ _ (by simp)).2.2.1 _ _ ihφ ihψ).1
  | or φ ψ ihφ ihψ => exact ((formulaFamily_closed hL Γ _ (by simp)).2.2.1 _ _ ihφ ihψ).2
  | all φ ih =>
    exact ((formulaFamily_closed hL Γ _ (by simp)).2.2.2 _ (by simpa [num_succ_def] using ih)).1
  | exs φ ih =>
    exact ((formulaFamily_closed hL Γ _ (by simp)).2.2.2 _ (by simpa [num_succ_def] using ih)).2

end ZFVP
