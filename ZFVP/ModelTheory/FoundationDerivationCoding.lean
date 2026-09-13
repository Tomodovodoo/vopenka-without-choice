import ZFVP.ModelTheory.StandardSequentEncoding

/-! Every Foundation logical derivation yields a proof accepted by the coded calculus. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem foundationDerivation_coded (T : V) {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) (k : ℕ) :
    StandardCodedProvable T (((k + 1 : ℕ) : V)) (encodeFiniteSequent k Γ) := by
  induction d generalizing k with
  | identity r v =>
    have h := StandardCodedProvable.identity T (n := ((k + 1 : ℕ) : V)) (by simp)
      (encodeMembershipFormula_mem (V := V) (finiteVariableClosure k (Semiformula.rel r v)))
    change StandardCodedProvable T _ (encodeFiniteSequent k [Semiformula.rel r v, ∼Semiformula.rel r v])
    simpa only [encodeFiniteSequent_cons, encodeFiniteSequent_nil, finiteVariableClosure_neg,
      encodeMembershipFormula_neg, Nat.add_zero, SetTheory.insert_empty_eq] using h
  | verum =>
    simpa [encodeFiniteSequent_cons, encodeFiniteSequent_nil, encodeMembershipFormula, encodeSemiformula] using
      (StandardCodedProvable.verum T (n := ((k + 1 : ℕ) : V)) (by simp))
  | @contraction Δ Γ d hsub ih =>
    exact (ih k).weaken (encodeFiniteSequent_valid k Γ) (encodeFiniteSequent_mono k hsub)
  | @or φ ψ Γ d ih =>
    have hp := ih k
    simp only [encodeFiniteSequent_cons] at hp
    have hv := encodeFiniteSequent_valid (V := V) k (φ ⋎ ψ :: Γ)
    simp only [encodeFiniteSequent_cons, finiteVariableClosure_or, encodeMembershipFormula_or] at hv ⊢
    exact hp.disj hv (encodeMembershipFormula_mem _) (encodeMembershipFormula_mem _)
  | @and φ Γ ψ dp dq ihp ihq =>
    have hp := ihp k
    have hq := ihq k
    simp only [encodeFiniteSequent_cons] at hp hq
    have hv := encodeFiniteSequent_valid (V := V) k (φ ⋏ ψ :: Γ)
    simp only [encodeFiniteSequent_cons, finiteVariableClosure_and, encodeMembershipFormula_and] at hv ⊢
    exact hp.conj hq hv (encodeMembershipFormula_mem _) (encodeMembershipFormula_mem _)
  | @cut φ Γ Δ dp dn ihp ihn =>
    have hp := ihp k
    have hn := ihn k
    simp only [encodeFiniteSequent_cons] at hp
    simp only [encodeFiniteSequent_cons, finiteVariableClosure_neg, encodeMembershipFormula_neg] at hn
    have hv := encodeFiniteSequent_valid (V := V) k (Γ ++ Δ)
    simp only [encodeFiniteSequent_append] at hv ⊢
    exact hp.cut hn hv (encodeMembershipFormula_mem _)
  | @all Γ φ d ih =>
    have hp := ih (k + 1)
    simp only [encodeFiniteSequent_cons, finiteVariableClosure_free, encodeFiniteSequent_shift, num_succ_def] at hp
    have hv := encodeFiniteSequent_valid (V := V) k ((∀¹ φ) :: Γ)
    simp only [encodeFiniteSequent_cons, finiteVariableClosure_all, encodeMembershipFormula_all] at hv ⊢
    apply StandardCodedProvable.all hp hv (encodeFiniteSequent_valid k Γ).2.2
    simpa only [num_succ_def] using encodeMembershipFormula_mem (V := V) (finiteVariableClosure k φ)
  | @exs φ t Γ d ih =>
    cases t with
    | bvar i => exact Fin.elim0 i
    | func f _ => exact Empty.elim f
    | fvar j =>
      have hp := ih k
      simp only [encodeFiniteSequent_cons, finiteVariableClosure_subst, encodeMembershipFormula_instantiate] at hp
      have hv := encodeFiniteSequent_valid (V := V) k ((∃¹ φ) :: Γ)
      simp only [encodeFiniteSequent_cons, finiteVariableClosure_exs, encodeMembershipFormula_exs] at hv ⊢
      apply StandardCodedProvable.exists hp hv (natCast_mem_of_lt (finiteVariableIndex k j).isLt)
      simpa only [num_succ_def] using encodeMembershipFormula_mem (V := V) (finiteVariableClosure k φ)

end ZFVP
