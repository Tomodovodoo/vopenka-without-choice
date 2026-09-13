import ZFVP.Syntax.FoundationEncoding
import ZFVP.Syntax.FormulaInversion

/-! Faithfulness of the encoding under injective symbol and variable representations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language} {ξ : Type*}

theorem standardTuple_length_eq {n m : ℕ} {v : Fin n → V} {w : Fin m → V}
    (h : standardTuple v = standardTuple w) : n = m := by
  have hd := congrArg domain h
  simp only [domain_standardTuple] at hd
  exact natCast_injective hd

theorem encodeSemiterm_injective (F : ∀ {k}, Λ.Func k → V) (e : ξ → V)
    (hF : ∀ k, Function.Injective (F (k := k))) (he : Function.Injective e) (n : ℕ) :
    Function.Injective (encodeSemiterm F e (n := n)) := by
  intro t
  induction t with
  | bvar i =>
    intro u h
    cases u with
    | bvar j =>
      simp only [encodeSemiterm, boundVarCode_inj] at h
      exact congrArg Semiterm.bvar (Fin.ext (natCast_injective h))
    | fvar x => simp [encodeSemiterm] at h
    | func f ts => simp [encodeSemiterm] at h
  | fvar x =>
    intro u h
    cases u with
    | bvar i => exact False.elim (boundVarCode_ne_freeVarCode _ _ h.symm)
    | fvar y =>
      simp only [encodeSemiterm, freeVarCode_inj] at h
      exact congrArg Semiterm.fvar (he h)
    | func f ts => simp [encodeSemiterm] at h
  | @func k f ts ih =>
    intro u h
    cases u with
    | bvar i => exact False.elim (boundVarCode_ne_functionTermCode _ _ _ h.symm)
    | fvar x => exact False.elim (freeVarCode_ne_functionTermCode _ _ _ h.symm)
    | @func l g us =>
      obtain ⟨hf, hv⟩ := functionTermCode_inj _ _ _ _ |>.mp h
      have hk := standardTuple_length_eq hv
      subst l
      have hfg := hF k hf
      subst g
      have htu : ts = us := funext (fun i ↦ ih i (congrFun (standardTuple_injective hv) i))
      subst us
      rfl

theorem encodeSemiformula_injective (F : ∀ {k}, Λ.Func k → V)
    (R : ∀ {k}, Λ.Rel k → V) (e : ξ → V)
    (hF : ∀ k, Function.Injective (F (k := k)))
    (hR : ∀ k, Function.Injective (R (k := k))) (he : Function.Injective e) (n : ℕ) :
    Function.Injective (encodeSemiformula F R e (n := n)) := by
  intro φ
  induction φ <;> intro ψ h <;> cases ψ <;>
    simp [encodeSemiformula, truthCode, falsityCode, atomCode, negAtomCode,
      andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff] at h
  all_goals try rfl
  case rel.rel n k r ts l s us =>
    obtain ⟨hr, hv⟩ := h
    have hk := standardTuple_length_eq hv
    subst l
    have hrs := hR k hr
    subst s
    have htu : ts = us := funext (fun i ↦ encodeSemiterm_injective F e hF he n
      (congrFun (standardTuple_injective hv) i))
    subst us
    rfl
  case nrel.nrel n k r ts l s us =>
    obtain ⟨hr, hv⟩ := h
    have hk := standardTuple_length_eq hv
    subst l
    have hrs := hR k hr
    subst s
    have htu : ts = us := funext (fun i ↦ encodeSemiterm_injective F e hF he n
      (congrFun (standardTuple_injective hv) i))
    subst us
    rfl
  case and.and n φ ψ ihφ ihψ χ θ =>
    exact congrArg₂ Semiformula.and (ihφ h.1) (ihψ h.2)
  case or.or n φ ψ ihφ ihψ χ θ =>
    exact congrArg₂ Semiformula.or (ihφ h.1) (ihψ h.2)
  case all.all n φ ih ψ =>
    exact congrArg Semiformula.all (ih h)
  case exs.exs n φ ih ψ =>
    exact congrArg Semiformula.exs (ih h)

end ZFVP
