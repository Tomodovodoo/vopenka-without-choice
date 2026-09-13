import ZFVP.SetTheory.CnAbsoluteness

/-! One level above correctness: Sigma(k+2) truth goes up from a C(k+1) stage and
Pi(k+2) truth goes down into it. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.levy_succ_transport {k : ℕ} {δ : V} (hδ : Cn (k + 1) δ) {p : LevyPolarity} {m n : ℕ}
    {φ : SetTheorySemisentence n} (hφ : IsLevyFormula p m φ) : m ≤ k + 2 →
      ∀ b : Fin n → SetDomain (hierarchy δ), p.Preserves (φ.Evalb b) (φ.Evalb (fun i ↦ (b i).val)) := by
  let := hδ.ordinal
  have hA : IsTransitive (hierarchy δ) := hierarchy_transitive δ
  have ht {n : ℕ} (b : Fin n → SetDomain (hierarchy δ)) (t : SetTheorySemiterm Empty n) :
      (t.val b Empty.elim).val = t.val (fun i ↦ (b i).val) Empty.elim := by
    cases t with
    | bvar i => rfl
    | fvar e => exact Empty.elim e
    | func f ts => exact Empty.elim f
  induction hφ with
  | @bounded p k n φ hφ =>
    intro _ b
    cases p
    · exact (bounded_formula_absolute _ hφ b).mp
    · exact (bounded_formula_absolute _ hφ b).mpr
  | @raise p q m n φ hφ ih =>
    intro hm b
    have habs := hδ.levy_correct (hφ.mono (by omega : m ≤ k + 1)) b
    cases q
    · exact habs.mp
    · exact habs.mpr
  | @and p m n φ ψ hφ hψ ihφ ihψ =>
    intro hm b
    cases p
    · exact fun h ↦ ⟨ihφ hm b h.1, ihψ hm b h.2⟩
    · exact fun h ↦ ⟨ihφ hm b h.1, ihψ hm b h.2⟩
  | @or p m n φ ψ hφ hψ ihφ ihψ =>
    intro hm b
    cases p
    · exact fun h ↦ h.elim (fun h ↦ Or.inl (ihφ hm b h)) (fun h ↦ Or.inr (ihψ hm b h))
    · exact fun h ↦ h.elim (fun h ↦ Or.inl (ihφ hm b h)) (fun h ↦ Or.inr (ihψ hm b h))
  | @boundedAll p m n t φ hφ ih =>
    intro hm b
    cases p
    · intro h
      apply (eval_boundedSetAll _ _ _).mpr
      intro y hy
      have hy' : y ∈ (t.val b Empty.elim).val := (ht b t).symm ▸ hy
      have hyA := hA.transitive _ (t.val b Empty.elim).property y hy'
      have hh := ih hm (⟨y, hyA⟩ :> b) ((eval_boundedSetAll _ _ _).mp h ⟨y, hyA⟩ hy')
      rw [setDomain_val_vecCons _ (⟨y, hyA⟩ : SetDomain (hierarchy δ)) b] at hh
      exact hh
    · intro h
      apply (eval_boundedSetAll _ _ _).mpr
      intro y hy
      apply ih hm (y :> b)
      rw [setDomain_val_vecCons _ y b]
      exact (eval_boundedSetAll _ _ _).mp h y.val ((ht b t) ▸ hy)
  | @boundedExs p m n t φ hφ ih =>
    intro hm b
    cases p
    · intro h
      obtain ⟨y, hy, hh⟩ := (eval_boundedSetExs _ _ _).mp h
      apply (eval_boundedSetExs _ _ _).mpr
      refine ⟨y.val, (ht b t) ▸ hy, ?_⟩
      have hv := ih hm (y :> b) hh
      rw [setDomain_val_vecCons _ y b] at hv
      exact hv
    · intro h
      obtain ⟨y, hy, hh⟩ := (eval_boundedSetExs _ _ _).mp h
      have hy' : y ∈ (t.val b Empty.elim).val := (ht b t).symm ▸ hy
      have hyA := hA.transitive _ (t.val b Empty.elim).property y hy'
      apply (eval_boundedSetExs _ _ _).mpr
      refine ⟨⟨y, hyA⟩, hy', ih hm (⟨y, hyA⟩ :> b) ?_⟩
      rw [setDomain_val_vecCons _ (⟨y, hyA⟩ : SetDomain (hierarchy δ)) b]
      exact hh
  | @exs m n φ hφ ih =>
    intro hm b h
    obtain ⟨y, hy⟩ := h
    refine ⟨y.val, ?_⟩
    have hh := ih hm (y :> b) hy
    rw [setDomain_val_vecCons _ y b] at hh
    exact hh
  | @all m n φ hφ ih =>
    intro hm b h y
    apply ih hm (y :> b)
    rw [setDomain_val_vecCons _ y b]
    exact h y.val

theorem Cn.sigma_succ_upward {k n : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    {φ : SetTheorySemisentence n} (hφ : IsSigmaFormula (k + 2) φ) (b : Fin n → SetDomain (hierarchy δ)) :
    φ.Evalb b → φ.Evalb (fun i ↦ (b i).val) := hδ.levy_succ_transport hφ le_rfl b

theorem Cn.pi_succ_downward {k n : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    {φ : SetTheorySemisentence n} (hφ : IsPiFormula (k + 2) φ) (b : Fin n → SetDomain (hierarchy δ)) :
    φ.Evalb (fun i ↦ (b i).val) → φ.Evalb b := hδ.levy_succ_transport hφ le_rfl b

theorem Cn.defined_pi_succ_downward {k n : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    {φ : SetTheorySemisentence n} (hφ : IsPiFormula (k + 2) φ)
    (R : (Fin n → V) → Prop) [Defined R φ] (v : Fin n → SetDomain (hierarchy δ)) :
    R (fun i ↦ (v i).val) → φ.Evalb v :=
  fun h ↦ hδ.pi_succ_downward hφ v ((Defined.eval_iff _).mpr h)

theorem Cn.defined_sigma_succ_upward {k n : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    {φ : SetTheorySemisentence n} (hφ : IsSigmaFormula (k + 2) φ)
    (R : (Fin n → V) → Prop) [Defined R φ] (v : Fin n → SetDomain (hierarchy δ)) :
    φ.Evalb v → R (fun i ↦ (v i).val) :=
  fun h ↦ (Defined.eval_iff _).mp (hδ.sigma_succ_upward hφ v h)

end ZFVP
