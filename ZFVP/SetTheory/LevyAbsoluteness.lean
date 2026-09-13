import ZFVP.SetTheory.LevyFormulas

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def LevyPolarity.Preserves (p : LevyPolarity) (P Q : Prop) : Prop :=
  match p with
  | .sigma => P → Q
  | .pi => Q → P

variable {V : Type*} [SetStructure V]

theorem levy_one_transport (A : V) [hA : IsTransitive A] {p k n} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula p k φ) : k ≤ 1 → ∀ b : Fin n → SetDomain A,
      p.Preserves (φ.Evalb b) (φ.Evalb (fun i ↦ (b i).val)) := by
  have ht {n : ℕ} (b : Fin n → SetDomain A) (t : SetTheorySemiterm Empty n) :
      (t.val b Empty.elim).val = t.val (fun i ↦ (b i).val) Empty.elim := by
    cases t with
    | bvar i => rfl
    | fvar e => exact Empty.elim e
    | func f ts => exact Empty.elim f
  induction hφ with
  | @bounded p k n φ hφ =>
    intro _ b
    cases p
    · exact (bounded_formula_absolute A hφ b).mp
    · exact (bounded_formula_absolute A hφ b).mpr
  | @raise p q k n φ hφ ih =>
    intro hk b
    have hzero : k = 0 := by omega
    have habs := bounded_formula_absolute A (hφ.zero_bounded hzero) b
    cases q
    · exact habs.mp
    · exact habs.mpr
  | @and p k n φ ψ hφ hψ ihφ ihψ =>
    intro hk b
    cases p
    · exact fun h ↦ ⟨ihφ hk b h.1, ihψ hk b h.2⟩
    · exact fun h ↦ ⟨ihφ hk b h.1, ihψ hk b h.2⟩
  | @or p k n φ ψ hφ hψ ihφ ihψ =>
    intro hk b
    cases p
    · exact fun h ↦ h.elim (fun h ↦ Or.inl (ihφ hk b h)) (fun h ↦ Or.inr (ihψ hk b h))
    · exact fun h ↦ h.elim (fun h ↦ Or.inl (ihφ hk b h)) (fun h ↦ Or.inr (ihψ hk b h))
  | @boundedAll p k n t φ hφ ih =>
    intro hk b
    cases p
    · intro h
      apply (eval_boundedSetAll _ _ _).mpr
      intro y hy
      have hy' : y ∈ (t.val b Empty.elim).val := (ht b t).symm ▸ hy
      have hyA := hA.transitive _ (t.val b Empty.elim).property y hy'
      have hh := ih hk (⟨y, hyA⟩ :> b) ((eval_boundedSetAll _ _ _).mp h ⟨y, hyA⟩ hy')
      rw [setDomain_val_vecCons A (⟨y, hyA⟩ : SetDomain A) b] at hh
      exact hh
    · intro h
      apply (eval_boundedSetAll _ _ _).mpr
      intro y hy
      apply ih hk (y :> b)
      rw [setDomain_val_vecCons A y b]
      exact (eval_boundedSetAll _ _ _).mp h y.val ((ht b t) ▸ hy)
  | @boundedExs p k n t φ hφ ih =>
    intro hk b
    cases p
    · intro h
      obtain ⟨y, hy, hh⟩ := (eval_boundedSetExs _ _ _).mp h
      apply (eval_boundedSetExs _ _ _).mpr
      refine ⟨y.val, (ht b t) ▸ hy, ?_⟩
      have hv := ih hk (y :> b) hh
      rw [setDomain_val_vecCons A y b] at hv
      exact hv
    · intro h
      obtain ⟨y, hy, hh⟩ := (eval_boundedSetExs _ _ _).mp h
      have hy' : y ∈ (t.val b Empty.elim).val := (ht b t).symm ▸ hy
      have hyA := hA.transitive _ (t.val b Empty.elim).property y hy'
      apply (eval_boundedSetExs _ _ _).mpr
      refine ⟨⟨y, hyA⟩, hy', ih hk (⟨y, hyA⟩ :> b) ?_⟩
      rw [setDomain_val_vecCons A (⟨y, hyA⟩ : SetDomain A) b]
      exact hh
  | @exs k n φ hφ ih =>
    intro hk b h
    obtain ⟨y, hy⟩ := h
    refine ⟨y.val, ?_⟩
    have hh := ih hk (y :> b) hy
    rw [setDomain_val_vecCons A y b] at hh
    exact hh
  | @all k n φ hφ ih =>
    intro hk b h y
    apply ih hk (y :> b)
    rw [setDomain_val_vecCons A y b]
    exact h y.val

theorem sigma_one_upward (A : V) [IsTransitive A] {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsSigmaFormula 1 φ) (b : Fin n → SetDomain A) :
    φ.Evalb b → φ.Evalb (fun i ↦ (b i).val) := levy_one_transport A hφ (by omega) b

theorem pi_one_downward (A : V) [IsTransitive A] {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsPiFormula 1 φ) (b : Fin n → SetDomain A) :
    φ.Evalb (fun i ↦ (b i).val) → φ.Evalb b := levy_one_transport A hφ (by omega) b

end ZFVP
