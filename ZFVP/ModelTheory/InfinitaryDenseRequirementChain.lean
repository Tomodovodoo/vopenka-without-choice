import Mathlib.Data.Set.Countable

namespace ZFVP.Infinitary
universe u v

/-- `R p q` means that `q` refines `p`. Each requirement is eventually met at
every later point of the sequence. -/
structure DenseRequirementChain {P : Type u} {I : Type v}
    (R : P → P → Prop) (Meets : I → P → Prop) (p₀ : P) where
  point : ℕ → P
  initial : point 0 = p₀
  step : ∀ n, R (point n) (point (n + 1))
  refines : ∀ {n m}, n ≤ m → R (point n) (point m)
  eventually_meets : ∀ i, ∃ N, ∀ n, N ≤ n → Meets i (point n)

/-- Countable requirements can be scheduled without a nonemptiness assumption
on their type. Unused decoding positions leave the current condition unchanged. -/
theorem exists_denseRequirementChain {P : Type u} {I : Type v} [Countable I]
    (R : P → P → Prop) (Meets : I → P → Prop)
    (hrefl : ∀ p, R p p) (htrans : ∀ {p q r}, R p q → R q r → R p r)
    (hpersist : ∀ i {p q}, R p q → Meets i p → Meets i q)
    (hdense : ∀ i p, ∃ q, R p q ∧ Meets i q) (p₀ : P) :
    Nonempty (DenseRequirementChain R Meets p₀) := by
  classical
  let : Encodable I := Encodable.ofCountable I
  let advance : Option I → P → P := fun o p ↦ match o with
    | none => p
    | some i => (hdense i p).choose
  have advance_refines (o : Option I) (p : P) : R p (advance o p) := by
    cases o with
    | none => exact hrefl p
    | some i => exact (hdense i p).choose_spec.1
  have advance_meets (i : I) (p : P) : Meets i (advance (some i) p) :=
    (hdense i p).choose_spec.2
  let c : ℕ → P := Nat.rec p₀ (fun n p ↦ advance (Encodable.decode n) p)
  have hstep (n : ℕ) : R (c n) (c (n + 1)) := advance_refines _ _
  have hle {n m : ℕ} (hnm : n ≤ m) : R (c n) (c m) :=
    Nat.le_induction (hrefl (c n)) (fun k _ ih ↦ htrans ih (hstep k)) m hnm
  refine ⟨⟨c, rfl, hstep, hle, ?_⟩⟩
  intro i
  have hi : Meets i (c (Encodable.encode i + 1)) := by
    change Meets i (advance (Encodable.decode (Encodable.encode i)) (c (Encodable.encode i)))
    rw [Encodable.encodek]
    exact advance_meets i _
  exact ⟨Encodable.encode i + 1, fun n hn ↦ hpersist i (hle hn) hi⟩

namespace DenseRequirementChain
variable {P : Type u} {I : Type v} {R : P → P → Prop} {Meets : I → P → Prop}
  {p₀ : P} (C : DenseRequirementChain R Meets p₀)

theorem meets (i : I) : ∃ n, Meets i (C.point n) := by
  obtain ⟨n, hn⟩ := C.eventually_meets i
  exact ⟨n, hn n (le_refl n)⟩

end DenseRequirementChain
end ZFVP.Infinitary
