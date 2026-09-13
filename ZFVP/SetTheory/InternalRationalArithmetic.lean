import ZFVP.SetTheory.InternalRationalOrder
import ZFVP.SetTheory.CountableSets

/-! Definable addition, negation and multiplication on the internal rational
quotient. The operations are sets of equivalent fraction codes, and their
values do not depend on a representative or on any choice function. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rationalCodeAddFormula : SetTheorySemisentence 3 :=
  f“z c e. z = !kpair.dfn
    (!kpair.dfn
      (!ordinalAddFormula
        (!naturalMulFormula (!kpair.π₁.dfn (!kpair.π₁.dfn c)) (!kpair.π₂.dfn e))
        (!naturalMulFormula (!kpair.π₁.dfn (!kpair.π₁.dfn e)) (!kpair.π₂.dfn c)))
      (!ordinalAddFormula
        (!naturalMulFormula (!kpair.π₂.dfn (!kpair.π₁.dfn c)) (!kpair.π₂.dfn e))
        (!naturalMulFormula (!kpair.π₂.dfn (!kpair.π₁.dfn e)) (!kpair.π₂.dfn c))))
    (!naturalMulFormula (!kpair.π₂.dfn c) (!kpair.π₂.dfn e))”

def rationalCodeNegFormula : SetTheorySemisentence 2 :=
  f“z c. z = !kpair.dfn
    (!kpair.dfn (!kpair.π₂.dfn (!kpair.π₁.dfn c)) (!kpair.π₁.dfn (!kpair.π₁.dfn c)))
    (!kpair.π₂.dfn c)”

def rationalCodeMulFormula : SetTheorySemisentence 3 :=
  f“z c e. z = !kpair.dfn
    (!kpair.dfn
      (!ordinalAddFormula
        (!naturalMulFormula (!kpair.π₁.dfn (!kpair.π₁.dfn c)) (!kpair.π₁.dfn (!kpair.π₁.dfn e)))
        (!naturalMulFormula (!kpair.π₂.dfn (!kpair.π₁.dfn c)) (!kpair.π₂.dfn (!kpair.π₁.dfn e))))
      (!ordinalAddFormula
        (!naturalMulFormula (!kpair.π₁.dfn (!kpair.π₁.dfn c)) (!kpair.π₂.dfn (!kpair.π₁.dfn e)))
        (!naturalMulFormula (!kpair.π₂.dfn (!kpair.π₁.dfn c)) (!kpair.π₁.dfn (!kpair.π₁.dfn e)))))
    (!naturalMulFormula (!kpair.π₂.dfn c) (!kpair.π₂.dfn e))”

def rationalZeroFormula : SetTheorySemisentence 1 :=
  f“q. q = !rationalClassFormula
    (!kpair.dfn (!kpair.dfn (!isEmpty) (!isEmpty)) (!succ.dfn (!isEmpty)))”

def rationalOneFormula : SetTheorySemisentence 1 :=
  f“q. q = !rationalClassFormula
    (!kpair.dfn (!kpair.dfn (!succ.dfn (!isEmpty)) (!isEmpty)) (!succ.dfn (!isEmpty)))”

def rationalAddFormula : SetTheorySemisentence 3 :=
  f“z q r. ∀ x, x ∈ z ↔ x ∈ !rationalCodeSpaceFormula ∧
    ∃ c ∈ q, ∃ e ∈ r, !rationalCodeEquivFormula (!rationalCodeAddFormula c e) x”

def rationalNegFormula : SetTheorySemisentence 2 :=
  f“z q. ∀ x, x ∈ z ↔ x ∈ !rationalCodeSpaceFormula ∧
    ∃ c ∈ q, !rationalCodeEquivFormula (!rationalCodeNegFormula c) x”

def rationalMulFormula : SetTheorySemisentence 3 :=
  f“z q r. ∀ x, x ∈ z ↔ x ∈ !rationalCodeSpaceFormula ∧
    ∃ c ∈ q, ∃ e ∈ r, !rationalCodeEquivFormula (!rationalCodeMulFormula c e) x”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace InternalRationalRep

noncomputable def zero : InternalRationalRep V := ⟨0, 0, 1, zero_lt_one⟩
noncomputable def one : InternalRationalRep V := ⟨1, 0, 1, zero_lt_one⟩

noncomputable def add (r s : InternalRationalRep V) : InternalRationalRep V where
  pos := r.pos * s.den + s.pos * r.den
  neg := r.neg * s.den + s.neg * r.den
  den := r.den * s.den
  den_pos := mul_pos r.den_pos s.den_pos

noncomputable def negation (r : InternalRationalRep V) : InternalRationalRep V where
  pos := r.neg
  neg := r.pos
  den := r.den
  den_pos := r.den_pos

noncomputable def mul (r s : InternalRationalRep V) : InternalRationalRep V where
  pos := r.pos * s.pos + r.neg * s.neg
  neg := r.pos * s.neg + r.neg * s.pos
  den := r.den * s.den
  den_pos := mul_pos r.den_pos s.den_pos

theorem add_congr {r r' s s' : InternalRationalRep V} (hr : r.Equal r')
    (hs : s.Equal s') : (r.add s).Equal (r'.add s') := by
  dsimp [Equal] at hr hs
  dsimp [Equal, add]
  calc
    (r.pos * s.den + s.pos * r.den) * (r'.den * s'.den) +
        (r'.neg * s'.den + s'.neg * r'.den) * (r.den * s.den) =
        (r.pos * r'.den + r'.neg * r.den) * (s.den * s'.den) +
          (s.pos * s'.den + s'.neg * s.den) * (r.den * r'.den) := by ring
    _ = (r.neg * r'.den + r'.pos * r.den) * (s.den * s'.den) +
          (s.neg * s'.den + s'.pos * s.den) * (r.den * r'.den) := by rw [hr, hs]
    _ = (r.neg * s.den + s.neg * r.den) * (r'.den * s'.den) +
          (r'.pos * s'.den + s'.pos * r'.den) * (r.den * s.den) := by ring

theorem negation_congr {r s : InternalRationalRep V} (h : r.Equal s) :
    r.negation.Equal s.negation := by
  exact h.symm

theorem mul_comm (r s : InternalRationalRep V) : (r.mul s).Equal (s.mul r) := by
  dsimp [Equal, mul]
  ring

theorem mul_congr_left {r r' s : InternalRationalRep V} (h : r.Equal r') :
    (r.mul s).Equal (r'.mul s) := by
  dsimp [Equal] at h
  dsimp [Equal, mul]
  calc
    (r.pos * s.pos + r.neg * s.neg) * (r'.den * s.den) +
        (r'.pos * s.neg + r'.neg * s.pos) * (r.den * s.den) =
        (r.pos * r'.den + r'.neg * r.den) * s.pos * s.den +
          (r.neg * r'.den + r'.pos * r.den) * s.neg * s.den := by ring
    _ = (r.neg * r'.den + r'.pos * r.den) * s.pos * s.den +
          (r.pos * r'.den + r'.neg * r.den) * s.neg * s.den := by rw [h]
    _ = (r.pos * s.neg + r.neg * s.pos) * (r'.den * s.den) +
          (r'.pos * s.pos + r'.neg * s.neg) * (r.den * s.den) := by ring

theorem mul_congr {r r' s s' : InternalRationalRep V} (hr : r.Equal r')
    (hs : s.Equal s') : (r.mul s).Equal (r'.mul s') := by
  apply equal_trans (mul_congr_left hr)
  apply equal_trans (mul_comm r' s)
  apply equal_trans (mul_congr_left hs)
  exact mul_comm s' r'

theorem add_comm (r s : InternalRationalRep V) : (r.add s).Equal (s.add r) := by
  dsimp [Equal, add]
  ring

theorem add_assoc (r s t : InternalRationalRep V) :
    ((r.add s).add t).Equal (r.add (s.add t)) := by
  dsimp [Equal, add]
  ring

theorem add_zero (r : InternalRationalRep V) : (r.add zero).Equal r := by
  dsimp [Equal, add, zero]
  ring

theorem add_negation (r : InternalRationalRep V) : (r.add r.negation).Equal zero := by
  dsimp [Equal, add, negation, zero]
  ring

theorem mul_assoc (r s t : InternalRationalRep V) :
    ((r.mul s).mul t).Equal (r.mul (s.mul t)) := by
  dsimp [Equal, mul]
  ring

theorem mul_one (r : InternalRationalRep V) : (r.mul one).Equal r := by
  dsimp [Equal, mul, one]
  ring

theorem mul_zero (r : InternalRationalRep V) : (r.mul zero).Equal zero := by
  simp [Equal, mul, zero]

theorem mul_add (r s t : InternalRationalRep V) :
    (r.mul (s.add t)).Equal ((r.mul s).add (r.mul t)) := by
  dsimp [Equal, mul, add]
  ring

end InternalRationalRep

noncomputable def rationalCodeAdd (c e : V) : V :=
  ⟨⟨ordinalAdd (naturalMul (kpair.π₁ (kpair.π₁ c)) (kpair.π₂ e))
        (naturalMul (kpair.π₁ (kpair.π₁ e)) (kpair.π₂ c)),
      ordinalAdd (naturalMul (kpair.π₂ (kpair.π₁ c)) (kpair.π₂ e))
        (naturalMul (kpair.π₂ (kpair.π₁ e)) (kpair.π₂ c))⟩ₖ,
    naturalMul (kpair.π₂ c) (kpair.π₂ e)⟩ₖ

noncomputable def rationalCodeNeg (c : V) : V :=
  ⟨⟨kpair.π₂ (kpair.π₁ c), kpair.π₁ (kpair.π₁ c)⟩ₖ, kpair.π₂ c⟩ₖ

noncomputable def rationalCodeMul (c e : V) : V :=
  ⟨⟨ordinalAdd
        (naturalMul (kpair.π₁ (kpair.π₁ c)) (kpair.π₁ (kpair.π₁ e)))
        (naturalMul (kpair.π₂ (kpair.π₁ c)) (kpair.π₂ (kpair.π₁ e))),
      ordinalAdd
        (naturalMul (kpair.π₁ (kpair.π₁ c)) (kpair.π₂ (kpair.π₁ e)))
        (naturalMul (kpair.π₂ (kpair.π₁ c)) (kpair.π₁ (kpair.π₁ e)))⟩ₖ,
    naturalMul (kpair.π₂ c) (kpair.π₂ e)⟩ₖ

instance rationalCodeAddFormula_defined :
    ℒₛₑₜ-function₂[V] rationalCodeAdd via rationalCodeAddFormula :=
  ⟨fun v ↦ by simp [rationalCodeAddFormula, rationalCodeAdd]⟩

instance rationalCodeAdd_definable : ℒₛₑₜ-function₂[V] rationalCodeAdd :=
  rationalCodeAddFormula_defined.to_definable

instance rationalCodeNegFormula_defined :
    ℒₛₑₜ-function₁[V] rationalCodeNeg via rationalCodeNegFormula :=
  ⟨fun v ↦ by simp [rationalCodeNegFormula, rationalCodeNeg]⟩

instance rationalCodeNeg_definable : ℒₛₑₜ-function₁[V] rationalCodeNeg :=
  rationalCodeNegFormula_defined.to_definable

instance rationalCodeMulFormula_defined :
    ℒₛₑₜ-function₂[V] rationalCodeMul via rationalCodeMulFormula :=
  ⟨fun v ↦ by simp [rationalCodeMulFormula, rationalCodeMul]⟩

instance rationalCodeMul_definable : ℒₛₑₜ-function₂[V] rationalCodeMul :=
  rationalCodeMulFormula_defined.to_definable

@[simp] theorem rationalCodeAdd_reps (r s : InternalRationalRep V) :
    rationalCodeAdd r.code s.code = (r.add s).code := by
  simp [rationalCodeAdd, InternalRationalRep.code, InternalRationalRep.add]

@[simp] theorem rationalCodeNeg_rep (r : InternalRationalRep V) :
    rationalCodeNeg r.code = r.negation.code := by
  simp [rationalCodeNeg, InternalRationalRep.code, InternalRationalRep.negation]

@[simp] theorem rationalCodeMul_reps (r s : InternalRationalRep V) :
    rationalCodeMul r.code s.code = (r.mul s).code := by
  simp [rationalCodeMul, InternalRationalRep.code, InternalRationalRep.mul]

theorem rationalCodeAdd_mem {c e : V} (hc : c ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) : rationalCodeAdd c e ∈ rationalCodeSpace V := by
  obtain ⟨r, rfl⟩ := rationalCode_exists_rep hc
  obtain ⟨s, rfl⟩ := rationalCode_exists_rep he
  simpa only [rationalCodeAdd_reps] using (r.add s).code_mem

theorem rationalCodeNeg_mem {c : V} (hc : c ∈ rationalCodeSpace V) :
    rationalCodeNeg c ∈ rationalCodeSpace V := by
  obtain ⟨r, rfl⟩ := rationalCode_exists_rep hc
  simpa only [rationalCodeNeg_rep] using r.negation.code_mem

theorem rationalCodeMul_mem {c e : V} (hc : c ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) : rationalCodeMul c e ∈ rationalCodeSpace V := by
  obtain ⟨r, rfl⟩ := rationalCode_exists_rep hc
  obtain ⟨s, rfl⟩ := rationalCode_exists_rep he
  simpa only [rationalCodeMul_reps] using (r.mul s).code_mem

theorem rationalCodeAdd_congr {c c' e e' : V}
    (hc : c ∈ rationalCodeSpace V) (hc' : c' ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) (he' : e' ∈ rationalCodeSpace V)
    (hcc : RationalCodeEquiv c c') (hee : RationalCodeEquiv e e') :
    RationalCodeEquiv (rationalCodeAdd c e) (rationalCodeAdd c' e') := by
  obtain ⟨r, rfl⟩ := rationalCode_exists_rep hc
  obtain ⟨r', rfl⟩ := rationalCode_exists_rep hc'
  obtain ⟨s, rfl⟩ := rationalCode_exists_rep he
  obtain ⟨s', rfl⟩ := rationalCode_exists_rep he'
  rw [InternalRationalRep.equiv_code_iff] at hcc hee
  simp only [rationalCodeAdd_reps, InternalRationalRep.equiv_code_iff]
  exact InternalRationalRep.add_congr hcc hee

theorem rationalCodeNeg_congr {c e : V} (hc : c ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) (h : RationalCodeEquiv c e) :
    RationalCodeEquiv (rationalCodeNeg c) (rationalCodeNeg e) := by
  obtain ⟨r, rfl⟩ := rationalCode_exists_rep hc
  obtain ⟨s, rfl⟩ := rationalCode_exists_rep he
  rw [InternalRationalRep.equiv_code_iff] at h
  simp only [rationalCodeNeg_rep, InternalRationalRep.equiv_code_iff]
  exact InternalRationalRep.negation_congr h

theorem rationalCodeMul_congr {c c' e e' : V}
    (hc : c ∈ rationalCodeSpace V) (hc' : c' ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) (he' : e' ∈ rationalCodeSpace V)
    (hcc : RationalCodeEquiv c c') (hee : RationalCodeEquiv e e') :
    RationalCodeEquiv (rationalCodeMul c e) (rationalCodeMul c' e') := by
  obtain ⟨r, rfl⟩ := rationalCode_exists_rep hc
  obtain ⟨r', rfl⟩ := rationalCode_exists_rep hc'
  obtain ⟨s, rfl⟩ := rationalCode_exists_rep he
  obtain ⟨s', rfl⟩ := rationalCode_exists_rep he'
  rw [InternalRationalRep.equiv_code_iff] at hcc hee
  simp only [rationalCodeMul_reps, InternalRationalRep.equiv_code_iff]
  exact InternalRationalRep.mul_congr hcc hee

noncomputable def rationalZero (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V := rationalClass ⟨⟨0, 0⟩ₖ, 1⟩ₖ

noncomputable def rationalOne (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V := rationalClass ⟨⟨1, 0⟩ₖ, 1⟩ₖ

noncomputable def rationalAdd (q r : V) : V :=
  {x ∈ rationalCodeSpace V ; ∃ c ∈ q, ∃ e ∈ r, RationalCodeEquiv (rationalCodeAdd c e) x}

noncomputable def rationalNeg (q : V) : V :=
  {x ∈ rationalCodeSpace V ; ∃ c ∈ q, RationalCodeEquiv (rationalCodeNeg c) x}

noncomputable def rationalMul (q r : V) : V :=
  {x ∈ rationalCodeSpace V ; ∃ c ∈ q, ∃ e ∈ r, RationalCodeEquiv (rationalCodeMul c e) x}

instance rationalZeroFormula_defined : ℒₛₑₜ-function₀[V] (rationalZero V) via rationalZeroFormula :=
  ⟨fun v ↦ by simp [rationalZeroFormula, rationalZero, zero_def]; rfl⟩

instance rationalOneFormula_defined : ℒₛₑₜ-function₀[V] (rationalOne V) via rationalOneFormula :=
  ⟨fun v ↦ by simp [rationalOneFormula, rationalOne, zero_def]; rfl⟩

instance rationalAddFormula_defined : ℒₛₑₜ-function₂[V] rationalAdd via rationalAddFormula :=
  ⟨fun v ↦ by
    change rationalAddFormula.Evalb v ↔ v 0 = rationalAdd (v 1) (v 2)
    rw [mem_ext_iff]
    simp [rationalAddFormula, rationalAdd]⟩

instance rationalAdd_definable : ℒₛₑₜ-function₂[V] rationalAdd := rationalAddFormula_defined.to_definable

instance rationalNegFormula_defined : ℒₛₑₜ-function₁[V] rationalNeg via rationalNegFormula :=
  ⟨fun v ↦ by
    change rationalNegFormula.Evalb v ↔ v 0 = rationalNeg (v 1)
    rw [mem_ext_iff]
    simp [rationalNegFormula, rationalNeg]⟩

instance rationalNeg_definable : ℒₛₑₜ-function₁[V] rationalNeg := rationalNegFormula_defined.to_definable

instance rationalMulFormula_defined : ℒₛₑₜ-function₂[V] rationalMul via rationalMulFormula :=
  ⟨fun v ↦ by
    change rationalMulFormula.Evalb v ↔ v 0 = rationalMul (v 1) (v 2)
    rw [mem_ext_iff]
    simp [rationalMulFormula, rationalMul]⟩

instance rationalMul_definable : ℒₛₑₜ-function₂[V] rationalMul := rationalMulFormula_defined.to_definable

theorem rationalAdd_classes {c e : V} (hc : c ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) :
    rationalAdd (rationalClass c) (rationalClass e) = rationalClass (rationalCodeAdd c e) := by
  apply mem_ext
  intro x
  simp only [rationalAdd, mem_sep_iff, mem_rationalClass_iff]
  constructor
  · rintro ⟨hx, c', ⟨hc', hcc'⟩, e', ⟨he', hee'⟩, h⟩
    exact ⟨hx, rationalCodeEquiv_trans (rationalCodeAdd_mem hc he)
      (rationalCodeAdd_mem hc' he') hx (rationalCodeAdd_congr hc hc' he he' hcc' hee') h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, c, ⟨hc, rationalCodeEquiv_refl hc⟩, e, ⟨he, rationalCodeEquiv_refl he⟩, h⟩

theorem rationalNeg_class {c : V} (hc : c ∈ rationalCodeSpace V) :
    rationalNeg (rationalClass c) = rationalClass (rationalCodeNeg c) := by
  apply mem_ext
  intro x
  simp only [rationalNeg, mem_sep_iff, mem_rationalClass_iff]
  constructor
  · rintro ⟨hx, c', ⟨hc', hcc'⟩, h⟩
    exact ⟨hx, rationalCodeEquiv_trans (rationalCodeNeg_mem hc) (rationalCodeNeg_mem hc') hx
      (rationalCodeNeg_congr hc hc' hcc') h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, c, ⟨hc, rationalCodeEquiv_refl hc⟩, h⟩

theorem rationalMul_classes {c e : V} (hc : c ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) :
    rationalMul (rationalClass c) (rationalClass e) = rationalClass (rationalCodeMul c e) := by
  apply mem_ext
  intro x
  simp only [rationalMul, mem_sep_iff, mem_rationalClass_iff]
  constructor
  · rintro ⟨hx, c', ⟨hc', hcc'⟩, e', ⟨he', hee'⟩, h⟩
    exact ⟨hx, rationalCodeEquiv_trans (rationalCodeMul_mem hc he)
      (rationalCodeMul_mem hc' he') hx (rationalCodeMul_congr hc hc' he he' hcc' hee') h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, c, ⟨hc, rationalCodeEquiv_refl hc⟩, e, ⟨he, rationalCodeEquiv_refl he⟩, h⟩

@[simp] theorem rationalAdd_reps (r s : InternalRationalRep V) :
    rationalAdd (rationalClass r.code) (rationalClass s.code) = rationalClass (r.add s).code := by
  rw [rationalAdd_classes r.code_mem s.code_mem, rationalCodeAdd_reps]

@[simp] theorem rationalNeg_rep (r : InternalRationalRep V) :
    rationalNeg (rationalClass r.code) = rationalClass r.negation.code := by
  rw [rationalNeg_class r.code_mem, rationalCodeNeg_rep]

@[simp] theorem rationalMul_reps (r s : InternalRationalRep V) :
    rationalMul (rationalClass r.code) (rationalClass s.code) = rationalClass (r.mul s).code := by
  rw [rationalMul_classes r.code_mem s.code_mem, rationalCodeMul_reps]

theorem rationalZero_eq : rationalZero V = rationalClass (InternalRationalRep.zero (V := V)).code := rfl
theorem rationalOne_eq : rationalOne V = rationalClass (InternalRationalRep.one (V := V)).code := rfl

theorem rationalZero_mem : rationalZero V ∈ internalRationals V :=
  rationalClass_mem_internalRationals InternalRationalRep.zero.code_mem

theorem rationalOne_mem : rationalOne V ∈ internalRationals V :=
  rationalClass_mem_internalRationals InternalRationalRep.one.code_mem

theorem rationalAdd_mem {q r : V} (hq : q ∈ internalRationals V) (hr : r ∈ internalRationals V) :
    rationalAdd q r ∈ internalRationals V := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  rw [rationalAdd_reps]
  exact rationalClass_mem_internalRationals (a.add b).code_mem

theorem rationalNeg_mem {q : V} (hq : q ∈ internalRationals V) :
    rationalNeg q ∈ internalRationals V := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  rw [rationalNeg_rep]
  exact rationalClass_mem_internalRationals a.negation.code_mem

theorem rationalMul_mem {q r : V} (hq : q ∈ internalRationals V) (hr : r ∈ internalRationals V) :
    rationalMul q r ∈ internalRationals V := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  rw [rationalMul_reps]
  exact rationalClass_mem_internalRationals (a.mul b).code_mem

theorem rationalClass_eq_of_reps_equal {a b : InternalRationalRep V} (h : a.Equal b) :
    rationalClass a.code = rationalClass b.code :=
  (rationalClass_eq_iff a.code_mem b.code_mem).mpr ((a.equiv_code_iff b).mpr h)

theorem rationalAdd_comm {q r : V} (hq : q ∈ internalRationals V) (hr : r ∈ internalRationals V) :
    rationalAdd q r = rationalAdd r q := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  simp only [rationalAdd_reps]
  exact rationalClass_eq_of_reps_equal (a.add_comm b)

theorem rationalAdd_assoc {q r s : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) (hs : s ∈ internalRationals V) :
    rationalAdd (rationalAdd q r) s = rationalAdd q (rationalAdd r s) := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  obtain ⟨c, rfl⟩ := internalRational_exists_rep hs
  simp only [rationalAdd_reps]
  exact rationalClass_eq_of_reps_equal (a.add_assoc b c)

theorem rationalAdd_zero {q : V} (hq : q ∈ internalRationals V) :
    rationalAdd q (rationalZero V) = q := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  rw [rationalZero_eq, rationalAdd_reps]
  exact rationalClass_eq_of_reps_equal a.add_zero

theorem rationalAdd_neg {q : V} (hq : q ∈ internalRationals V) :
    rationalAdd q (rationalNeg q) = rationalZero V := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  rw [rationalNeg_rep, rationalAdd_reps, rationalZero_eq]
  exact rationalClass_eq_of_reps_equal a.add_negation

theorem rationalMul_comm {q r : V} (hq : q ∈ internalRationals V) (hr : r ∈ internalRationals V) :
    rationalMul q r = rationalMul r q := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  simp only [rationalMul_reps]
  exact rationalClass_eq_of_reps_equal (a.mul_comm b)

theorem rationalMul_assoc {q r s : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) (hs : s ∈ internalRationals V) :
    rationalMul (rationalMul q r) s = rationalMul q (rationalMul r s) := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  obtain ⟨c, rfl⟩ := internalRational_exists_rep hs
  simp only [rationalMul_reps]
  exact rationalClass_eq_of_reps_equal (a.mul_assoc b c)

theorem rationalMul_one {q : V} (hq : q ∈ internalRationals V) :
    rationalMul q (rationalOne V) = q := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  rw [rationalOne_eq, rationalMul_reps]
  exact rationalClass_eq_of_reps_equal a.mul_one

theorem rationalMul_zero {q : V} (hq : q ∈ internalRationals V) :
    rationalMul q (rationalZero V) = rationalZero V := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  rw [rationalZero_eq, rationalMul_reps]
  exact rationalClass_eq_of_reps_equal a.mul_zero

theorem rationalMul_add {q r s : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) (hs : s ∈ internalRationals V) :
    rationalMul q (rationalAdd r s) = rationalAdd (rationalMul q r) (rationalMul q s) := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  obtain ⟨c, rfl⟩ := internalRational_exists_rep hs
  simp only [rationalAdd_reps, rationalMul_reps]
  exact rationalClass_eq_of_reps_equal (a.mul_add b c)

theorem rationalZero_ne_one : rationalZero V ≠ rationalOne V := by
  intro h
  rw [rationalZero_eq, rationalOne_eq, rationalClass_eq_iff
    InternalRationalRep.zero.code_mem InternalRationalRep.one.code_mem,
    InternalRationalRep.equiv_code_iff] at h
  simp [InternalRationalRep.Equal, InternalRationalRep.zero, InternalRationalRep.one] at h

theorem rationalCodeSpace_countable : IsInternallyCountable (rationalCodeSpace V) := by
  let F : V → V := fun c ↦ naturalPairCode
    (naturalPairCode (kpair.π₁ (kpair.π₁ c)) (kpair.π₂ (kpair.π₁ c))) (kpair.π₂ c)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  refine ⟨definableGraph (rationalCodeSpace V) F hF,
    definableGraph_mem_function_of_mapsTo _ _ _ _ ?_, ?_⟩
  · intro c hc
    obtain ⟨a, ha, b, hb, d, hd, _, rfl⟩ := (mem_rationalCodeSpace_iff c).mp hc
    simpa [F] using naturalPairCode_natural (naturalPairCode_natural ha hb) hd
  · intro c e z hcz hez
    obtain ⟨hc, hzc⟩ := (pair_mem_definableGraph_iff _ _ _ c z).mp hcz
    obtain ⟨he, hze⟩ := (pair_mem_definableGraph_iff _ _ _ e z).mp hez
    have h : F c = F e := hzc.symm.trans hze
    obtain ⟨a, ha, b, hb, d, hd, _, rfl⟩ := (mem_rationalCodeSpace_iff c).mp hc
    obtain ⟨u, hu, v, hv, f, hf, _, rfl⟩ := (mem_rationalCodeSpace_iff e).mp he
    simp only [F, kpair.π₁_kpair, kpair.π₂_kpair] at h
    obtain ⟨hab, hdf⟩ := naturalPairCode_injective (naturalPairCode_natural ha hb) hd
      (naturalPairCode_natural hu hv) hf h
    obtain ⟨hau, hbv⟩ := naturalPairCode_injective ha hb hu hv hab
    rw [hau, hbv, hdf]

theorem internalRationals_countable : IsInternallyCountable (internalRationals V) :=
  internallyCountable_repl rationalClass (by definability) rationalCodeSpace_countable

end ZFVP
