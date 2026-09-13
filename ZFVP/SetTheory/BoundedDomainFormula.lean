import ZFVP.SetTheory.BoundedFormulas

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Add the domain as the last bound parameter and bound every quantifier by it. -/
def boundDomainTerm {n : ℕ} : SetTheorySemiterm Empty n → SetTheorySemiterm Empty (n + 1)
  | .bvar i => .bvar i.castSucc
  | .fvar e => Empty.elim e

def boundedDomainFormula : {n : ℕ} → SetTheorySemisentence n → SetTheorySemisentence (n + 1)
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, .rel r ts => .rel r (fun i ↦ boundDomainTerm (ts i))
  | _, .nrel r ts => .nrel r (fun i ↦ boundDomainTerm (ts i))
  | _, .and φ ψ => .and (boundedDomainFormula φ) (boundedDomainFormula ψ)
  | _, .or φ ψ => .or (boundedDomainFormula φ) (boundedDomainFormula ψ)
  | n, .all φ => boundedSetAll (.bvar (Fin.last n)) (boundedDomainFormula φ)
  | n, .exs φ => boundedSetExs (.bvar (Fin.last n)) (boundedDomainFormula φ)

theorem boundedDomainFormula_bounded {n : ℕ} (φ : SetTheorySemisentence n) :
    IsBoundedSetFormula (boundedDomainFormula φ) := by
  induction φ with
  | verum => exact .verum
  | falsum => exact .falsum
  | rel r ts => exact .rel _ _
  | nrel r ts => exact .nrel _ _
  | and φ ψ ihφ ihψ => exact .and ihφ ihψ
  | or φ ψ ihφ ihψ => exact .or ihφ ihψ
  | all φ ih => exact .all _ ih
  | exs φ ih => exact .exs _ ih

variable {V : Type*} [SetStructure V]

omit [SetStructure V] in
private theorem lastCases_cons {n : ℕ} (U x : V) (b : Fin n → V) :
    Fin.lastCases U (x :> b) = x :> Fin.lastCases U b := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp
  · rw [Fin.lastCases_castSucc]
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · rfl
    · simp

private theorem val_boundDomainTerm {n : ℕ} (U : V) (b : Fin n → SetDomain U)
    (t : SetTheorySemiterm Empty n) :
    (boundDomainTerm t).val (Fin.lastCases U (fun i ↦ (b i).val)) Empty.elim =
      (t.val b Empty.elim).val := by
  cases t with
  | bvar i => simp [boundDomainTerm]
  | fvar e => exact Empty.elim e
  | func f ts => exact Empty.elim f

theorem eval_boundedDomainFormula {n : ℕ} (U : V) (φ : SetTheorySemisentence n)
    (b : Fin n → SetDomain U) :
    (boundedDomainFormula φ).Evalb (Fin.lastCases U (fun i ↦ (b i).val)) ↔ φ.Evalb b := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    cases r <;> simp only [boundedDomainFormula, Semiformula.Evalb, Semiformula.eval_rel,
      Structure.rel, Function.comp_def, val_boundDomainTerm]
    · exact Subtype.ext_iff.symm
    · rfl
  | nrel r ts =>
    cases r <;> simp only [boundedDomainFormula, Semiformula.Evalb, Semiformula.eval_nrel,
      Structure.rel, Function.comp_def, val_boundDomainTerm]
    · exact not_congr Subtype.ext_iff.symm
    · rfl
  | and φ ψ ihφ ihψ => exact and_congr (ihφ b) (ihψ b)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ b) (ihψ b)
  | @all n φ ih =>
    have hv (x : SetDomain U) : Fin.lastCases U (fun i ↦ ((x :> b) i).val) =
        x.val :> Fin.lastCases U (fun i ↦ (b i).val) :=
      (congrArg (fun v : Fin (n + 1) → V ↦ (Fin.lastCases U v : Fin (n + 2) → V)) (setDomain_val_vecCons U x b)).trans (lastCases_cons U x.val _)
    rw [boundedDomainFormula, eval_boundedSetAll]
    simp only [Semiterm.val_bvar, Fin.lastCases_last]
    change (∀ x ∈ U, (boundedDomainFormula φ).Evalb (x :> Fin.lastCases U (fun i ↦ (b i).val))) ↔
      ∀ x : SetDomain U, φ.Evalb (x :> b)
    constructor
    · intro h x
      apply (ih (x :> b)).mp
      rw [hv]
      exact h x.val x.property
    · intro h x hx
      have he := (ih ((⟨x, hx⟩ : SetDomain U) :> b)).mpr (h ⟨x, hx⟩)
      rw [hv (⟨x, hx⟩ : SetDomain U)] at he
      exact he
  | @exs n φ ih =>
    have hv (x : SetDomain U) : Fin.lastCases U (fun i ↦ ((x :> b) i).val) =
        x.val :> Fin.lastCases U (fun i ↦ (b i).val) :=
      (congrArg (fun v : Fin (n + 1) → V ↦ (Fin.lastCases U v : Fin (n + 2) → V)) (setDomain_val_vecCons U x b)).trans (lastCases_cons U x.val _)
    rw [boundedDomainFormula, eval_boundedSetExs]
    simp only [Semiterm.val_bvar, Fin.lastCases_last]
    change (∃ x ∈ U, (boundedDomainFormula φ).Evalb (x :> Fin.lastCases U (fun i ↦ (b i).val))) ↔
      ∃ x : SetDomain U, φ.Evalb (x :> b)
    constructor
    · rintro ⟨x, hx, he⟩
      refine ⟨⟨x, hx⟩, (ih ((⟨x, hx⟩ : SetDomain U) :> b)).mp ?_⟩
      rw [hv (⟨x, hx⟩ : SetDomain U)]
      exact he
    · rintro ⟨x, hx⟩
      refine ⟨x.val, x.property, ?_⟩
      have he := (ih (x :> b)).mpr hx
      simpa only [hv] using he

theorem eval_boundedDomainFormula_two (U : V) (φ : SetTheorySemisentence 2)
    (x y : SetDomain U) :
    (boundedDomainFormula φ).Evalb ![x.val, y.val, U] ↔ φ.Evalb ![x, y] := by
  have hv : Fin.lastCases U (fun i ↦ ((![x, y] : Fin 2 → SetDomain U) i).val) = ![x.val, y.val, U] := by
    funext i
    repeat' first | exact rfl | exact Fin.elim0 i | (refine Fin.cases ?_ (fun i ↦ ?_) i)
  simpa only [hv] using eval_boundedDomainFormula U φ ![x, y]

end ZFVP
