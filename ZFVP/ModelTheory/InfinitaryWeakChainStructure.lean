import ZFVP.ModelTheory.InfinitaryWeakChain

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakOmegaChain
open FragmentClosure
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  (C : WeakOmegaChain.{u,v} S)

omit [L.Eq] in
theorem firstOrder_in_fragment {n} (φ : Semisentence L n) :
    ⟨n, Formula.fo φ⟩ ∈ FragmentClosure.carrier S :=
  firstOrder_subset_carrier S (Or.inl ⟨⟨n, φ⟩, rfl⟩)

theorem stage_func_congr {n i j} (f : L.Func n)
    (b : Fin n → (C.model i).Domain) (c : Fin n → (C.model j).Domain)
    (he : C.fromStage i ∘ b = C.fromStage j ∘ c) :
    C.fromStage i (Structure.func f b) = C.fromStage j (Structure.func f c) := by
  apply (C.fromStage_eq_iff _ _ (Nat.le_max_left i j) (Nat.le_max_right i j)).mpr
  rw [(C.map (Nat.le_max_left i j)).func, (C.map (Nat.le_max_right i j)).func]
  congr 1
  funext l
  exact (C.fromStage_eq_iff (b l) (c l) (Nat.le_max_left i j)
    (Nat.le_max_right i j)).mp (congrFun he l)

noncomputable def tupleStage {n} (b : Fin n → C.Limit) : ℕ := (C.tuple_cover b).choose

noncomputable def tupleValue {n} (b : Fin n → C.Limit) :
    Fin n → (C.model (C.tupleStage b)).Domain := (C.tuple_cover b).choose_spec.choose

theorem tupleValue_spec {n} (b : Fin n → C.Limit) :
    C.fromStage (C.tupleStage b) ∘ C.tupleValue b = b := (C.tuple_cover b).choose_spec.choose_spec

noncomputable instance limitStructure : Structure L C.Limit where
  func := fun _ f b ↦ C.fromStage (C.tupleStage b) (Structure.func f (C.tupleValue b))
  rel := fun _ r b ↦ C.StageEval (.fo (.rel r Semiterm.bvar)) b

theorem func_fromStage {n i} (f : L.Func n) (b : Fin n → (C.model i).Domain) :
    Structure.func (self := C.limitStructure) f (C.fromStage i ∘ b) =
      C.fromStage i (Structure.func f b) :=
  C.stage_func_congr f _ b (C.tupleValue_spec _)

theorem rel_fromStage {n i} (r : L.Rel n) (b : Fin n → (C.model i).Domain) :
    Structure.rel (self := C.limitStructure) r (C.fromStage i ∘ b) ↔ Structure.rel r b :=
  C.stageEval_fromStage (.fo (.rel r Semiterm.bvar)) (firstOrder_in_fragment _) b

theorem term_fromStage {n i} (t : Semiterm L Empty n) (b : Fin n → (C.model i).Domain) :
    Semiterm.val (s := C.limitStructure) (C.fromStage i ∘ b) Empty.elim t =
      C.fromStage i (t.val b Empty.elim) := by
  induction t with
  | bvar l => rfl
  | fvar e => exact e.elim
  | func f ts ih =>
    change Structure.func f (fun l ↦ Semiterm.val _ _ (ts l)) = _
    rw [funext ih]
    exact C.func_fromStage f _

instance limitStructure_eq : Structure.Eq L C.Limit where
  eq a b := by
    obtain ⟨i, c, hc⟩ := C.tuple_cover ![a, b]
    have ha : C.fromStage i (c 0) = a := congrFun hc 0
    have hb : C.fromStage i (c 1) = b := congrFun hc 1
    change Structure.rel (self := C.limitStructure) (Language.Eq.eq (L := L)) ![a, b] ↔ a = b
    rw [← hc, C.rel_fromStage]
    have he : c = ![c 0, c 1] := by
      funext l
      cases l using Fin.cases with
      | zero => rfl
      | succ l => cases l using Fin.cases with
        | zero => rfl
        | succ l => exact l.elim0
    have hs : Structure.rel (self := (C.model i).str) (Language.Eq.eq (L := L)) c ↔ c 0 = c 1 := by
      rw [he]
      exact Structure.Eq.eq (L := L) (c 0) (c 1)
    exact hs.trans ⟨fun h ↦ ha.symm.trans ((congrArg (C.fromStage i) h).trans hb),
      fun h ↦ C.fromStage_injective i (ha.trans (h.trans hb.symm))⟩

theorem firstOrder_fromStage {n} (φ : Semisentence L n)
    (i : ℕ) (b : Fin n → (C.model i).Domain) :
    Semiformula.Eval (s := C.limitStructure) (C.fromStage i ∘ b) Empty.elim φ ↔
      Semiformula.Eval b Empty.elim φ := by
  induction φ generalizing i with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    change Structure.rel r (fun l ↦ Semiterm.val (s := C.limitStructure)
      (C.fromStage i ∘ b) Empty.elim (ts l)) ↔ _
    rw [funext (fun l ↦ C.term_fromStage (ts l) b)]
    exact C.rel_fromStage r _
  | nrel r ts =>
    change (¬Structure.rel r (fun l ↦ Semiterm.val (s := C.limitStructure)
      (C.fromStage i ∘ b) Empty.elim (ts l))) ↔ _
    rw [funext (fun l ↦ C.term_fromStage (ts l) b)]
    exact not_congr (C.rel_fromStage r _)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ i b) (ihψ i b)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ i b) (ihψ i b)
  | all φ ih =>
    change (∀ x : C.Limit, Semiformula.Eval (x :> C.fromStage i ∘ b) Empty.elim φ) ↔
      ∀ x : (C.model i).Domain, Semiformula.Eval (x :> b) Empty.elim φ
    constructor
    · intro h x
      have hx := h (C.fromStage i x)
      exact (ih i (x :> b)).mp (by simpa only [C.fromStage_cons] using hx)
    · intro h x
      obtain ⟨j, y, rfl⟩ := C.stage_cover x
      let k := max i j
      have hi : i ≤ k := Nat.le_max_left _ _
      have hj : j ≤ k := Nat.le_max_right _ _
      have hall := (C.map hi).elementary (.fo (.all φ)) (firstOrder_in_fragment _) b |>.mpr h
      have hy := (ih k (C.map hj y :> C.map hi ∘ b)).mpr (hall (C.map hj y))
      simpa only [C.fromStage_cons, ← Function.comp_assoc, C.fromStage_comp,
        C.fromStage_coherent] using hy
  | exs φ ih =>
    change (∃ x : C.Limit, Semiformula.Eval (x :> C.fromStage i ∘ b) Empty.elim φ) ↔
      ∃ x : (C.model i).Domain, Semiformula.Eval (x :> b) Empty.elim φ
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨j, y, rfl⟩ := C.stage_cover x
      let k := max i j
      have hi : i ≤ k := Nat.le_max_left _ _
      have hj : j ≤ k := Nat.le_max_right _ _
      have hy : Semiformula.Eval (C.map hj y :> C.map hi ∘ b) Empty.elim φ := by
        apply (ih k (C.map hj y :> C.map hi ∘ b)).mp
        simpa only [C.fromStage_cons, ← Function.comp_assoc, C.fromStage_comp,
          C.fromStage_coherent] using hx
      exact (C.map hi).elementary (.fo (.exs φ)) (firstOrder_in_fragment _) b |>.mp ⟨C.map hj y, hy⟩
    · rintro ⟨x, hx⟩
      refine ⟨C.fromStage i x, ?_⟩
      simpa only [C.fromStage_cons] using (ih i (x :> b)).mpr hx

theorem stageEval_firstOrder {n} (φ : Semisentence L n) (b : Fin n → C.Limit) :
    C.StageEval (.fo φ) b ↔ Semiformula.Eval (s := C.limitStructure) b Empty.elim φ := by
  obtain ⟨i, a, rfl⟩ := C.tuple_cover b
  rw [C.stageEval_fromStage (.fo φ) (firstOrder_in_fragment _), C.firstOrder_fromStage]
  rfl

end WeakOmegaChain
end ZFVP.Infinitary
