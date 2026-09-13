import ZFVP.ModelTheory.InfinitaryWeakRewriting
import ZFVP.ModelTheory.InfinitaryFragmentClosure
import Foundation.FirstOrder.Basic.Semantics.Elementary

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v w

/-- A countable nonempty structure with actual equality and an extensional,
monotone quantifier on subsets. -/
structure WeakModel (L : Language.{u}) [L.Eq] where
  Domain : Type v
  str : Structure L Domain
  eq : @Structure.Eq L Domain str _
  nonempty : Nonempty Domain
  countable : Countable Domain
  Q : Set Domain → Prop
  mono : Monotone Q

attribute [instance] WeakModel.str WeakModel.eq WeakModel.nonempty WeakModel.countable

structure WeakElementaryMap {L : Language.{u}} [L.Eq] (T : Set (TaggedFormula L))
    (M : WeakModel.{u,v} L) (N : WeakModel.{u,w} L) where
  toFun : M.Domain → N.Domain
  injective : Function.Injective toFun
  func : ∀ {n} (f : L.Func n) (b : Fin n → M.Domain),
    toFun (Structure.func f b) = Structure.func f (toFun ∘ b)
  rel : ∀ {n} (r : L.Rel n) (b : Fin n → M.Domain),
    Structure.rel r (toFun ∘ b) ↔ Structure.rel r b
  elementary : ∀ {n} (φ : Formula L n), ⟨n, φ⟩ ∈ T → ∀ b : Fin n → M.Domain,
    Formula.WeakEval N.Q φ (toFun ∘ b) ↔ Formula.WeakEval M.Q φ b

instance {L : Language.{u}} [L.Eq] {T : Set (TaggedFormula L)}
    {M : WeakModel.{u,v} L} {N : WeakModel.{u,w} L} :
    CoeFun (WeakElementaryMap T M N) (fun _ ↦ M.Domain → N.Domain) := ⟨fun f ↦ f.toFun⟩

/-- A coherent increasing omega-chain elementary for one fixed closed fragment. -/
structure WeakOmegaChain {L : Language.{u}} [L.Eq] [L.Encodable]
    (S : Set (TaggedFormula L)) where
  model : ℕ → WeakModel.{u,v} L
  map : ∀ {i j}, i ≤ j → WeakElementaryMap (FragmentClosure.carrier S) (model i) (model j)
  identity : ∀ i (h : i ≤ i) x, map h x = x
  composition : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) x,
    map hjk (map hij x) = map (hij.trans hjk) x

namespace WeakOmegaChain
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  (C : WeakOmegaChain.{u,v} S)

abbrev Point := Σ i, (C.model i).Domain

def Equal (x y : C.Point) : Prop :=
  ∃ k, ∃ hx : x.1 ≤ k, ∃ hy : y.1 ≤ k, C.map hx x.2 = C.map hy y.2

theorem equal_iff_at {i j k} (x : (C.model i).Domain) (y : (C.model j).Domain)
    (hi : i ≤ k) (hj : j ≤ k) :
    C.Equal ⟨i, x⟩ ⟨j, y⟩ ↔ C.map hi x = C.map hj y := by
  constructor
  · rintro ⟨m, him, hjm, he⟩
    apply (C.map (Nat.le_max_left k m)).injective
    have hi' : C.map (Nat.le_max_left k m) (C.map hi x) =
        C.map (Nat.le_max_right k m) (C.map him x) := by rw [C.composition, C.composition]
    have hj' : C.map (Nat.le_max_left k m) (C.map hj y) =
        C.map (Nat.le_max_right k m) (C.map hjm y) := by rw [C.composition, C.composition]
    rw [hi', hj', he]
  · exact fun he ↦ ⟨k, hi, hj, he⟩

def pointSetoid : Setoid C.Point where
  r := C.Equal
  iseqv := by
    refine ⟨fun x ↦ ⟨x.1, le_refl _, le_refl _, rfl⟩, ?_, ?_⟩
    · rintro x y ⟨k, hx, hy, he⟩
      exact ⟨k, hy, hx, he.symm⟩
    · intro x y z hxy hyz
      let k := max (max x.1 y.1) z.1
      have hx : x.1 ≤ k := (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
      have hy : y.1 ≤ k := (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
      have hz : z.1 ≤ k := Nat.le_max_right _ _
      exact ⟨k, hx, hz, ((C.equal_iff_at x.2 y.2 hx hy).mp hxy).trans
        ((C.equal_iff_at y.2 z.2 hy hz).mp hyz)⟩

def Limit : Type v := Quotient C.pointSetoid

def fromStage (i : ℕ) (x : (C.model i).Domain) : C.Limit := Quotient.mk C.pointSetoid ⟨i, x⟩

theorem fromStage_eq_iff {i j k} (x : (C.model i).Domain) (y : (C.model j).Domain)
    (hi : i ≤ k) (hj : j ≤ k) :
    C.fromStage i x = C.fromStage j y ↔ C.map hi x = C.map hj y :=
  Quotient.eq.trans (C.equal_iff_at x y hi hj)

theorem fromStage_injective (i : ℕ) : Function.Injective (C.fromStage i) := by
  intro x y he
  have h := (C.fromStage_eq_iff x y (le_refl i) (le_refl i)).mp he
  simpa only [C.identity] using h

theorem fromStage_coherent {i j} (h : i ≤ j) (x : (C.model i).Domain) :
    C.fromStage j (C.map h x) = C.fromStage i x := by
  apply (C.fromStage_eq_iff _ _ (le_refl j) h).mpr
  exact C.identity j (le_refl j) _

theorem fromStage_comp {i j} (h : i ≤ j) :
    C.fromStage j ∘ C.map h = C.fromStage i := funext (C.fromStage_coherent h)

theorem stage_cover (x : C.Limit) : ∃ i, ∃ a : (C.model i).Domain, C.fromStage i a = x := by
  induction x using Quotient.inductionOn with
  | _ x => exact ⟨x.1, x.2, rfl⟩

theorem tuple_cover {n} (b : Fin n → C.Limit) :
    ∃ i, ∃ a : Fin n → (C.model i).Domain, C.fromStage i ∘ a = b := by
  classical
  choose i a ha using fun j ↦ C.stage_cover (b j)
  let k := Finset.univ.sup i
  have hi (j : Fin n) : i j ≤ k := Finset.le_sup (by simp)
  refine ⟨k, fun j ↦ C.map (hi j) (a j), ?_⟩
  funext j
  exact (C.fromStage_coherent (hi j) (a j)).trans (ha j)

instance limit_countable : Countable C.Limit :=
  inferInstanceAs (Countable (Quotient C.pointSetoid))

instance limit_nonempty : Nonempty C.Limit :=
  Nonempty.map (C.fromStage 0) inferInstance

theorem map_cons {i j n} (h : i ≤ j) (x : (C.model i).Domain)
    (b : Fin n → (C.model i).Domain) : C.map h ∘ (x :> b) = C.map h x :> C.map h ∘ b := by
  funext k
  cases k using Fin.cases <;> rfl

theorem fromStage_cons {i n} (x : (C.model i).Domain) (b : Fin n → (C.model i).Domain) :
    C.fromStage i ∘ (x :> b) = C.fromStage i x :> C.fromStage i ∘ b := by
  funext k
  cases k using Fin.cases <;> rfl

theorem stage_eval_congr {n i j} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S)
    (b : Fin n → (C.model i).Domain) (c : Fin n → (C.model j).Domain)
    (he : C.fromStage i ∘ b = C.fromStage j ∘ c) :
    Formula.WeakEval (C.model i).Q φ b ↔ Formula.WeakEval (C.model j).Q φ c := by
  have hb := (C.map (Nat.le_max_left i j)).elementary φ hφ b
  have hc := (C.map (Nat.le_max_right i j)).elementary φ hφ c
  have hbc : C.map (Nat.le_max_left i j) ∘ b = C.map (Nat.le_max_right i j) ∘ c := by
    funext l
    exact (C.fromStage_eq_iff (b l) (c l) (Nat.le_max_left i j)
      (Nat.le_max_right i j)).mp (congrFun he l)
  exact hb.symm.trans (hbc ▸ hc)

/-- Evaluation read at any common source stage of the finite tuple. -/
def StageEval {n} (φ : Formula L n) (b : Fin n → C.Limit) : Prop :=
  ∃ i, ∃ a : Fin n → (C.model i).Domain,
    C.fromStage i ∘ a = b ∧ Formula.WeakEval (C.model i).Q φ a

theorem stageEval_fromStage {n i} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S) (b : Fin n → (C.model i).Domain) :
    C.StageEval φ (C.fromStage i ∘ b) ↔ Formula.WeakEval (C.model i).Q φ b := by
  constructor
  · rintro ⟨j, c, hc, ht⟩
    exact (C.stage_eval_congr φ hφ c b hc).mp ht
  · exact fun ht ↦ ⟨i, b, rfl, ht⟩

end WeakOmegaChain
end ZFVP.Infinitary
