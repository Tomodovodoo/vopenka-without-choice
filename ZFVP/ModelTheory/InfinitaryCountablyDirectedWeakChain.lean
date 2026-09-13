import ZFVP.ModelTheory.InfinitaryWeakChain

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v w

/-- A weak structure without a cardinality restriction on its domain. -/
structure WeakLimitStructure (L : Language.{u}) [L.Eq] where
  Domain : Type v
  str : Structure L Domain
  eq : @Structure.Eq L Domain str _
  nonempty : Nonempty Domain
  Q : Set Domain → Prop
  mono : Monotone Q

attribute [instance] WeakLimitStructure.str WeakLimitStructure.eq WeakLimitStructure.nonempty

structure WeakLimitEmbedding {L : Language.{u}} [L.Eq] (T : Set (TaggedFormula L))
    (M : WeakModel.{u,v} L) (N : WeakLimitStructure.{u,w} L) where
  toFun : M.Domain → N.Domain
  injective : Function.Injective toFun
  func : ∀ {n} (f : L.Func n) (b : Fin n → M.Domain),
    toFun (Structure.func f b) = Structure.func f (toFun ∘ b)
  rel : ∀ {n} (r : L.Rel n) (b : Fin n → M.Domain),
    Structure.rel r (toFun ∘ b) ↔ Structure.rel r b
  elementary : ∀ {n} (φ : Formula L n), ⟨n, φ⟩ ∈ T → ∀ b : Fin n → M.Domain,
    Formula.WeakEval N.Q φ (toFun ∘ b) ↔ Formula.WeakEval M.Q φ b

instance {L : Language.{u}} [L.Eq] {T : Set (TaggedFormula L)}
    {M : WeakModel.{u,v} L} {N : WeakLimitStructure.{u,w} L} :
    CoeFun (WeakLimitEmbedding T M N) (fun _ ↦ M.Domain → N.Domain) := ⟨fun f ↦ f.toFun⟩

/-- A coherent system with a common upper bound for every countable family of
indices. Its stages are elementary for one fixed closed fragment. -/
structure WeakDirectedChain {L : Language.{u}} [L.Eq] [L.Encodable]
    (I : Type v) [Preorder I] [Nonempty I] (S : Set (TaggedFormula L)) where
  bounded : ∀ f : ℕ → I, ∃ k, ∀ n, f n ≤ k
  model : I → WeakModel.{u,w} L
  map : ∀ {i j}, i ≤ j → WeakElementaryMap (FragmentClosure.carrier S) (model i) (model j)
  identity : ∀ i (h : i ≤ i) x, map h x = x
  composition : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) x,
    map hjk (map hij x) = map (hij.trans hjk) x

namespace WeakDirectedChain
variable {L : Language.{u}} [L.Eq] [L.Encodable] {I : Type v} [Preorder I] [Nonempty I]
  {S : Set (TaggedFormula L)} (C : WeakDirectedChain.{u,v,w} I S)

noncomputable def upper (i j : I) : I := (C.bounded (fun n ↦ if n = 0 then i else j)).choose

theorem le_upper_left (i j : I) : i ≤ C.upper i j := by
  simpa only [upper, ite_true] using (C.bounded (fun n ↦ if n = 0 then i else j)).choose_spec 0

theorem le_upper_right (i j : I) : j ≤ C.upper i j := by
  simpa only [upper, show (1 : ℕ) ≠ 0 from Nat.one_ne_zero, ite_false] using
    (C.bounded (fun n ↦ if n = 0 then i else j)).choose_spec 1

abbrev Point := Σ i, (C.model i).Domain

def Equal (x y : C.Point) : Prop :=
  ∃ k, ∃ hx : x.1 ≤ k, ∃ hy : y.1 ≤ k, C.map hx x.2 = C.map hy y.2

theorem equal_iff_at {i j k} (x : (C.model i).Domain) (y : (C.model j).Domain)
    (hi : i ≤ k) (hj : j ≤ k) :
    C.Equal ⟨i, x⟩ ⟨j, y⟩ ↔ C.map hi x = C.map hj y := by
  constructor
  · rintro ⟨m, him, hjm, he⟩
    apply (C.map (C.le_upper_left k m)).injective
    have hi' : C.map (C.le_upper_left k m) (C.map hi x) =
        C.map (C.le_upper_right k m) (C.map him x) := by rw [C.composition, C.composition]
    have hj' : C.map (C.le_upper_left k m) (C.map hj y) =
        C.map (C.le_upper_right k m) (C.map hjm y) := by rw [C.composition, C.composition]
    rw [hi', hj', he]
  · exact fun he ↦ ⟨k, hi, hj, he⟩

def pointSetoid : Setoid C.Point where
  r := C.Equal
  iseqv := by
    refine ⟨fun x ↦ ⟨x.1, le_refl _, le_refl _, rfl⟩, ?_, ?_⟩
    · rintro x y ⟨k, hx, hy, he⟩
      exact ⟨k, hy, hx, he.symm⟩
    · intro x y z hxy hyz
      let k := C.upper (C.upper x.1 y.1) z.1
      have hx : x.1 ≤ k := (C.le_upper_left _ _).trans (C.le_upper_left _ _)
      have hy : y.1 ≤ k := (C.le_upper_right _ _).trans (C.le_upper_left _ _)
      have hz : z.1 ≤ k := C.le_upper_right _ _
      exact ⟨k, hx, hz, ((C.equal_iff_at x.2 y.2 hx hy).mp hxy).trans
        ((C.equal_iff_at y.2 z.2 hy hz).mp hyz)⟩

def Limit : Type (max v w) := Quotient C.pointSetoid

def fromStage (i : I) (x : (C.model i).Domain) : C.Limit := Quotient.mk C.pointSetoid ⟨i, x⟩

theorem fromStage_eq_iff {i j k} (x : (C.model i).Domain) (y : (C.model j).Domain)
    (hi : i ≤ k) (hj : j ≤ k) :
    C.fromStage i x = C.fromStage j y ↔ C.map hi x = C.map hj y :=
  Quotient.eq.trans (C.equal_iff_at x y hi hj)

theorem fromStage_injective (i : I) : Function.Injective (C.fromStage i) := by
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
  let d : I := Classical.choice inferInstance
  let f : ℕ → I := fun m ↦ if h : m < n then i ⟨m, h⟩ else d
  obtain ⟨k, hk⟩ := C.bounded f
  have hi (j : Fin n) : i j ≤ k := by simpa [f, j.isLt] using hk j.val
  refine ⟨k, fun j ↦ C.map (hi j) (a j), ?_⟩
  funext j
  exact (C.fromStage_coherent (hi j) (a j)).trans (ha j)

theorem countable_cover (b : ℕ → C.Limit) :
    ∃ i, ∀ n, ∃ a : (C.model i).Domain, C.fromStage i a = b n := by
  classical
  choose j a ha using fun n ↦ C.stage_cover (b n)
  obtain ⟨i, hi⟩ := C.bounded j
  exact ⟨i, fun n ↦ ⟨C.map (hi n) (a n), (C.fromStage_coherent (hi n) (a n)).trans (ha n)⟩⟩

instance limit_countable [Countable I] : Countable C.Limit :=
  inferInstanceAs (Countable (Quotient C.pointSetoid))

instance limit_nonempty : Nonempty C.Limit := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact Nonempty.map (C.fromStage i) inferInstance

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
  have hb := (C.map (C.le_upper_left i j)).elementary φ hφ b
  have hc := (C.map (C.le_upper_right i j)).elementary φ hφ c
  have hbc : C.map (C.le_upper_left i j) ∘ b = C.map (C.le_upper_right i j) ∘ c := by
    funext l
    exact (C.fromStage_eq_iff (b l) (c l) (C.le_upper_left i j)
      (C.le_upper_right i j)).mp (congrFun he l)
  exact hb.symm.trans (hbc ▸ hc)

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

end WeakDirectedChain
end ZFVP.Infinitary
