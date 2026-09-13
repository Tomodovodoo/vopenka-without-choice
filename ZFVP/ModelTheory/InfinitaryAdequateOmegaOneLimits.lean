import ZFVP.ModelTheory.InfinitaryAdequateGrowthBlock
import ZFVP.ModelTheory.InfinitaryOmegaOneFreezing

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v

/-- A coherent system on a countable linear order. No countable-upper-bound
condition is imposed on the index order. -/
structure CountableWeakDiagram (I : Type) [LinearOrder I]
    {L : Language.{u}} [L.Eq] [L.Encodable] (S : Set (TaggedFormula L)) where
  model : I → WeakModel.{u,v} L
  map : ∀ {i j}, i ≤ j → WeakElementaryMap (FragmentClosure.carrier S) (model i) (model j)
  identity : ∀ i (h : i ≤ i) x, map h x = x
  composition : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) x,
    map hjk (map hij x) = map (hij.trans hjk) x

namespace CountableWeakDiagram
variable {I : Type} [LinearOrder I] [Countable I] [Nonempty I]

private noncomputable def enumIndex : ℕ → I := (exists_surjective_nat I).choose
omit [LinearOrder I] in
private theorem enumIndex_surjective : Function.Surjective (enumIndex (I := I)) :=
  (exists_surjective_nat I).choose_spec

noncomputable def cofinalIndex : ℕ → I
  | 0 => enumIndex 0
  | n + 1 => max (cofinalIndex n) (enumIndex (n + 1))

theorem cofinalIndex_mono : Monotone (cofinalIndex (I := I)) :=
  monotone_nat_of_le_succ (fun _ ↦ le_max_left _ _)

theorem cofinalIndex_cofinal (i : I) : ∃ n, i ≤ cofinalIndex n := by
  obtain ⟨n, rfl⟩ := enumIndex_surjective (I := I) i
  cases n with
  | zero => exact ⟨0, le_refl _⟩
  | succ n => exact ⟨n + 1, le_max_right _ _⟩

variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  (D : CountableWeakDiagram.{u,v} I S)

noncomputable def omegaChain : WeakOmegaChain.{u,v} S where
  model := fun n ↦ D.model (cofinalIndex n)
  map := fun h ↦ D.map (cofinalIndex_mono h)
  identity := fun i _ x ↦ D.identity (cofinalIndex i) _ x
  composition := fun hij hjk x ↦ D.composition (cofinalIndex_mono hij) (cofinalIndex_mono hjk) x

private noncomputable def coverIndex (i : I) : ℕ := (cofinalIndex_cofinal i).choose
private theorem le_coverIndex (i : I) : i ≤ cofinalIndex (coverIndex i) :=
  (cofinalIndex_cofinal i).choose_spec

noncomputable def limitEmbedding (i : I) :
    WeakElementaryMap (FragmentClosure.carrier S) (D.model i) D.omegaChain.limitModel :=
  (D.omegaChain.limitEmbedding (coverIndex i)).comp (D.map (le_coverIndex i))

theorem limitEmbedding_eq_at (i : I) (n : ℕ) (h : i ≤ cofinalIndex n) (x : (D.model i).Domain) :
    D.limitEmbedding i x = D.omegaChain.fromStage n (D.map h x) := by
  change D.omegaChain.fromStage (coverIndex i) (D.map (le_coverIndex i) x) = _
  apply (D.omegaChain.fromStage_eq_iff _ _ (Nat.le_max_left (coverIndex i) n)
    (Nat.le_max_right (coverIndex i) n)).mpr
  change D.map _ (D.map _ x) = D.map _ (D.map _ x)
  rw [D.composition, D.composition]

theorem limitEmbedding_coherent {i j : I} (h : i ≤ j) (x : (D.model i).Domain) :
    D.limitEmbedding j (D.map h x) = D.limitEmbedding i x := by
  obtain ⟨n, hn⟩ := cofinalIndex_cofinal j
  rw [D.limitEmbedding_eq_at j n hn, D.limitEmbedding_eq_at i n (h.trans hn), D.composition]

theorem limitEmbedding_cover (x : D.omegaChain.limitModel.Domain) :
    ∃ i, ∃ a : (D.model i).Domain, D.limitEmbedding i a = x := by
  obtain ⟨n, a, rfl⟩ := D.omegaChain.stage_cover x
  change (D.model (cofinalIndex n)).Domain at a
  refine ⟨cofinalIndex n, a, ?_⟩
  rw [D.limitEmbedding_eq_at (cofinalIndex n) n (le_refl _), D.identity]

theorem omegaChain_freezes
    (hf : ∀ i j (h : i ≤ j), (D.map h).FreezesSmallFibers) :
    ∀ i j (h : i ≤ j), (D.omegaChain.map h).FreezesSmallFibers :=
  fun _ _ h ↦ hf _ _ (cofinalIndex_mono h)

theorem limitEmbedding_freezes
    (hf : ∀ i j (h : i ≤ j), (D.map h).FreezesSmallFibers) (i : I) :
    (D.limitEmbedding i).FreezesSmallFibers :=
  WeakElementaryMap.comp_freezes (D.map (le_coverIndex i))
    (D.omegaChain.limitEmbedding (coverIndex i)) (hf _ _ _)
    (D.omegaChain.limitEmbedding_freezes (D.omegaChain_freezes hf) _)

/-- The limit of a countable predecessor diagram is the actual weak omega
limit of a chosen cofinal sequence. -/
theorem exists_adequate_limit
    (D : CountableWeakDiagram.{u,v} I (SequenceClosure.carrier S))
    (ha : ∀ i, (D.model i).Adequate S)
    (hf : ∀ i j (h : i ≤ j), (D.map h).FreezesSmallFibers) :
    ∃ N : WeakModel.{u,v} L,
      ∃ e : ∀ i, WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) (D.model i) N,
        N.Adequate S ∧ (∀ i, (e i).FreezesSmallFibers) ∧
          (∀ i j (h : i ≤ j) x, e j (D.map h x) = e i x) ∧
          ∀ x : N.Domain, ∃ i, ∃ a : (D.model i).Domain, e i a = x :=
  ⟨D.omegaChain.limitModel, D.limitEmbedding,
    D.omegaChain.limit_adequate (fun n ↦ ha (cofinalIndex n)),
    D.limitEmbedding_freezes hf, (fun _ _ h x ↦ D.limitEmbedding_coherent h x), D.limitEmbedding_cover⟩

end CountableWeakDiagram
end ZFVP.Infinitary


