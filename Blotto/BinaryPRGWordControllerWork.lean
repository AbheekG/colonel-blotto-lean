import Blotto.BinaryPRGWordControllerRequest
import Blotto.BinaryPRGFrameCostJoin

/-! Reached work for the concrete Store/Boolean-PC segment caller.  The
categorical interpreter is the implemented quadratic Boolean interpreter;
the midpoint producer executes its direct odd/power-of-two Boolean path.
Factory and route callers are not assigned a price by output equality.

The ledger counts Boolean/list cells and conservative array producer visits.
Logical indexed table reads, their address representation and whole-caller
factory/emission work remain separate until their concrete interpreter joins.
-/

namespace Blotto.BinaryPRGWordControllerWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryStoredOverlapEnvironment BinaryRationalExpression
open scoped BigOperators

def pointWithWork {n k : ℕ} (table : Segment n k) (slot : Fin k)
    (K : ℕ) (bits : Fin K → Bool) : FixedArrayTable n SignedWord × ℕ :=
  let scalar := BinaryDirectDyadicMidpoint.sampleWithWork (List.ofFn bits)
  let cells := FixedArrayTable.ofFn (fun j => BinaryQuadraticExpression.run
    (BinarySegmentPoint.environment ((table.P.read slot).read j)
      ((table.Q.read slot).read j) scalar.1) BinarySegmentPoint.program.compile)
  (FixedArrayTable.ofFn (fun j => (cells.read j).1.1),
    scalar.2 + 4 * K + 1 + (∑ j, (cells.read j).2) + 6 * n + n * (n + 1) + 2)

theorem pointWithWork_erasure {n k : ℕ} (table : Segment n k) (slot : Fin k)
    (K : ℕ) (bits : Fin K → Bool) :
    (pointWithWork table slot K bits).1 = BinaryPRGWordControllerSegment.point table slot K bits := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [pointWithWork, BinaryPRGWordControllerSegment.point,
    FixedArrayTable.read_ofFn, BinaryDirectDyadicMidpoint.sampleWithWork_state,
    BinaryQuadraticData.expression_erasure]
  rfl

theorem pointWithWork_recorded {n k : ℕ} (table : Segment n k) (slot : Fin k)
    (K : ℕ) (bits : Fin K → Bool) :
    (pointWithWork table slot K bits).2 =
      (BinaryDirectDyadicMidpoint.sampleWithWork (List.ofFn bits)).2 + 4 * K + 1 +
        BinaryPRGWordControllerSegment.pointExpressionWork table slot K bits +
          6 * n + n * (n + 1) + 2 := by
  simp only [pointWithWork, BinaryPRGWordControllerSegment.pointExpressionWork,
    BinaryDirectDyadicMidpoint.sampleWithWork_state, BinaryDirectDyadicMidpoint.sample_ofFn, FixedArrayTable.read_ofFn]

def pointBound (n s K : ℕ) : ℕ :=
  20 * (K + 2) + 4 * K + 1 + 9 * n *
    BinaryQuadraticExpression.uniformPrice (expressionHeightBudget (max s (K + 2)) 3) +
      6 * n + n * (n + 1) + 2

theorem pointWithWork_bound {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ slot j, RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s)
    (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    (pointWithWork table slot K bits).2 ≤ pointBound n s K := by
  rw [pointWithWork_recorded]
  have hMid := BinaryDirectDyadicMidpoint.sampleWithWork_bound (List.ofFn bits)
  rw [List.length_ofFn] at hMid
  have hExpr := BinaryPRGWordControllerSegment.pointExpressionWork_bound table hC s hs hHeight slot K bits
  unfold pointBound
  omega

def selectionBound (k s indexWidth span : ℕ) : ℕ :=
  let W := 1 + k * s
  let body := BinaryWordIndexCoinController.allowance (5 + 8 * W) indexWidth
  let preparation := (k + 1) * (11000 * (2 + 2 * W)^2 + 2) +
    500 * (2 + 2 * W)^2 + 4
  (k + 1) * (preparation + 12 * (6 + 8 * W) + body + 2) + span * body

def segmentWithWork {n k : ℕ} (store : Store)
    (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : Fin K → Bool) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerSegment.Result store n × ℕ :=
  let selected := BinaryPRGWordControllerCategorical.run store fallback
    (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp
  match selected.1.1 with
  | none => ((none, selected.1.2), selected.2 + 3 * k + 3)
  | some slot =>
      let emitted := pointWithWork prepared.table slot K scalar
      ((some emitted.1, selected.1.2), selected.2 + emitted.2 + 3 * k + 3)

theorem segmentWithWork_erasure {n k : ℕ} (store : Store)
    (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : Fin K → Bool) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (segmentWithWork store prepared fallback K scalar pc hp).1 =
      BinaryPRGWordControllerSegment.run store prepared fallback K scalar pc hp := by
  unfold segmentWithWork BinaryPRGWordControllerSegment.run
  dsimp only
  rw [← BinaryPRGWordControllerDataCategorical.run_erasure]
  split
  · rename_i hNone
    simp only [hNone, Option.map_none]
  · rename_i slot hSlot
    simp only [hSlot, pointWithWork_erasure, Option.map_some]

def segmentBound (n k s K indexWidth span : ℕ) : ℕ :=
  selectionBound k s indexWidth span + pointBound n s K + 3 * k + 3

theorem segmentWithWork_bound {n k : ℕ} (store : Store)
    (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 2 ≤ s)
    (hWeight : ∀ slot, RationalHeight (source.weight slot) s)
    (hHeight : ∀ slot j, RationalHeight (value ((prepared.table.P.read slot).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) s)
    (fallback : Fin k) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (segmentWithWork store prepared fallback K scalar pc hp).2 ≤
      segmentBound n k s K store.width (store.cap.value - pc.value) := by
  let weights := NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative
  have hRun := BinaryPRGWordControllerCategorical.run_bound
    (BinaryStoredSegmentChoiceWork.denominator prepared.table)
    (BinaryStoredSegmentChoiceWork.denominator_positive prepared.table) store fallback weights
    (BinaryStoredSegmentChoiceWork.source_unit prepared source hR) pc hp
  have hWidth := BinaryStoredSegmentChoiceWork.denominator_width prepared.table s
    (fun slot => by rw [hR.1 slot]; exact hWeight slot)
  have hPosition := BinaryPRGWordControllerCategorical.run_position_bounds store fallback weights pc hp
  have hSpan : (BinaryPRGWordControllerCategorical.run store fallback weights pc hp).1.2.value - pc.value ≤
      store.cap.value - pc.value := Nat.sub_le_sub_right hPosition.2 _
  have hSelection : (BinaryPRGWordControllerCategorical.run store fallback weights pc hp).2 ≤
      selectionBound k s store.width (store.cap.value - pc.value) := by
    apply hRun.trans
    have hLength : weights.items.length = k := List.length_ofFn
    rw [hLength]
    unfold BinaryPRGWordControllerCategorical.bound BinaryPRGWordControllerCategorical.choiceBound
      BinaryPRGWordControllerPreparation.preparationBound BinaryPRGWordControllerCategorical.bodyBound
      selectionBound BinaryWordIndexCoinController.allowance
    dsimp only
    gcongr
  dsimp [weights] at hSelection
  unfold segmentWithWork segmentBound
  dsimp only
  split
  · omega
  · rename_i slot hSlot
    have hPoint := pointWithWork_bound prepared.table prepared.canonical s hs hHeight slot K scalar
    omega

/-- The Store is built from exactly the supplied canonical choice list; the
counting and padded-tree production are included independently of draw work. -/
def storeWithWork (seed : List Bool) : Store × ℕ :=
  (BinarySeedLookupTree.prepare seed, BinarySeedLookupTree.preparationCells seed)

theorem storeWithWork_erasure (seed : List Bool) :
    (storeWithWork seed).1 = BinarySeedLookupTree.prepare seed := rfl

theorem storeWithWork_bound (seed : List Bool) :
    (storeWithWork seed).2 ≤ 33 * seed.length + 6 :=
  BinarySeedLookupTree.preparationCells_bound seed

end Blotto.BinaryPRGWordControllerWork
