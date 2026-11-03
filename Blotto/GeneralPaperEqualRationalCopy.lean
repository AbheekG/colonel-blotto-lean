import Blotto.GeneralPaperScalarTableCopy

/-! Retained routes and rational segment tables are copied field by field
between explicit widths. Existing grouping and formula preparation is not
rerun. Data equalities preserve the exact prepared law. -/
namespace Blotto.GeneralPaperEqualRationalCopy
open GeneralPaperEncodedScalarStorage GeneralPaperEqualRetainedStorage
open GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def routes {n m : ℕ} {G : RationalProportionalGroups n m} (S A : ℕ) (source : PreparedGroupOutput G) :=
  let table := GeneralPaperReferenceCopy.array S A (GeneralPaperReferenceCopy.scalar S A (routeFoot A)) source.table
  let actual : PreparedGroupOutput G := ⟨table.1,by
    intro j
    rw [GeneralPaperReferenceCopy.array_data S A _ (fun _ => rfl)]
    exact source.correct j⟩
  (actual,table.2 + 64 * (S + A + 1))

theorem routes_data {n m : ℕ} {G : RationalProportionalGroups n m} (S A : ℕ) (source : PreparedGroupOutput G) :
    (routes S A source).1 = source := by
  apply GeneralPaperEqualRouteConstruction.prepared_eq
  exact GeneralPaperReferenceCopy.array_data S A _ (fun _ => rfl) source.table

def routesPrice (S A n m c : ℕ) : ℕ :=
  GeneralPaperReferenceCopy.arrayPrice S A n (4 + binaryWordWidth m + 2 * c + 16 * A + 32 * (S + A + 1)) +
    64 * (S + A + 1)

theorem routes_work {n m c : ℕ} {G : RationalProportionalGroups n m} (S A : ℕ) (source : PreparedGroupOutput G)
    (h : ∀ j,RationalHeight (source.table.read j).2 c) : (routes S A source).2 ≤ routesPrice S A n m c := by
  have ht := GeneralPaperReferenceCopy.array_bound S A
    (4 + binaryWordWidth m + 2 * c + 16 * A + 32 * (S + A + 1))
    (GeneralPaperReferenceCopy.scalar S A (routeFoot A)) source.table (by
      intro j
      have hj := route_bound A (source.table.read j) (h j)
      dsimp only [GeneralPaperReferenceCopy.scalar]
      omega)
  dsimp only [routes,routesPrice]
  omega

theorem routes_charged {n m : ℕ} {G : RationalProportionalGroups n m} (S A : ℕ) (source : PreparedGroupOutput G) :
    arrayFootprint A (routeFoot A) (routes S A source).1.table ≤ 16 * (routes S A source).2 := by
  have h := GeneralPaperReferenceCopy.array_charged S A 16
    (GeneralPaperReferenceCopy.scalar S A (routeFoot A)) (routeFoot A) source.table (by decide)
    (by intro j; dsimp only [GeneralPaperReferenceCopy.scalar]; omega)
  dsimp only [routes]
  nlinarith

def segments {m r : ℕ} {l : RationalSegmentLottery m r} (S A : ℕ) (source : PreparedSegmentDescriptor l) :=
  let weights := GeneralPaperScalarTableCopy.run S A rationalWordWidth source.weights
  let left := GeneralPaperScalarTableCopy.matrix S A source.left
  let right := GeneralPaperScalarTableCopy.matrix S A source.right
  let actual : PreparedSegmentDescriptor l :=
    ⟨weights.1,left.1,right.1,(by
      intro i; rw [GeneralPaperScalarTableCopy.data]; exact source.weight_correct i),(by
      intro i j; rw [GeneralPaperScalarTableCopy.matrix_data]; exact source.left_correct i j),(by
      intro i j; rw [GeneralPaperScalarTableCopy.matrix_data]; exact source.right_correct i j)⟩
  (actual,weights.2 + left.2 + right.2 + 128 * (S + A + 1))

theorem segments_data {m r : ℕ} {l : RationalSegmentLottery m r} (S A : ℕ) (source : PreparedSegmentDescriptor l) :
    (segments S A source).1 = source := GeneralPaperSegmentExpressionCompiler.unique _ _

def segmentsPrice (S A m r P : ℕ) : ℕ :=
  GeneralPaperScalarTableCopy.price S A r (r * P) +
    2 * GeneralPaperScalarTableCopy.matrixPrice S A m r P + 128 * (S + A + 1)

theorem segments_work {m r P : ℕ} {l : RationalSegmentLottery m r} (S A : ℕ) (source : PreparedSegmentDescriptor l)
    (hw : ∀ i,rationalWordWidth (source.weights.read i) ≤ P)
    (hl : ∀ i j,rationalWordWidth ((source.left.read i).read j) ≤ P)
    (hr : ∀ i j,rationalWordWidth ((source.right.read i).read j) ≤ P) :
    (segments S A source).2 ≤ segmentsPrice S A m r P := by
  have hW := GeneralPaperScalarTableCopy.bounded_work S A P rationalWordWidth source.weights hw
  have hL := GeneralPaperScalarTableCopy.matrix_work S A P source.left hl
  have hR := GeneralPaperScalarTableCopy.matrix_work S A P source.right hr
  dsimp only [segments,segmentsPrice]
  omega

theorem segments_charged {m r : ℕ} {l : RationalSegmentLottery m r} (S A : ℕ) (source : PreparedSegmentDescriptor l) :
    segmentFoot A (segments S A source).1 ≤ 16 * (segments S A source).2 := by
  have hw := GeneralPaperScalarTableCopy.charged S A rationalWordWidth source.weights
  have hl := GeneralPaperScalarTableCopy.matrix_charged S A source.left
  have hr := GeneralPaperScalarTableCopy.matrix_charged S A source.right
  dsimp only [segments,segmentFoot]
  nlinarith

end Blotto.GeneralPaperEqualRationalCopy
