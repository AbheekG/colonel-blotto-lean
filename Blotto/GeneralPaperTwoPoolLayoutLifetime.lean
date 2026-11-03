import Blotto.GeneralPaperSequentialLayoutLifetime

/-! The two actual sequential passes retain their parent layout fields.
Each pass uses one common final extent and complete work envelope. Pending
activations and primitive scratch are bounded linearly in block count;
actual output region lists remain in the separate simultaneous owner window. -/
namespace Blotto.GeneralPaperTwoPoolLayoutLifetime
open GeneralPaperEncodedScalarStorage GeneralPaperMeasuredBlockPlan
open GeneralPaperSequentialLayoutLifetime (frames localBound controlCap)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def controls (model : RationalCostModel) (S I A : ℕ) (inner outer : Plan) : List ℕ :=
  let first := GeneralPaperMeasuredBlockLayout.run model S I 0 inner
  let second := GeneralPaperMeasuredBlockLayout.run model S A first.2.1 outer
  let layout := GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer
  [S,I,A,inner.work,outer.work,first.2.2,second.2.2,layout.work,layout.boundary,layout.finish]

theorem saved_prices (model : RationalCostModel) (S I A Q : ℕ) (inner outer : Plan)
    (hWork : (GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer).work ≤ Q) :
    inner.work ≤ Q ∧ outer.work ≤ Q ∧
      (GeneralPaperMeasuredBlockLayout.run model S I 0 inner).2.2 ≤ Q ∧
      (GeneralPaperMeasuredBlockLayout.run model S A inner.sizes.sum outer).2.2 ≤ Q := by
  dsimp only [GeneralPaperMeasuredTwoPoolLayout.run] at hWork
  rw [GeneralPaperMeasuredBlockLayout.cursor,Nat.zero_add] at hWork
  dsimp only [GeneralPaperMeasuredBlockLayout.run] at hWork ⊢
  omega

theorem controls_bounded (model : RationalCostModel) (S I A Q : ℕ) (inner outer : Plan)
    (hWork : (GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer).work ≤ Q) :
    ∀ x ∈ controls model S I A inner outer,
      x ≤ controlCap S (I + A) (inner.sizes.sum + outer.sizes.sum) Q := by
  have hPrices := saved_prices model S I A Q inner outer hWork
  intro x hx
  simp only [controls,GeneralPaperMeasuredBlockLayout.cursor,Nat.zero_add,
    GeneralPaperMeasuredTwoPoolLayout.boundary,GeneralPaperMeasuredTwoPoolLayout.finish,
    List.mem_cons,List.not_mem_nil,or_false] at hx
  unfold controlCap
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

def parentFoot (model : RationalCostModel) (S I A : ℕ) (inner outer : Plan) : ℕ :=
  fields S (controls model S I A inner outer) + 128 * S

def parentBound (S I A M Q : ℕ) : ℕ :=
  10 * (natBits (controlCap S (I + A) M Q) + S) + 160 * S

theorem parent_bound (model : RationalCostModel) (S I A Q : ℕ) (inner outer : Plan)
    (hWork : (GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer).work ≤ Q) :
    parentFoot model S I A inner outer ≤ parentBound S I A (inner.sizes.sum + outer.sizes.sum) Q := by
  have hFields := fields_bound S (natBits (controlCap S (I + A) (inner.sizes.sum + outer.sizes.sum) Q))
    (controls model S I A inner outer) (by
      intro x hx
      exact Nat.add_le_add_left (binaryWordWidth_mono (controls_bounded model S I A Q inner outer hWork x hx)) 1)
  change fields S _ ≤ 10 * (natBits (controlCap S (I + A) (inner.sizes.sum + outer.sizes.sum) Q) + S) + 32 * S at hFields
  unfold parentFoot parentBound
  omega

def window (model : RationalCostModel) (S I A : ℕ) (inner outer : Plan) : ℕ :=
  let first := GeneralPaperMeasuredBlockLayout.run model S I 0 inner
  frames model S I 0 inner.sizes + frames model S A first.2.1 outer.sizes + parentFoot model S I A inner outer

def bound (model : RationalCostModel) (S I A Bi Bo Q : ℕ) : ℕ :=
  (Bi + 1) * localBound model S I (Bi + Bo) Q +
    (Bo + 1) * localBound model S A (Bi + Bo) Q + parentBound S I A (Bi + Bo) Q

theorem window_bound (model : RationalCostModel) (S I A Q : ℕ) (inner outer : Plan)
    (hInner : GeneralPaperMeasuredPlanPositive.Positive inner)
    (hOuter : GeneralPaperMeasuredPlanPositive.Positive outer) (hI : 0 < I) (hA : 0 < A)
    (hInnerCap : inner.sizes.sum < 2 ^ I) (hTotalCap : inner.sizes.sum + outer.sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer).work ≤ Q) :
    window model S I A inner outer ≤ bound model S I A inner.sizes.sum outer.sizes.sum Q := by
  have hPrices := saved_prices model S I A Q inner outer hWork
  have hInnerWork : (GeneralPaperSequentialLayout.run model S I 0 inner.sizes).2.2 ≤ Q := by
    have h := hPrices.2.2.1
    dsimp only [GeneralPaperMeasuredBlockLayout.run] at h
    omega
  have hOuterWork : (GeneralPaperSequentialLayout.run model S A inner.sizes.sum outer.sizes).2.2 ≤ Q := by
    have h := hPrices.2.2.2
    dsimp only [GeneralPaperMeasuredBlockLayout.run] at h
    omega
  have hi := GeneralPaperSequentialLayoutLifetime.frames_bound model S I 0 (inner.sizes.sum + outer.sizes.sum) Q inner.sizes
    hI (by simpa only [Nat.zero_add] using hInnerCap) (by omega) hInnerWork
  have ho := GeneralPaperSequentialLayoutLifetime.frames_bound model S A inner.sizes.sum
    (inner.sizes.sum + outer.sizes.sum) Q outer.sizes hA hTotalCap le_rfl hOuterWork
  have hiCount := GeneralPaperMeasuredPlanPositive.block_count inner hInner
  have hoCount := GeneralPaperMeasuredPlanPositive.block_count outer hOuter
  have hiMajor := Nat.mul_le_mul_right (localBound model S I (inner.sizes.sum + outer.sizes.sum) Q)
    (Nat.add_le_add_right hiCount 1)
  have hoMajor := Nat.mul_le_mul_right (localBound model S A (inner.sizes.sum + outer.sizes.sum) Q)
    (Nat.add_le_add_right hoCount 1)
  have hParent := parent_bound model S I A Q inner outer hWork
  dsimp only [window,bound]
  rw [GeneralPaperMeasuredBlockLayout.cursor,Nat.zero_add]
  omega

end Blotto.GeneralPaperTwoPoolLayoutLifetime
