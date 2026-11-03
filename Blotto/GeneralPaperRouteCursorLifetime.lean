import Blotto.GeneralPaperScalarComponentLifetime

/-! Actual route and route-array lifetime instances. Optional labels and
rational coefficients are copied at their own widths; the scalar trailing
record and enclosing source/price owners are included. -/
namespace Blotto.GeneralPaperRouteCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (encode)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def controls {m : ℕ} (S A : ℕ) (source : GroupRoute m) (regions : List (Region A)) : List ℕ :=
  let copyWork := (GeneralPaperRouteFieldCursor.copy S A source).2
  let parserWork := (GeneralPaperTrailingScalarRecord.run S A (GeneralPaperRouteFieldCursor.values source) regions).work
  [S,A,copyWork,parserWork,copyWork + parserWork,(GeneralPaperRouteFieldCursor.run S A source regions).work]

def window {m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : GroupRoute m) (rest : List (Region A)) : ℕ :=
  GeneralPaperScalarRecordCursorLifetime.trailingWindow model S A start 16 (GeneralPaperRouteFieldCursor.values source) rest +
    3 * listFootprint S encode (GeneralPaperRouteFieldCursor.values source) +
    fields S (controls S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredLeafPlans.route model S A source)).1 ++ rest)) + 256 * S

theorem window_bound {m : ℕ} (model : RationalCostModel) (S A start Q : ℕ) (source : GroupRoute m)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredLeafPlans.route model S A source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperRouteFieldCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredLeafPlans.route model S A source)).1 ++ rest)).work ≤ Q) :
    window model S A start source rest ≤
      ((GeneralPaperEqualMeasuredLeafPlans.route model S A source).sizes.sum + 1) * 64 * unit model S A Q := by
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredLeafPlans.route model S A source)).1 ++ rest
  have hTotal : (GeneralPaperRouteFieldCursor.run S A source regions).work =
      (GeneralPaperRouteFieldCursor.copy S A source).2 +
      (GeneralPaperTrailingScalarRecord.run S A (GeneralPaperRouteFieldCursor.values source) regions).work + 64 * (S + A + 1) := by
    rfl
  change (GeneralPaperRouteFieldCursor.run S A source regions).work ≤ Q at hWork
  have hParsed : (GeneralPaperTrailingScalarRecord.run S A (GeneralPaperRouteFieldCursor.values source) regions).work ≤ Q := by omega
  dsimp only [regions,GeneralPaperMeasuredBlockLayout.run] at hParsed
  rw [GeneralPaperRouteFieldCursor.plan] at hParsed
  rw [GeneralPaperRouteFieldCursor.plan,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
  have hParser := GeneralPaperScalarRecordCursorLifetime.trailing_bound model S A start 16 Q
    (GeneralPaperRouteFieldCursor.values source) rest hA (GeneralPaperRouteFieldCursor.value_count source) hCap hParsed
  have hRawTotal := hTotal
  have hRawWork := hWork
  dsimp only [regions] at hRawTotal hRawWork
  have hFields := fields_bound S (natBits (cap S A Q)) (controls S A source regions) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 6 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hN := GeneralPaperScalarCursorWork.count_le_payload (GeneralPaperRouteFieldCursor.values source)
  have hLinks := Nat.mul_le_mul_left (GeneralPaperRouteFieldCursor.values source).length (show 6 * S ≤ unit model S A Q by omega)
  have hCountPay := Nat.mul_le_mul_right (unit model S A Q) hN
  have hPayload := Nat.mul_le_mul_left ((GeneralPaperRouteFieldCursor.values source).map encode).sum (show 3 ≤ unit model S A Q by omega)
  have hParent : fields S (controls S A source regions) + 352 * S ≤ unit model S A Q := by omega
  have hMass := Nat.mul_le_mul_right (unit model S A Q)
    (show ((GeneralPaperRouteFieldCursor.values source).map encode).sum ≤
      ((GeneralPaperRouteFieldCursor.values source).map encode).sum + A * 16 + 1 by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q)
    (show 1 ≤ ((GeneralPaperRouteFieldCursor.values source).map encode).sum + A * 16 + 1 by omega)
  unfold window listFootprint
  nlinarith only [hParser,hLinks,hCountPay,hPayload,hParent,hMass,hBase]

theorem lifetime {m : ℕ} (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A 64 (GeneralPaperRouteArrayCursor.schema (m := m) model S A)
      (GeneralPaperRouteFieldCursor.run S A) (fun source start rest => window model S A start source rest) := by
  intro source start rest Q hCap hWork
  exact window_bound model S A start Q source rest hA hCap hWork

def arrayWindow {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n (GroupRoute m))
    (rest : List (Region A)) : ℕ :=
  GeneralPaperFrontRecordCursorLifetime.window model S A 64 1 (GeneralPaperRouteFieldCursor.run S A)
    (GeneralPaperRouteArrayCursor.schema model S A) (GeneralPaperRouteFieldCursor.expected model S A)
    (fun route start rest => window model S A start route rest) start source.data.toList rest

theorem array_bound {n m : ℕ} (model : RationalCostModel) (S A start Q : ℕ) (source : FixedArrayTable n (GroupRoute m))
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperRouteArrayCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start
        (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source)).1 ++ rest)).work ≤ Q) :
    arrayWindow model S A start source rest ≤
      ((GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source).sizes.sum + 1) * 128 * unit model S A Q := by
  have hCorrect : GeneralPaperChildCursorWork.Correct model S A (GeneralPaperRouteArrayCursor.schema (m := m) model S A)
      (GeneralPaperRouteFieldCursor.expected model S A) (GeneralPaperRouteFieldCursor.run S A) := by
    intro route start rest
    have h := GeneralPaperRouteFieldCursor.success model S A start route rest
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  rw [GeneralPaperRouteArrayCursor.plan,List.sum_cons] at hCap ⊢
  exact GeneralPaperFrontRecordCursorLifetime.array_bound model S A 64 Q
    (GeneralPaperRouteFieldCursor.run S A) (GeneralPaperRouteArrayCursor.schema model S A)
    (GeneralPaperRouteFieldCursor.expected model S A) (fun route start rest => window model S A start route rest)
    hCorrect (lifetime model S A hA) (fun route => GeneralPaperEqualMeasuredPlanPositive.route model S A route hA)
    hA start source.data.toList rest hCap
    (by simpa only [GeneralPaperRouteArrayCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperRouteArrayCursor.plan] using hWork)

end Blotto.GeneralPaperRouteCursorLifetime
