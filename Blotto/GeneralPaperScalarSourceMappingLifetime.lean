import Blotto.GeneralPaperScalarCursorTargetLifetime

/-! Actual source-to-typed-scalar traversal: full input/output payload
lists, pending scalar copies and all saved partial prices. Injection keeps
source values unchanged; every scalar uses its own encoded length. -/
namespace Blotto.GeneralPaperScalarSourceMappingLifetime
open GeneralPaperRetainedScalarValue (Scalar encode)
open GeneralPaperMappedScalarArrayCursor (liftValues)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds price_word)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def frames {α : Type*} (S A : ℕ) (lift : α → Scalar) : List α → ℕ
  | [] => fields S [S,A,(liftValues S A lift []).2] + 64 * S
  | value :: values =>
    2 * encode (lift value) + fields S [S,A,(liftValues S A lift values).2,
      (liftValues S A lift values).2 + encode (lift value),(liftValues S A lift (value :: values)).2] + 128 * S + frames S A lift values

theorem frames_bound {α : Type*} (model : RationalCostModel) (S A Q : ℕ) (lift : α → Scalar) (values : List α)
    (hWork : (liftValues S A lift values).2 ≤ Q) :
    frames S A lift values ≤ 2 * (values.map (fun value => encode (lift value))).sum + (values.length + 1) * unit model S A Q := by
  induction values with
  | nil =>
    have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(liftValues S A lift []).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    simp only [frames,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.one_mul]
    omega
  | cons value values ih =>
    have hWhole := hWork
    change (liftValues S A lift values).2 + encode (lift value) + 64 * (S + A + 1) ≤ Q at hWork
    have ht := ih (by omega)
    have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(liftValues S A lift values).2,
      (liftValues S A lift values).2 + encode (lift value),(liftValues S A lift (value :: values)).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 5 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    have hLocal : fields S [S,A,(liftValues S A lift values).2,
        (liftValues S A lift values).2 + encode (lift value),(liftValues S A lift (value :: values)).2] + 128 * S ≤ unit model S A Q := by omega
    simp only [frames,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [ht,hLocal]

def window {α : Type*} (S A : ℕ) (lift : α → Scalar) (values : List α) : ℕ :=
  listFootprint S (fun value => encode (lift value)) values + listFootprint S encode (liftValues S A lift values).1 +
    frames S A lift values + fields S [S,A,(liftValues S A lift values).2] + 64 * S

theorem window_bound {α : Type*} (model : RationalCostModel) (S A Q : ℕ) (lift : α → Scalar) (values : List α)
    (hWork : (liftValues S A lift values).2 ≤ Q) :
    window S A lift values ≤ ((values.map (fun value => encode (lift value))).sum + 1) * 8 * unit model S A Q := by
  have hFrames := frames_bound model S A Q lift values hWork
  have hCount : values.length ≤ (values.map (fun value => encode (lift value))).sum := by
    have h := GeneralPaperScalarCursorWork.count_le_payload (values.map lift)
    simpa only [List.length_map,List.map_map,Function.comp_def] using h
  have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(liftValues S A lift values).2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hLinks := Nat.mul_le_mul_left values.length (show 4 * S ≤ unit model S A Q by omega)
  have hFactor := Nat.mul_le_mul_right (unit model S A Q) hCount
  have hPayload := Nat.mul_le_mul_left (values.map (fun value => encode (lift value))).sum (show 4 ≤ unit model S A Q by omega)
  unfold window
  rw [GeneralPaperMappedScalarArrayCursor.lift_data]
  simp only [listFootprint,List.map_map,List.length_map,Function.comp_def]
  nlinarith only [hFrames,hFields,hUnit,hLinks,hFactor,hPayload]

def profile (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  (B + 1) * 8 * unit model S A ((B + 1) * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A)

theorem actual_bound {α : Type*} (model : RationalCostModel) (S A : ℕ) (lift : α → Scalar) (values : List α) :
    window S A lift values ≤ profile model S A (values.map (fun value => encode (lift value))).sum := by
  have hCount : values.length ≤ (values.map (fun value => encode (lift value))).sum := by
    simpa only [List.length_map,List.map_map,Function.comp_def] using GeneralPaperScalarCursorWork.count_le_payload (values.map lift)
  have hUnit := GeneralPaperMeasuredPlanWorkAlgebra.unit_bounds model S A
  have hMeta := Nat.mul_le_mul_left ((values.map (fun value => encode (lift value))).sum + 1)
    (show 1 + 64 * (S + A + 1) ≤ GeneralPaperMeasuredPlanWorkAlgebra.unit model S A by unfold GeneralPaperMeasuredPlanWorkAlgebra.unit; omega)
  have hMass := Nat.mul_le_mul_right (64 * (S + A + 1)) (Nat.add_le_add_right hCount 1)
  apply window_bound model S A _ lift values
  rw [GeneralPaperMappedScalarArrayCursor.lift_work]
  nlinarith only [hMeta,hMass]

end Blotto.GeneralPaperScalarSourceMappingLifetime
