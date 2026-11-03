import Blotto.GeneralPaperScalarRecordAssemblyLifetime

/-! Actual front-header and trailing scalar-record lifetimes. Successful
prefixes expose every scalar/target/read price and retain the exact shared
suffix seen by the scalar cursor. -/
namespace Blotto.GeneralPaperScalarRecordCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar encode)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def frontWindow (model : RationalCostModel) (S A start fixed stride : ℕ) (values : List Scalar) (rest : List (Region A)) : ℕ :=
  GeneralPaperScalarRecordAssemblyLifetime.window S A fixed values
    (GeneralPaperScalarRecordComponents.listHeader A start fixed stride values.length)
    (GeneralPaperSequentialLayout.run model S A (start + A * (stride * values.length + fixed)) (values.map encode)).1 rest
    (GeneralPaperScalarRecordComponents.listRun S A fixed values
      ((GeneralPaperSequentialLayout.run model S A start (A * (stride * values.length + fixed) :: values.map encode)).1 ++ rest)).work

theorem front_bound (model : RationalCostModel) (S A start fixed stride Q : ℕ) (values : List Scalar) (rest : List (Region A))
    (hA : 0 < A) (hStride : 1 ≤ stride)
    (hCap : start + (A * (stride * values.length + fixed) + (values.map encode).sum) < 2 ^ A)
    (hWork : (GeneralPaperScalarRecordComponents.listRun S A fixed values
      ((GeneralPaperSequentialLayout.run model S A start (A * (stride * values.length + fixed) :: values.map encode)).1 ++ rest)).work ≤ Q) :
    frontWindow model S A start fixed stride values rest ≤
      (A * (stride * values.length + fixed) + (values.map encode).sum + 1) * 32 * unit model S A Q := by
  let header := GeneralPaperScalarRecordComponents.listHeader A start fixed stride values.length
  let first := (GeneralPaperSequentialLayout.run model S A (start + A * (stride * values.length + fixed)) (values.map encode)).1
  let total := (GeneralPaperScalarRecordComponents.listRun S A fixed values
    ((GeneralPaperSequentialLayout.run model S A start (A * (stride * values.length + fixed) :: values.map encode)).1 ++ rest)).work
  have hLength : first.length = values.length := by dsimp only [first]; rw [GeneralPaperSequentialLayout.count,List.length_map]
  have hSome := (GeneralPaperScalarFieldCursor.on_prefix S A first rest values hLength).1
  have hRegions : (GeneralPaperSequentialLayout.run model S A start (A * (stride * values.length + fixed) :: values.map encode)).1 = header :: first := by
    simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,header,first,GeneralPaperScalarRecordComponents.listHeader]
  have hTotal : total = (GeneralPaperScalarFieldCursor.run S A values (first ++ rest)).work +
      (GeneralPaperScalarArrayFieldCursor.targets S A (GeneralPaperScalarFieldCursor.cells A first values)).2 +
      GeneralPaperLastRegionSelection.price S A header + 128 * (S + A + 1) := by
    dsimp only [total]
    rw [hRegions,List.cons_append]
    simp only [GeneralPaperScalarRecordComponents.listRun,hSome]
  have hRange := GeneralPaperSequentialLayout.range model S A (start + A * (stride * values.length + fixed)) (values.map encode)
  have hHeader : A * (fixed + values.length) ≤ header.length := by
    change A * (fixed + values.length) ≤ A * (stride * values.length + fixed)
    have h := Nat.mul_le_mul_right values.length hStride
    exact Nat.mul_le_mul_left A (by omega)
  have h := GeneralPaperScalarRecordAssemblyLifetime.window_bound model S A fixed Q values header first rest total hA hLength
    (fun region hr => (hRange region hr).2.trans_lt (by omega))
    (by change start + A * (stride * values.length + fixed) < 2 ^ A; omega) hHeader hWork (by omega)
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 32 (by omega)))

def trailingWindow (model : RationalCostModel) (S A start arity : ℕ) (values : List Scalar) (rest : List (Region A)) : ℕ :=
  let header := GeneralPaperTrailingScalarRecord.header A (start + (values.map encode).sum) arity
  GeneralPaperScalarRecordAssemblyLifetime.window S A 0 values header
    (GeneralPaperSequentialLayout.run model S A start (values.map encode)).1 (header :: rest)
    (GeneralPaperTrailingScalarRecord.run S A values
      ((GeneralPaperSequentialLayout.run model S A start (values.map encode ++ [A * arity])).1 ++ rest)).work

theorem trailing_bound (model : RationalCostModel) (S A start arity Q : ℕ) (values : List Scalar) (rest : List (Region A))
    (hA : 0 < A) (hArity : values.length ≤ arity)
    (hCap : start + ((values.map encode).sum + A * arity) < 2 ^ A)
    (hWork : (GeneralPaperTrailingScalarRecord.run S A values
      ((GeneralPaperSequentialLayout.run model S A start (values.map encode ++ [A * arity])).1 ++ rest)).work ≤ Q) :
    trailingWindow model S A start arity values rest ≤
      ((values.map encode).sum + A * arity + 1) * 32 * unit model S A Q := by
  let header := GeneralPaperTrailingScalarRecord.header A (start + (values.map encode).sum) arity
  let first := (GeneralPaperSequentialLayout.run model S A start (values.map encode)).1
  let total := (GeneralPaperTrailingScalarRecord.run S A values
    ((GeneralPaperSequentialLayout.run model S A start (values.map encode ++ [A * arity])).1 ++ rest)).work
  have hLength : first.length = values.length := by dsimp only [first]; rw [GeneralPaperSequentialLayout.count,List.length_map]
  have hSome := GeneralPaperScalarFieldCursor.on_prefix S A first (header :: rest) values hLength
  have hTotal : total = (GeneralPaperScalarFieldCursor.run S A values (first ++ header :: rest)).work +
      (GeneralPaperScalarArrayFieldCursor.targets S A (GeneralPaperScalarFieldCursor.cells A first values)).2 +
      GeneralPaperLastRegionSelection.price S A header + 128 * (S + A + 1) := by
    dsimp only [total]
    rw [GeneralPaperTrailingScalarRecord.layout_regions,List.append_assoc,List.singleton_append]
    simp only [GeneralPaperTrailingScalarRecord.run,hSome.1,hSome.2,first,header]
  have hRange := GeneralPaperSequentialLayout.range model S A start (values.map encode)
  have h := GeneralPaperScalarRecordAssemblyLifetime.window_bound model S A 0 Q values header first (header :: rest) total hA hLength
    (fun region hr => (hRange region hr).2.trans_lt (by omega))
    (by change start + (values.map encode).sum + A * arity < 2 ^ A; omega)
    (by change A * (0 + values.length) ≤ A * arity; simpa only [Nat.zero_add] using Nat.mul_le_mul_left A hArity)
    hWork (by omega)
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 32 (by omega)))

end Blotto.GeneralPaperScalarRecordCursorLifetime
