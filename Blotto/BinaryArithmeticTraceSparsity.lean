import Blotto.BinaryMeasuredTraceSparsity
import Blotto.BinaryQuadraticExpressionMeasured

/-! Actual Stein, normalization and expression traces have structural event
certificates on every input. Data-erasure lemmas are used only where they
preserve the complete trace component. No certificate runs in a producer. -/
namespace Blotto.BinaryArithmeticTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization BinaryRationalEncoding
open BinaryMeasuredTraceSparsity
open BinaryPRGHeapPrimitiveLifetime (cells)
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem difference_sparse (first second : List Bool) :
    BinaryInitialTraceSparsity.Sparse (BinaryBooleanPrimitiveLifetime.differenceWithTrace first second).2 := by
  simp only [BinaryInitialTraceSparsity.Sparse,BinaryBooleanPrimitiveLifetime.differenceWithTrace,cells,listCells,arraySlots,
    List.length_cons,List.length_nil]
  omega

theorem divide_sparse (first second : List Bool) :
    BinaryInitialTraceSparsity.Sparse (BinaryBooleanPrimitiveLifetime.divideWithTrace first second).2 := by
  simp only [BinaryInitialTraceSparsity.Sparse,BinaryBooleanPrimitiveLifetime.divideWithTrace,cells,listCells,arraySlots,
    List.length_cons,List.length_nil]
  omega

theorem trim_sparse (bits : List Bool) :
    BinaryInitialTraceSparsity.Sparse (BinaryBooleanPrimitiveLifetime.trimWithTrace bits).2 := by
  simp only [BinaryInitialTraceSparsity.Sparse,BinaryBooleanPrimitiveLifetime.trimWithTrace,cells,listCells,arraySlots,
    List.length_cons,List.length_nil]
  omega

theorem append_sparse (first second : List Bool) :
    BinaryInitialTraceSparsity.Sparse (BinaryPRGOutputLifetime.appendWithTrace first second).2 := by
  induction first with
  | nil => simp [BinaryInitialTraceSparsity.Sparse,BinaryPRGOutputLifetime.appendWithTrace,cells,listCells,arraySlots]
  | cons bit rest ih =>
      exact BinaryInitialTraceSparsity.prefix_one _ _ 1
        (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega) ih

theorem first_sparse (first : List Bool) : BinaryInitialTraceSparsity.Sparse (BinarySteinGCDLifetime.firstTrace first) :=
  BinaryInitialTraceSparsity.prefix_one _ _ 2
    (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
    (BinaryInitialTraceSparsity.scan_sparse first)

theorem both_sparse (first second : List Bool) :
    BinaryInitialTraceSparsity.Sparse (BinarySteinGCDLifetime.bothTrace first second) :=
  BinaryInitialTraceSparsity.prefix_two _ _ _ 2 2
    (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
    (BinaryInitialTraceSparsity.scan_sparse first) (BinaryInitialTraceSparsity.scan_sparse second)

theorem middle_one (first header second : Trace) (depth : ℕ)
    (hHeader : header.length+1 ≤ 2*cells header)
    (hFirst : BinaryInitialTraceSparsity.Sparse first) (hSecond : BinaryInitialTraceSparsity.Sparse second) :
    BinaryInitialTraceSparsity.Sparse (first++header++under depth second) := by
  unfold BinaryInitialTraceSparsity.Sparse at hFirst hSecond ⊢
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

theorem middle_two (first header second third : Trace) (a b : ℕ)
    (hHeader : header.length+2 ≤ 2*cells header)
    (hFirst : BinaryInitialTraceSparsity.Sparse first) (hSecond : BinaryInitialTraceSparsity.Sparse second)
    (hThird : BinaryInitialTraceSparsity.Sparse third) :
    BinaryInitialTraceSparsity.Sparse (first++header++under a second++under b third) := by
  unfold BinaryInitialTraceSparsity.Sparse at hFirst hSecond hThird ⊢
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

theorem gcd_loop_sparse (ruler first second : List Bool) :
    BinaryInitialTraceSparsity.Sparse (BinarySteinGCDLifetime.loopWithTrace ruler first second).2 := by
  induction ruler generalizing first second with
  | nil => exact first_sparse first
  | cons unused ruler ih =>
      unfold BinarySteinGCDLifetime.loopWithTrace
      dsimp only
      split
      · split
        · cases first with
          | nil => exact both_sparse [] second
          | cons a first => cases second with
            | nil => cases a <;> exact both_sparse _ []
            | cons b second =>
                cases a <;> cases b <;> dsimp only
                · exact middle_one _ [.listAllocation 1] _ 1
                    (by simp [cells,listCells,arraySlots]) (both_sparse _ _) (ih _ _)
                · exact middle_one _ [.listAllocation 1] _ 1
                    (by simp [cells,listCells,arraySlots]) (both_sparse _ _) (ih _ _)
                · exact middle_one _ [.listAllocation 1] _ 1
                    (by simp [cells,listCells,arraySlots]) (both_sparse _ _) (ih _ _)
                · split <;> exact middle_two _ [.listAllocation 2] _ _ 2 1
                    (by simp [cells,listCells,arraySlots]) (both_sparse _ _) (difference_sparse _ _) (ih _ _)
        · exact both_sparse first second
      · exact first_sparse first

theorem gcd_sparse (first second : List Bool) :
    BinaryInitialTraceSparsity.Sparse (BinarySteinGCDLifetime.gcdWithTrace first second).2 :=
  BinaryInitialTraceSparsity.prefix_three _ _ _ _ 2 2 2
    (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
    (append_sparse first second) (gcd_loop_sparse _ first second) (trim_sparse _)

theorem normalize_bound (word : SignedWord) : Bounded (BinaryQuadraticLifetime.normalizeWithTrace word).2 := by
  exact prefix_four _ _ _ _ _ 2 2 2 2
    (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
    (of_sparse _ (gcd_sparse _ _)) (of_sparse _ (divide_sparse _ _))
    (of_sparse _ (divide_sparse _ _)) (of_sparse _ (BinaryInitialTraceSparsity.scan_sparse _))

theorem canonicalize_bound (word : SignedWord) : Bounded (BinaryQuadraticLifetime.canonicalizeWithTrace word).2 := by
  exact prefix_three _ _ _ _ 2 2 2
    (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
    (normalize_bound _) (of_sparse _ (trim_sparse _)) (of_sparse _ (trim_sparse _))

theorem raw_bound (op : RealArithmeticOp) (first second : SignedWord) :
    Bounded (BinaryQuadraticLifetime.rawWithTrace op first second).2 := by
  simp only [Bounded,BinaryQuadraticLifetime.rawWithTrace,cells,listCells,arraySlots,List.length_cons,List.length_nil]
  omega

theorem opcode_bound (op : RealArithmeticOp) (first second : SignedWord) :
    Bounded (BinaryQuadraticLifetime.applyWithTrace op first second).2 := by
  exact prefix_two _ _ _ 2 2
    (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
    (raw_bound _ _ _) (canonicalize_bound _)

theorem measured_opcode_bound (op : RealArithmeticOp) (first second : SignedWord) :
    Bounded (BinaryQuadraticMeasured.apply op first second).1.2 := by
  rw [BinaryQuadraticMeasured.apply_erases]
  exact opcode_bound op first second

theorem comparison_bound (first second : SignedWord) :
    Bounded (BinaryQuadraticExpressionMeasured.compare first second).1.2 := by
  rw [BinaryQuadraticExpressionMeasured.compare_erases]
  simp only [Bounded,BinaryQuadraticExpressionLifetime.compareWithTrace,cells,listCells,arraySlots,
    List.length_cons,List.length_nil]
  omega

theorem expression_combine_bound (op : RealArithmeticOp) (a b : (SignedWord × Trace) × ℕ)
    (ha : Bounded a.1.2) (hb : Bounded b.1.2) :
    Bounded (BinaryQuadraticExpressionMeasured.combine op a b).1.2 := by
  simp only [BinaryQuadraticExpressionMeasured.combine_record,BinaryPlannedQuadratic.apply_previous]
  exact prefix_three _ _ _ _ 1 1 2
    (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
    ha hb (measured_opcode_bound _ _ _)

theorem expression_bound {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) :
    Bounded (BinaryQuadraticExpressionMeasured.evaluate env e).1.2 := by
  induction e with
  | input _ | literal _ => simp [BinaryQuadraticExpressionMeasured.evaluate_record,Bounded,cells,listCells,arraySlots]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      rw [BinaryQuadraticExpressionMeasured.evaluate_record]
      exact expression_combine_bound _ _ _ ha hb
  | ifLe a b yes no ha hb hy hn =>
      rw [BinaryQuadraticExpressionMeasured.evaluate_record]
      dsimp only
      split
      · exact prefix_four _ _ _ _ _ 1 1 2 1
          (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
          ha hb (comparison_bound _ _) hy
      · exact prefix_four _ _ _ _ _ 1 1 2 1
          (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
          ha hb (comparison_bound _ _) hn

end Blotto.BinaryArithmeticTraceSparsity
