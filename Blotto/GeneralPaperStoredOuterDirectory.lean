import Blotto.GeneralPaperStoredReadbackPreservation

/-! The unchanged measured outer fields form a complete unified directory:
control header, one natural address scalar and the final selected record.
All owners fit the existing measured extent. -/
namespace Blotto.GeneralPaperStoredOuterDirectory
open GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots
open GeneralPaperEqualOuterFieldLayout
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

def directory (A : ℕ) (fields : Fields A) (branch tag : FixedBinaryWord A) : Directory A :=
  ⟨fields.record,headers fields branch tag,[⟨fields.value,.natural A⟩]⟩

theorem safe (model : RationalCostModel) (S A start : ℕ) (branch tag : FixedBinaryWord A) :
    Safe (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A)).1
      (directory A (canonical A start) branch tag) := by
  refine ⟨?_,selected_owners model S A start branch tag,?_,valid A start branch tag,?_⟩
  · rw [regions]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · rw [regions]
    change [(canonical A start).value].Sublist [(canonical A start).control,(canonical A start).value,(canonical A start).record]
    exact ((List.nil_sublist [(canonical A start).record]).cons_cons (canonical A start).value).cons (canonical A start).control
  · intro cell hc
    have hEq : cell = (⟨(canonical A start).value,.natural A⟩ : GeneralPaperScalarFieldCursor.Cell A) := List.mem_singleton.mp hc
    subst cell
    rfl

theorem covered (model : RationalCostModel) (S A start : ℕ) (branch tag : FixedBinaryWord A) :
    Covered (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A)).1
      (directory A (canonical A start) branch tag) := by
  rw [regions]
  change [(canonical A start).control,(canonical A start).record,(canonical A start).value].Perm
    [(canonical A start).control,(canonical A start).value,(canonical A start).record]
  exact (List.Perm.swap _ _ []).cons _

theorem positive (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    GeneralPaperMeasuredPlanPositive.Positive (GeneralPaperEqualMeasuredSelectedPlan.header model S A) := by
  intro size hs
  rw [plan_data] at hs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact Nat.mul_pos hA (by decide)
  · exact GeneralPaperRetainedScalarValue.positive (.natural A)
  · exact Nat.mul_pos hA (by decide)

theorem area (model : RationalCostModel) (S A start : ℕ) (branch tag : FixedBinaryWord A) :
    A * GeneralPaperReferenceHeaderSlotArea.slots (directory A (canonical A start) branch tag).headers +
      ((directory A (canonical A start) branch tag).cells.map (fun cell => GeneralPaperRetainedScalarValue.encode cell.value)).sum ≤
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum :=
  GeneralPaperFieldDirectorySeparation.joint_area model S A start _ _ (safe model S A start branch tag) (covered model S A start branch tag)

end Blotto.GeneralPaperStoredOuterDirectory
