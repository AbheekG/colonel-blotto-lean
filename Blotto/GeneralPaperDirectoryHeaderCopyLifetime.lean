import Blotto.GeneralPaperScalarCursorLifetimeRates

/-! Complete actual directory-header copying. The target-word scalar
copy includes operand/output and primitive scratch. Pending target copies,
all saved prices, original/returned headers and target lists coexist.
Bounds keep local target counts so later aggregation remains additive. -/
namespace Blotto.GeneralPaperDirectoryHeaderCopyLifetime
open GeneralPaperReferenceRegionSlots (Header Valid)
open GeneralPaperFieldDirectory (copyHeader)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def copy (S A : ℕ) (value : FixedBinaryWord A) : FixedBinaryWord A × ℕ :=
  GeneralPaperReferenceCopy.scalar S S (fun _ : FixedBinaryWord A => A) value

def targets (S A : ℕ) (values : List (FixedBinaryWord A)) : List (FixedBinaryWord A) × ℕ :=
  GeneralPaperReferenceCopy.list S S (copy S A) values

theorem scalar_bound (model : RationalCostModel) (S A Q : ℕ) (value : FixedBinaryWord A)
    (hWork : (copy S A value).2 ≤ Q) :
    GeneralPaperScalarTableCopyLifetime.scalarWindow S S (fun _ : FixedBinaryWord A => A) value ≤ unit model S A Q := by
  have hFields := fields_bound S (natBits (cap S A Q)) [S,S,(copy S A value).2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  change A + fields S [S,S,(copy S A value).2] + 64 * (S + S + 1) ≤ _
  omega

def frames (S A : ℕ) : List (FixedBinaryWord A) → ℕ
  | [] => fields S [S,A,(targets S A []).2] + 64 * S
  | value :: values =>
    GeneralPaperScalarTableCopyLifetime.scalarWindow S S (fun _ : FixedBinaryWord A => A) value + A +
      fields S [S,A,(copy S A value).2,(targets S A values).2,(copy S A value).2 + (targets S A values).2,
        (targets S A (value :: values)).2] + 128 * S + frames S A values

theorem frames_bound (model : RationalCostModel) (S A Q : ℕ) (values : List (FixedBinaryWord A))
    (hWork : (targets S A values).2 ≤ Q) : frames S A values ≤ (values.length + 1) * 2 * unit model S A Q := by
  induction values with
  | nil =>
    have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(targets S A []).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    simp only [frames,List.length_nil,Nat.zero_add,Nat.one_mul]
    omega
  | cons value values ih =>
    have hWhole := hWork
    change (copy S A value).2 + (targets S A values).2 + 64 * (S + S + 1) ≤ Q at hWork
    have hScalar := scalar_bound model S A Q value (by omega)
    have ht := ih (by omega)
    have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(copy S A value).2,(targets S A values).2,
      (copy S A value).2 + (targets S A values).2,(targets S A (value :: values)).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 6 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    have hParent : A + fields S [S,A,(copy S A value).2,(targets S A values).2,
        (copy S A value).2 + (targets S A values).2,(targets S A (value :: values)).2] + 128 * S ≤ unit model S A Q := by omega
    simp only [frames,List.length_cons]
    nlinarith only [hScalar,ht,hParent]

def window (S A : ℕ) (header : Header A) : ℕ :=
  frames S A header.targets + 2 * listFootprint S (fun _ : FixedBinaryWord A => A) (targets S A header.targets).1 +
    GeneralPaperFieldDirectoryStorage.headerFoot S header + GeneralPaperFieldDirectoryStorage.headerFoot S (copyHeader S A header).1 +
    GeneralPaperLastRegionSelection.price S A header.region +
    fields S [S,A,(targets S A header.targets).2,(copyHeader S A header).2,
      GeneralPaperLastRegionSelection.price S A header.region] + 128 * S

theorem window_bound (model : RationalCostModel) (S A Q : ℕ) (header : Header A) (hA : 0 < A)
    (hValid : Valid header) (hCap : header.region.stop < 2 ^ A) (hWork : (copyHeader S A header).2 ≤ Q) :
    window S A header ≤ (header.targets.length + 1) * 8 * unit model S A Q := by
  have hWhole := hWork
  change (targets S A header.targets).2 + GeneralPaperLastRegionSelection.price S A header.region + natBits header.fixed + 64 * (S + A + 1) ≤ Q at hWork
  have hFrames := frames_bound model S A Q header.targets (by omega)
  have hTargets := list_bound S A (fun _ : FixedBinaryWord A => A) (targets S A header.targets).1 (fun _ _ => le_rfl)
  have hData : (targets S A header.targets).1 = header.targets :=
    GeneralPaperReferenceCopy.list_data S S (copy S A) (fun _ => rfl) header.targets
  rw [hData] at hTargets
  have hHeader := GeneralPaperFieldDirectoryStorage.header_bound S A header hA hValid hCap
  have hRead := GeneralPaperDirectoryCopyWork.region_work model S A header.region hA hCap
  have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(targets S A header.targets).2,(copyHeader S A header).2,
    GeneralPaperLastRegionSelection.price S A header.region] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 5 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hHeaderPay := Nat.mul_le_mul_left (header.targets.length + 1)
    (show 384 * (S + A + 1) ≤ unit model S A Q by omega)
  have hTargetPay := Nat.mul_le_mul_left header.targets.length (show A + 2 * S ≤ unit model S A Q by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ header.targets.length + 1 by omega)
  have hParent : GeneralPaperLastRegionSelection.price S A header.region + fields S [S,A,(targets S A header.targets).2,
      (copyHeader S A header).2,GeneralPaperLastRegionSelection.price S A header.region] + 128 * S ≤ unit model S A Q := by omega
  unfold window
  rw [hData,GeneralPaperFieldDirectory.copy_header_data]
  nlinarith only [hFrames,hTargets,hHeader,hHeaderPay,hTargetPay,hBase,hParent,hUnit]

end Blotto.GeneralPaperDirectoryHeaderCopyLifetime
