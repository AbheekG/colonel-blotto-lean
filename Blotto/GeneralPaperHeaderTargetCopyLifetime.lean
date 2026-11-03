import Blotto.GeneralPaperSelectedInstallationLifetime

/-! Complete target-copy activations include the actual increment scratch
and returned count/work fields. One returned target list is counted once;
pending suffixes share tails. Bounds retain the actual local list length,
so summing them over headers does not square the total measured extent. -/
namespace Blotto.GeneralPaperHeaderTargetCopyLifetime
open GeneralPaperEncodedScalarStorage
open GeneralPaperHeaderTargetCopy (run)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def cap (S A B Q : ℕ) : ℕ := S + A + B + Q + 1

def controls (model : RationalCostModel) (S A : ℕ) (value : FixedBinaryWord A)
    (values : List (FixedBinaryWord A)) : List ℕ :=
  let later := run model S A values
  let count := GeneralPaperNaturalScalarStep.run model S .add later.count 1
  [S,A,later.count,count.1,count.2,later.work,(run model S A (value :: values)).work]

theorem controls_bounded (model : RationalCostModel) (S A B Q : ℕ) (value : FixedBinaryWord A)
    (values : List (FixedBinaryWord A)) (hLength : (value :: values).length ≤ B)
    (hWork : (run model S A (value :: values)).work ≤ Q) :
    ∀ x ∈ controls model S A value values,x ≤ cap S A B Q := by
  have hWhole := hWork
  change (run model S A values).work +
    (GeneralPaperNaturalScalarStep.run model S .add (run model S A values).count 1).2 + A + 128 * (S + A + 1) ≤ Q at hWork
  intro x hx
  simp only [controls,GeneralPaperHeaderTargetCopy.count,GeneralPaperNaturalScalarStep.data,
    GeneralPaperNaturalScalarStep.Op.apply,List.mem_cons,List.not_mem_nil,or_false] at hx
  have hCounter : (GeneralPaperNaturalScalarStep.run model S .add values.length 1).2 ≤ Q := by
    simpa only [GeneralPaperHeaderTargetCopy.count] using
      (show (GeneralPaperNaturalScalarStep.run model S .add (run model S A values).count 1).2 ≤ Q by omega)
  unfold cap
  simp only [List.length_cons] at hLength
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

def localFoot (model : RationalCostModel) (S A : ℕ) (value : FixedBinaryWord A)
    (values : List (FixedBinaryWord A)) : ℕ :=
  A + fields S (controls model S A value values) + 192 * S +
    GeneralPaperNaturalScalarLifetime.footprint model S .add (run model S A values).count 1

def frameBound (model : RationalCostModel) (S A B Q : ℕ) : ℕ :=
  A + 7 * (natBits (cap S A B Q) + S) + 224 * S +
    32 * GeneralPaperStoredHeaderPreparationWork.scalarBound model S A

theorem local_bound (model : RationalCostModel) (S A B Q : ℕ) (value : FixedBinaryWord A)
    (values : List (FixedBinaryWord A)) (hLength : (value :: values).length ≤ B)
    (hWidth : binaryWordWidth (value :: values).length ≤ A + 8)
    (hWork : (run model S A (value :: values)).work ≤ Q) :
    localFoot model S A value values ≤ frameBound model S A B Q := by
  have hFields := fields_bound S (natBits (cap S A B Q)) (controls model S A value values) (by
    intro x hx
    exact Nat.add_le_add_left (binaryWordWidth_mono (controls_bounded model S A B Q value values hLength hWork x hx)) 1)
  change fields S _ ≤ 7 * (natBits (cap S A B Q) + S) + 32 * S at hFields
  have hIncrement := GeneralPaperStoredHeaderPreparationWork.increment_work model S A (run model S A values).count (by
    rw [GeneralPaperHeaderTargetCopy.count]
    exact (binaryWordWidth_mono (show values.length ≤ (value :: values).length by simp only [List.length_cons]; omega)).trans hWidth)
  have hScratch := (GeneralPaperNaturalScalarLifetime.bounded model S .add (run model S A values).count 1).trans
    (Nat.mul_le_mul_left 32 hIncrement)
  unfold localFoot frameBound
  omega

def frames (model : RationalCostModel) (S A : ℕ) : List (FixedBinaryWord A) → ℕ
  | [] => fields S [S,A,(run model S A []).count,(run model S A []).work] + 64 * S
  | value :: values => localFoot model S A value values + frames model S A values

theorem frames_bound (model : RationalCostModel) (S A B Q : ℕ) (values : List (FixedBinaryWord A))
    (hLength : values.length ≤ B) (hWidth : binaryWordWidth values.length ≤ A + 8)
    (hWork : (run model S A values).work ≤ Q) :
    frames model S A values ≤ (values.length + 1) * frameBound model S A B Q := by
  induction values with
  | nil =>
    have hFields := fields_bound S (natBits (cap S A B Q)) [S,A,(run model S A []).count,(run model S A []).work] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl|rfl <;> dsimp only [run] at * <;> omega)
    change fields S _ ≤ 4 * (natBits (cap S A B Q) + S) + 32 * S at hFields
    simp only [frames,List.length_nil,Nat.zero_add,Nat.one_mul]
    unfold frameBound
    omega
  | cons value values ih =>
    have hTailLength : values.length ≤ B := by simp only [List.length_cons] at hLength; omega
    have hTailWidth := (binaryWordWidth_mono (show values.length ≤ (value :: values).length by simp only [List.length_cons]; omega)).trans hWidth
    have hTailWork : (run model S A values).work ≤ Q := by
      change (run model S A values).work +
        (GeneralPaperNaturalScalarStep.run model S .add (run model S A values).count 1).2 + A + 128 * (S + A + 1) ≤ Q at hWork
      omega
    have hLocal := local_bound model S A B Q value values hLength hWidth hWork
    have hTail := ih hTailLength hTailWidth hTailWork
    simp only [frames,List.length_cons]
    nlinarith only [hLocal,hTail]

def window (model : RationalCostModel) (S A : ℕ) (values : List (FixedBinaryWord A)) : ℕ :=
  frames model S A values + listFootprint S (fun _ : FixedBinaryWord A => A) (run model S A values).values +
    fields S [(run model S A values).count,(run model S A values).work] + 64 * S

def unit (model : RationalCostModel) (S A B Q : ℕ) : ℕ :=
  frameBound model S A B Q + A + 2 * S + 2 * (natBits (cap S A B Q) + S) + 128 * S

theorem window_bound (model : RationalCostModel) (S A B Q : ℕ) (values : List (FixedBinaryWord A))
    (hLength : values.length ≤ B) (hWidth : binaryWordWidth values.length ≤ A + 8)
    (hWork : (run model S A values).work ≤ Q) :
    window model S A values ≤ (values.length + 1) * unit model S A B Q := by
  have hFrames := frames_bound model S A B Q values hLength hWidth hWork
  have hList := list_bound S A (fun _ : FixedBinaryWord A => A) (run model S A values).values (fun _ _ => le_rfl)
  rw [GeneralPaperHeaderTargetCopy.data] at hList
  have hFields := fields_bound S (natBits (cap S A B Q)) [(run model S A values).count,(run model S A values).work] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl
    · rw [GeneralPaperHeaderTargetCopy.count]; omega
    · omega)
  change fields S _ ≤ 2 * (natBits (cap S A B Q) + S) + 32 * S at hFields
  have hReserve := Nat.mul_le_mul_left values.length
    (show 0 ≤ 2 * (natBits (cap S A B Q) + S) + 128 * S by omega)
  unfold window unit
  rw [GeneralPaperHeaderTargetCopy.data]
  nlinarith only [hFrames,hList,hFields,hReserve]

@[fun_prop]
theorem unit_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B Q L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L)
    (hB : Small B L) (hQ : Small Q L) : Polylog (fun x => unit model (S x) (A x) (B x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => cap (S x) (A x) (B x) (Q x)) L := by unfold cap; fun_prop
  have hScalar := GeneralPaperStoredPreparationWorkRates.scalar_rate model hFast S A L hL hS hA
  unfold unit frameBound
  fun_prop

end Blotto.GeneralPaperHeaderTargetCopyLifetime
