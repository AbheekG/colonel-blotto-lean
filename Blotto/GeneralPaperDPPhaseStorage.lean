import Blotto.GeneralPaperActualTablePrefixStorage

/-! Native leaf/merge phase windows include full reserved initialization,
one shared label list and the streaming table/candidate/control workspace.
Height-dependent exact resources are aggregated over the balanced tree. -/
namespace Blotto.GeneralPaperDPPhaseStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open GeneralPaperOrderedTableHeight GeneralPaperEncodedScatterStorage GeneralPaperEncodedFixedVector
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def applyFixed (W J P : ℕ) : ℕ := 2*(64*W+J*(9*W+P+1))+P+rankWord J+224*W

theorem apply_split (W J P s : ℕ) :
    applyProfile W J P s=applyFixed W J P+(2*J+1)*(1+2*s+2) := by
  unfold applyProfile tableProfile entryProfile applyFixed
  ring

def leafFixed (W K J : ℕ) : ℕ :=
  J*(1+W)+64*W+GeneralPaperDPControlStorage.labelsProfile W K+
    applyFixed W J (rankWord K)+GeneralPaperDPControlStorage.frame W K J+128*W

def mergeFixed (W J : ℕ) : ℕ :=
  J*(1+W)+64*W+GeneralPaperDPControlStorage.labelsProfile W J+
    applyFixed W J (2*rankWord J)+2*GeneralPaperDPControlStorage.frame W J J+128*W

def leafWindow {K q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (field : Field Tag K) : ℕ :=
  let A := if bits then GeneralPaperSummaryArrayExecution.arrayWord W grid.size else W
  let L := if bits then GeneralPaperSummaryArrayExecution.arrayWord W (K+2) else W
  let initial := GeneralPaperDPTableControls.empty (Fin K) index W A grid.size
  let labels := GeneralPaperDPTableControls.labels index W L K
  GeneralPaperEncodedReferenceVector.reservedFootprint W grid.size (GeneralPaperDPControlStorage.slotBits W rankBits)
      (PaperIndexedArrayConstruction.fill index A (fun _ : Fin grid.size => ((none : Option (Selection Tag (Fin K))),64*W))
        grid.size (Nat.le_refl _)).1+
    GeneralPaperEncodedLabelStorage.listFootprint W labels.1+
    GeneralPaperStreamingScatterStorage.foldPeak price W A (GeneralPaperDPControlStorage.frame W K grid.size) rankBits
      (GeneralPaperOrderedLeafEntryPrice.run bits price W grid field) labels.1 initial.1+128*W

theorem leaf_bound {K q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W s : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (field : Field Tag K)
    (hl : ∀ i,RationalHeight (field.read i).2.threshold s) :
    leafWindow bits index price W grid field≤leafFixed W K grid.size+(2*grid.size+1)*(GeneralPaperTagHeight.word s 0+2) := by
  let A := if bits then GeneralPaperSummaryArrayExecution.arrayWord W grid.size else W
  let L := if bits then GeneralPaperSummaryArrayExecution.arrayWord W (K+2) else W
  have he := GeneralPaperDPControlStorage.empty_prefix (Witness:=Fin K) index W A grid.size grid.size (Nat.le_refl _) rankBits
  have hlab := GeneralPaperDPControlStorage.labels index W L K
  have hf := GeneralPaperActualTablePrefixStorage.leaf_peak bits index price W A s grid field hl
  unfold leafWindow
  dsimp only
  simp only [GeneralPaperDPTableControls.labels_data] at hlab hf ⊢
  have total := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add he hlab) hf) (128*W)
  exact total.trans_eq (by rw [apply_split,GeneralPaperTagHeight.word_zero]; unfold leafFixed; ring)

def mergeWindow {Left Right : Type*} {q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (left : Table Tag Left grid.size) (right : Table Tag Right grid.size) : ℕ :=
  let A := if bits then GeneralPaperSummaryArrayExecution.arrayWord W grid.size else W
  let L := if bits then GeneralPaperSummaryArrayExecution.arrayWord W (grid.size+2) else W
  let initial := GeneralPaperDPTableControls.empty (Fin grid.size × Fin grid.size) index W A grid.size
  let labels := GeneralPaperDPTableControls.labels index W L grid.size
  GeneralPaperEncodedReferenceVector.reservedFootprint W grid.size
      (GeneralPaperDPControlStorage.slotBits W GeneralPaperActualTablePrefixStorage.pairBits)
      (PaperIndexedArrayConstruction.fill index A
        (fun _ : Fin grid.size => ((none : Option (Selection Tag (Fin grid.size × Fin grid.size))),64*W)) grid.size (Nat.le_refl _)).1+
    GeneralPaperEncodedLabelStorage.listFootprint W labels.1+
    GeneralPaperStreamingScatterStorage.rowsPeak price W A (GeneralPaperDPControlStorage.frame W grid.size grid.size)
      GeneralPaperActualTablePrefixStorage.pairBits (GeneralPaperOrderedMergeEntryPrice.run bits price W grid left right)
      labels.1 labels.1 initial.1+128*W

theorem merge_bound {Left Right : Type*} {q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W s h : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (left : Table Tag Left grid.size) (right : Table Tag Right grid.size)
    (hl : Safe (expressionHeightBudget s h) left) (hr : Safe (expressionHeightBudget s h) right) :
    mergeWindow bits index price W grid left right≤mergeFixed W grid.size+(2*grid.size+1)*(GeneralPaperTagHeight.word s (h+1)+2) := by
  let A := if bits then GeneralPaperSummaryArrayExecution.arrayWord W grid.size else W
  let L := if bits then GeneralPaperSummaryArrayExecution.arrayWord W (grid.size+2) else W
  have he := GeneralPaperDPControlStorage.empty_prefix (Witness:=Fin grid.size × Fin grid.size)
    index W A grid.size grid.size (Nat.le_refl _) GeneralPaperActualTablePrefixStorage.pairBits
  have hlab := GeneralPaperDPControlStorage.labels index W L grid.size
  have hf := GeneralPaperActualTablePrefixStorage.merge_peak bits index price W A s h grid left right hl hr
  unfold mergeWindow
  dsimp only
  simp only [GeneralPaperDPTableControls.labels_data] at hlab hf ⊢
  have total := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add he hlab) hf) (128*W)
  exact total.trans_eq (by rw [apply_split]; unfold mergeFixed GeneralPaperTagHeight.word; ring)

def phaseProfile (W K J s : ℕ) : ℕ → ℕ
  | 0 => leafFixed W K J+(2*J+1)*(GeneralPaperTagHeight.word s 0+2)
  | h+1 => 2*phaseProfile W K J s h+mergeFixed W J+(2*J+1)*(GeneralPaperTagHeight.word s (h+1)+2)

def phaseBound (W K J s h : ℕ) : ℕ :=
  2^h*(leafFixed W K J+mergeFixed W J)+(2*J+1)*(h+1)*2^h*(2*s+4)

theorem phase_bound (W K J s h : ℕ) : phaseProfile W K J s h≤phaseBound W K J s h := by
  have strong : phaseProfile W K J s h+mergeFixed W J≤
      2^h*(leafFixed W K J+mergeFixed W J)+GeneralPaperRetainedDPStorage.tagProfile (2*J+1) s h := by
    induction h with
    | zero => simp only [phaseProfile,GeneralPaperRetainedDPStorage.tagProfile,pow_zero,one_mul]; omega
    | succ h ih =>
      simp only [phaseProfile,GeneralPaperRetainedDPStorage.tagProfile,pow_succ]
      nlinarith only [ih]
  have htag := GeneralPaperRetainedDPStorage.tag_profile_bound (2*J+1) s h
  unfold phaseBound
  nlinarith only [strong,htag]

end Blotto.GeneralPaperDPPhaseStorage
