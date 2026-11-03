import Blotto.GeneralPaperOriginalPreparationResources

/-! Deterministic bit output from the one-field rows actually retained by
the shared dispatcher. The copy prices rational input/output words and
array writes; no accuracy scan, random primitive or rational re-encoding
pass is assumed. Singleton arrays have a fixed inline layout. -/
namespace Blotto.GeneralPaperOneFieldBitOutput
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def retained (p : Input) (poor : Bool) : RationalResourceArray 1 :=
  let actual := (GeneralPaperOneFieldRealPreparation.run 1 p.budget).1
  if poor then actual.2 else actual.1

def budget (p : Input) (poor : Bool) : ℚ := if poor then p.budget else 1

def run (p : Input) (poor : Bool) : GeneralPaperEqualFullBitDraw.Result 1 :=
  let copied := GeneralPaperEqualBitBranchDraw.copyRow 1 (retained p poor)
  ⟨some copied.1, 0, copied.2 + 16⟩

theorem retained_actual (p : Input) (hN : p.n = 1) :
    (GeneralPaperAllBranchBitDispatch.one p hN).1 =
      .oneField hN (retained p false) (retained p true) := rfl

theorem retained_data (p : Input) (poor : Bool) (j : Fin 1) :
    (retained p poor).allocation j = budget p poor := by
  have h (b : ℚ) : (GeneralPaperEqualRealBoundaryScan.vertex b (0 : Fin 1)).1.allocation j = b :=
    GeneralPaperOneFieldOriginalStorage.row_read b j
  cases poor <;> exact h _

theorem copied_data (p : Input) (poor : Bool) (j : Fin 1) :
    (GeneralPaperEqualBitBranchDraw.copyRow 1 (retained p poor)).1.allocation j = budget p poor := by
  rw [GeneralPaperEqualSelectedDraw.copy_allocation, retained_data]

theorem work (p : Input) (poor : Bool) : (run p poor).work = rationalWordWidth (budget p poor) + 270 := by
  unfold run GeneralPaperEqualBitBranchDraw.copyRow
  dsimp only
  rw [PaperIndexedArrayConstruction.run_work]
  simp only [retained_data, Fin.sum_univ_one]
  have hLog : Nat.log2 1 = 0 := by decide
  norm_num [PaperIndexedArrayConstruction.overhead, PaperIndexedArrayConstruction.initialWork,
    PaperIndexedArrayConstruction.stepWork, id_eq, binaryWordWidth, hLog]

theorem reads (p : Input) (poor : Bool) : (run p poor).reads = 0 := rfl

theorem written (p : Input) (poor : Bool) :
    ∃ output : RationalResourceArray 1, (run p poor).output = some output ∧
      (∀ j, output.allocation j = budget p poor) ∧
      (∑ j : Fin 1, rationalWordWidth (output.allocation j)) = rationalWordWidth (budget p poor) ∧
      FullBudget (budget p poor : ℝ) output.realAllocation := by
  refine ⟨(GeneralPaperEqualBitBranchDraw.copyRow 1 (retained p poor)).1, rfl,
    copied_data p poor, ?_, ?_⟩
  · simp only [copied_data, Fin.sum_univ_one]
  · have h : (GeneralPaperEqualBitBranchDraw.copyRow 1 (retained p poor)).1.realAllocation =
        PureBoundaryEquilibria.oneFieldRow (budget p poor : ℝ) := by
      funext j
      change (((GeneralPaperEqualBitBranchDraw.copyRow 1 (retained p poor)).1.allocation j : ℚ) : ℝ) = _
      rw [copied_data]
      rfl
    rw [h]
    apply PureBoundaryEquilibria.oneFieldRow_fullBudget
    cases poor
    · norm_num [budget]
    · exact_mod_cast p.budget_valid.1.le

def originalSize (p : Input) : ℕ :=
  GeneralPaperValueRoundingInputPrice.inputSize p.values + rationalWordWidth p.budget + 1

theorem input_linear (p : Input) (poor : Bool) : (run p poor).work ≤ 512 * originalSize p := by
  have hi : 1 ≤ originalSize p := by unfold originalSize; omega
  have hb : rationalWordWidth p.budget + 1 ≤ originalSize p := by unfold originalSize; omega
  have hOne : rationalWordWidth (1 : ℚ) = 3 := by decide
  rw [work]
  cases poor <;> simp only [budget, Bool.false_eq_true, ↓reduceIte, hOne] <;> omega

noncomputable def decode (p : Input) (hN : p.n = 1) (poor : Bool) (_ : Unit) : Allocation p.n :=
  GeneralPaperAllBranchBitOutput.oneAllocation hN
    (GeneralPaperEqualBitBranchDraw.copyRow 1 (retained p poor)).1

theorem law_eq (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) (poor : Bool) :
    (GeneralPaperAllBranchBitLaw.law model K p (GeneralPaperAllBranchBitDispatch.one p hN).1 poor :
      MeasureTheory.Measure (Allocation p.n)) = MeasureTheory.Measure.dirac (decode p hN poor ()) := by
  rcases p with ⟨n, values, selector, correct, words, b, hBudget⟩
  change n = 1 at hN
  subst n
  cases poor <;>
    change MeasureTheory.Measure.dirac _ = MeasureTheory.Measure.dirac _ <;>
    congr 1

def Independent (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) : Prop :=
  MeasureTheory.Measure.map (Prod.map (decode p hN false) (decode p hN true))
    ((MeasureTheory.Measure.dirac ()).prod (MeasureTheory.Measure.dirac ())) =
    (GeneralPaperAllBranchBitLaw.law model K p (GeneralPaperAllBranchBitDispatch.one p hN).1 false :
      MeasureTheory.Measure (Allocation p.n)).prod
    (GeneralPaperAllBranchBitLaw.law model K p (GeneralPaperAllBranchBitDispatch.one p hN).1 true :
      MeasureTheory.Measure (Allocation p.n))

theorem independent (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) :
    Independent model K p hN := by
  unfold Independent
  rw [law_eq model K p hN false, law_eq model K p hN true]
  change MeasureTheory.Measure.map (fun _ : Unit × Unit => (decode p hN false (), decode p hN true ()))
    ((MeasureTheory.Measure.dirac ()).prod (MeasureTheory.Measure.dirac ())) = _
  rw [MeasureTheory.Measure.map_const, MeasureTheory.measure_univ, one_smul,
    MeasureTheory.Measure.dirac_prod_dirac]

end Blotto.GeneralPaperOneFieldBitOutput
