import Blotto.RationalLottoBitRouteSampler
import Blotto.RationalTerminalArrayRouteProgram

/-! The whole source sampler uses the streamed array-backed route compiler.
Its common input-derived slot width and exact sample/law equality preserve
budgets and CDF guarantees. Full cost and peak-space composition remain open. -/

namespace Blotto.RationalLottoResourceSystem
open MeasureTheory

def arrayRouteTerminalCompiler {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (value : i.PhaseResult) : RationalAllocationProgram n 80 :=
  (i.terminalData value).programWithArrayRoutes (bitRouteSlotWidth n s)
    (i.terminal_route_frameFit D s hD hB hLength hs hWidth value)
    (ArrayStoreRAM.allocate (n * bitRouteSlotWidth n s) false ()) K outerBits scalarBits

theorem arrayRouteTerminalCompiler_eq {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (value : i.PhaseResult) :
    i.arrayRouteTerminalCompiler D s hD hB hLength hs hWidth K outerBits scalarBits value =
      (i.terminalData value).program K outerBits scalarBits :=
  (i.terminalData value).programWithArrayRoutes_eq _ _ _ K outerBits scalarBits

def arrayRouteFixedSample {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : Fin n → ℚ :=
  (i.runSharedWithTerminalIndexed (i.arrayRouteTerminalCompiler D s hD hB hLength hs hWidth K outerBits scalarBits)
    R choiceBits (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)).1.getD i.fallbackAllocation

theorem arrayRouteFixedSample_eq {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.arrayRouteFixedSample D s hD hB hLength hs hWidth K R outerBits scalarBits choiceBits =
      i.paperFixedSample K R outerBits scalarBits choiceBits := by
  exact congrArg (fun result : Option (Fin n → ℚ) × ℕ => result.1.getD i.fallbackAllocation)
    (i.runSharedWithTerminalIndexed_eq _ K outerBits scalarBits
      (i.arrayRouteTerminalCompiler_eq D s hD hB hLength hs hWidth K outerBits scalarBits)
      R choiceBits (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R))

def arrayRoutePaperSample {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.arrayRouteFixedSample D s hD hB hLength hs hWidth K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits) (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

theorem arrayRoutePaperSample_eq {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.arrayRoutePaperSample D s hD hB hLength hs hWidth K bits = i.paperSample K bits := by
  unfold arrayRoutePaperSample
  rw [i.arrayRouteFixedSample_eq]
  rfl

theorem arrayRoutePaperSample_fullBudget {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.arrayRoutePaperSample D s hD hB hLength hs hWidth K bits j : ℝ)) := by
  rw [i.arrayRoutePaperSample_eq]
  exact i.paperSample_fullBudget K bits

noncomputable def arrayRoutePaperLaw {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s) (K : ℕ) : Mixed n :=
  (fairBitLaw (sampleBitBudget n K)).map (fun bits j => (i.arrayRoutePaperSample D s hD hB hLength hs hWidth K bits j : ℝ))

theorem arrayRoutePaperLaw_eq {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s) (K : ℕ) :
    i.arrayRoutePaperLaw D s hD hB hLength hs hWidth K = i.paperSampleLaw K := by
  unfold arrayRoutePaperLaw paperSampleLaw
  simp only [i.arrayRoutePaperSample_eq]

theorem arrayRoutePaperLaw_CDF_error {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s) (K : ℕ) :
    CDFClose (i.arrayRoutePaperLaw D s hD hB hLength hs hWidth K) i.real.law (5 / (2 * (2 : ℝ) ^ K)) := by
  rw [i.arrayRoutePaperLaw_eq]
  exact i.paperSampleLaw_CDF_error K

end Blotto.RationalLottoResourceSystem
