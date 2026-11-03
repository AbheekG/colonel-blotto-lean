import Blotto.RationalRouteLengthLatticeFit
import Blotto.RationalSharedTerminalSubstitution
import Blotto.RationalLottoPaperProgram

/-! The primary source loop uses a verified binary-route terminal compiler.
The common length lattice provides its fixed slot width for every terminal
input. Exact sample equality retains budgets, joint laws and CDF guarantees;
complete runtime/address/space composition remains separate. -/

namespace Blotto.RationalLottoResourceSystem
open MeasureTheory

def bitRouteSlotWidth (n s : ℕ) : ℕ := 2 * RationalTerminalPacking.routePayloadWidth n s + 1

def bitRouteTerminalCompiler {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (value : i.PhaseResult) : RationalAllocationProgram n 80 :=
  (i.terminalData value).programWithBitRoutes (bitRouteSlotWidth n s)
    (i.terminal_route_frameFit D s hD hB hLength hs hWidth value)
    (⟨fun _ => false, ()⟩ : TableStoreState (n * bitRouteSlotWidth n s) Bool Unit) K outerBits scalarBits

theorem bitRouteTerminalCompiler_eq {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (value : i.PhaseResult) :
    i.bitRouteTerminalCompiler D s hD hB hLength hs hWidth K outerBits scalarBits value =
      (i.terminalData value).program K outerBits scalarBits :=
  (i.terminalData value).programWithBitRoutes_eq _ _ _ K outerBits scalarBits

def bitRouteFixedSample {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : Fin n → ℚ :=
  (i.runSharedWithTerminalIndexed (i.bitRouteTerminalCompiler D s hD hB hLength hs hWidth K outerBits scalarBits)
    R choiceBits (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)).1.getD i.fallbackAllocation

theorem bitRouteFixedSample_eq {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.bitRouteFixedSample D s hD hB hLength hs hWidth K R outerBits scalarBits choiceBits =
      i.paperFixedSample K R outerBits scalarBits choiceBits := by
  exact congrArg (fun result : Option (Fin n → ℚ) × ℕ => result.1.getD i.fallbackAllocation)
    (i.runSharedWithTerminalIndexed_eq _ K outerBits scalarBits
      (i.bitRouteTerminalCompiler_eq D s hD hB hLength hs hWidth K outerBits scalarBits)
      R choiceBits (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R))

def bitRoutePaperSample {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.bitRouteFixedSample D s hD hB hLength hs hWidth K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits) (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

theorem bitRoutePaperSample_eq {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.bitRoutePaperSample D s hD hB hLength hs hWidth K bits = i.paperSample K bits := by
  unfold bitRoutePaperSample
  rw [i.bitRouteFixedSample_eq]
  rfl

theorem bitRoutePaperSample_fullBudget {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.bitRoutePaperSample D s hD hB hLength hs hWidth K bits j : ℝ)) := by
  rw [i.bitRoutePaperSample_eq]
  exact i.paperSample_fullBudget K bits

noncomputable def bitRoutePaperLaw {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s) (K : ℕ) : Mixed n :=
  (fairBitLaw (sampleBitBudget n K)).map (fun bits j => (i.bitRoutePaperSample D s hD hB hLength hs hWidth K bits j : ℝ))

theorem bitRoutePaperLaw_eq {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s) (K : ℕ) :
    i.bitRoutePaperLaw D s hD hB hLength hs hWidth K = i.paperSampleLaw K := by
  unfold bitRoutePaperLaw paperSampleLaw
  simp only [i.bitRoutePaperSample_eq]

theorem bitRoutePaperLaw_CDF_error {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s) (K : ℕ) :
    CDFClose (i.bitRoutePaperLaw D s hD hB hLength hs hWidth K) i.real.law (5 / (2 * (2 : ℝ) ^ K)) := by
  rw [i.bitRoutePaperLaw_eq]
  exact i.paperSampleLaw_CDF_error K

end Blotto.RationalLottoResourceSystem
