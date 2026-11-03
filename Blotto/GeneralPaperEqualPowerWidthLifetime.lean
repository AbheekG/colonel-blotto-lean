import Blotto.GeneralPaperEqualCompactionCapacity
import Blotto.GeneralPaperNatPowerBitConstructionStorage
import Blotto.GeneralPaperPowerCeilingStorage

/-! Reuse the literal repeated-squaring and doubling observers, retaining
categorical integer data in the caller. The power return remains live while
width is discovered. Final records include native depth/work and bit prices.
All metadata here is erased observation of already executed constructors. -/
namespace Blotto.GeneralPaperEqualPowerWidthLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def power (model : RationalCostModel) (A K : ℕ) := GeneralPaperNatPowerBits.run model.rat A 2 K

def width (model : RationalCostModel) (A D : ℕ) := GeneralPaperStoredRejectionWidth.run model A D

def cachedPower (model : RationalCostModel) (A K : ℕ) : ℕ :=
  GeneralPaperNatPowerConstructionStorage.record A (power model A K).1 +
    fields A [K, (power model A K).2, (power model A K).2 + 128 * A + 128] + 128 * A

def cachedPowerProfile (model : RationalCostModel) (A K : ℕ) : ℕ :=
  3 * (GeneralPaperNatPowerConstructionStorage.payload 2 K + A) + 32 * A +
    3 * (natBits (K + GeneralPaperNatPowerBitConstructionStorage.price model A 2 K + 128 * A + 129) + A) + 160 * A

theorem cached_power_bound (model : RationalCostModel) (A K : ℕ) :
    cachedPower model A K ≤ cachedPowerProfile model A K := by
  have hRecord := GeneralPaperNatPowerConstructionStorage.record_bound A 2 K K (by decide) le_rfl
  rw [← GeneralPaperNatPowerBits.data model.rat A] at hRecord
  change GeneralPaperNatPowerConstructionStorage.record A (power model A K).1 ≤ _ at hRecord
  have hWork : (power model A K).2 ≤ GeneralPaperNatPowerBitConstructionStorage.price model A 2 K :=
    GeneralPaperNatPowerBitConstructionStorage.work model A 2 K K (by decide) le_rfl
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A
    (K + GeneralPaperNatPowerBitConstructionStorage.price model A 2 K + 128 * A + 129)
    [K, (power model A K).2, (power model A K).2 + 128 * A + 128] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 3 * (natBits (K + GeneralPaperNatPowerBitConstructionStorage.price model A 2 K + 128 * A + 129) + A) + 32 * A at hFields
  unfold cachedPower cachedPowerProfile
  omega

def finalControls (model : RationalCostModel) (A D K : ℕ) : ℕ :=
  fields A [K, (power model A K).2, (power model A K).2 + 128 * A + 128,
    (width model A D).1, (width model A D).2, 128 * A + 128] + 128 * A

def widthTime (model : RationalCostModel) (A L : ℕ) : ℕ := 128 * (L + 1) * (A + model.rat (L + 6) + 1)

def controlCap (model : RationalCostModel) (A L K : ℕ) : ℕ :=
  K + GeneralPaperNatPowerBitConstructionStorage.price model A 2 K + widthTime model A L + 128 * A + 129

def controlProfile (model : RationalCostModel) (A L K : ℕ) : ℕ :=
  6 * (natBits (controlCap model A L K) + A) + 160 * A

theorem controls_bound (model : RationalCostModel) (A D L K : ℕ) (hD : binaryWordWidth D ≤ L) :
    finalControls model A D K ≤ controlProfile model A L K := by
  have hPower : (power model A K).2 ≤ GeneralPaperNatPowerBitConstructionStorage.price model A 2 K :=
    GeneralPaperNatPowerBitConstructionStorage.work model A 2 K K (by decide) le_rfl
  have hWidth : (width model A D).2 ≤ widthTime model A L := GeneralPaperStoredRejectionWidth.word_work model A D L hD
  have hData : (width model A D).1 ≤ L + 6 := by
    change (GeneralPaperPowerCeilingBits.loop model.rat A D 1 (by decide)).1.doublings ≤ _
    have hWord : 1 + binaryWordWidth (2 * (D + 1)) ≤ L + 6 := by
      have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add D 1
      have hMul := binaryWordWidth_mul 2 (D + 1)
      have h1 : binaryWordWidth 1 = 1 := by decide
      have h2 : binaryWordWidth 2 = 2 := by decide
      omega
    exact (GeneralPaperPowerCeilingStorage.result_bounds model A D 1 (D + 1) (L + 6)
      (by decide) (by omega) (by omega) hWord).2.1
  have hTime : L + 6 ≤ widthTime model A L := by
    have hRat := model.word_le (L + 6)
    unfold widthTime
    nlinarith only [hRat, Nat.zero_le (L * model.rat (L + 6)), Nat.zero_le (L * A)]
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (controlCap model A L K)
    [K, (power model A K).2, (power model A K).2 + 128 * A + 128,
      (width model A D).1, (width model A D).2, 128 * A + 128] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        unfold controlCap
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 6 * (natBits (controlCap model A L K) + A) + 32 * A at hFields
  unfold finalControls controlProfile
  omega

inductive Phase (K : ℕ) where
  | power (e : ℕ) (he : e ≤ K)
  | width
  | returned

def window (model : RationalCostModel) (A D K borrowed : ℕ) : Phase K → ℕ
  | .power e _ => borrowed + GeneralPaperNatPowerBitConstructionStorage.window model A 2 e + finalControls model A D K
  | .width => borrowed + cachedPower model A K + GeneralPaperPowerCeilingStorage.window model A D 1 (by decide) + finalControls model A D K
  | .returned => borrowed + cachedPower model A K + finalControls model A D K

def profile (model : RationalCostModel) (A L K borrowed : ℕ) : ℕ :=
  borrowed + GeneralPaperNatPowerBitConstructionStorage.profile model A 2 K + cachedPowerProfile model A K +
    GeneralPaperPowerCeilingStorage.profile model A (L + 6) + controlProfile model A L K

theorem borrowed_mono (model : RationalCostModel) (A L K B C : ℕ) (h : B ≤ C) :
    profile model A L K B ≤ profile model A L K C := by unfold profile; omega

theorem all_phases (model : RationalCostModel) (A D L K borrowed : ℕ) (hD : binaryWordWidth D ≤ L) (phase : Phase K) :
    window model A D K borrowed phase ≤ profile model A L K borrowed := by
  have hCached := cached_power_bound model A K
  have hControls := controls_bound model A D L K hD
  cases phase with
  | power e he =>
    have hPower := GeneralPaperNatPowerBitConstructionStorage.bounded model A 2 K e (by decide) he
    change borrowed + GeneralPaperNatPowerBitConstructionStorage.window model A 2 e + finalControls model A D K ≤ _
    unfold profile
    omega
  | width =>
    have hWord : 1 + binaryWordWidth (2 * (D + 1)) ≤ L + 6 := by
      have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add D 1
      have hMul := binaryWordWidth_mul 2 (D + 1)
      have h1 : binaryWordWidth 1 = 1 := by decide
      have h2 : binaryWordWidth 2 = 2 := by decide
      omega
    have hWidth := GeneralPaperPowerCeilingStorage.bounded model A D (L + 6) hWord
    change borrowed + cachedPower model A K + GeneralPaperPowerCeilingStorage.window model A D 1 (by decide) + finalControls model A D K ≤ _
    unfold profile
    omega
  | returned =>
    change borrowed + cachedPower model A K + finalControls model A D K ≤ _
    unfold profile
    omega

end Blotto.GeneralPaperEqualPowerWidthLifetime
