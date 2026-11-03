import Blotto.GeneralPaperNamedCircleHeight

/-! Construct occurrence-block labels by adaptive arithmetic division.
The actual path uses comparisons, doubling, subtraction and a constructed
fuel cap. Division and encoding widths occur only in erased specifications. -/
namespace Blotto.GeneralPaperNativeBlockLabel
set_option autoImplicit false
set_option maxHeartbeats 2800000

theorem fuel_cap (n B : ℕ) (hB : 0<B) : n<B*2^(n+1) := by
  have hn : n<2^(n+1) := lt_trans (Nat.lt_two_pow_self : n<2^n) (GeneralPaperBoundedQuotient.dyadic_cap n)
  exact hn.trans_le (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^(n+1)) hB)

theorem quotient (price : ℕ → ℕ) (A n B : ℕ) (hB : 0<B) :
    (GeneralPaperGrowingQuotientBits.run price A n B (n+1)).1.quotient=n/B := by
  have he := congrArg GeneralPaperGrowingQuotient.Result.quotient (GeneralPaperNaturalGrowingQuotient.data n B (n+1))
  dsimp only [GeneralPaperNaturalGrowingQuotient.lift] at he
  rw [GeneralPaperGrowingQuotientBits.data,he]
  exact GeneralPaperConstructedNatDivision.quotient_eq n B (n+1) hB (fuel_cap n B hB)

def run {K B : ℕ} (price : ℕ → ℕ) (A : ℕ) (hB : 0<B) (r : Fin (K*B)) : Fin K × ℕ :=
  let divided := GeneralPaperGrowingQuotientBits.run price A r.val B (r.val+1)
  (⟨divided.1.quotient,by rw [quotient price A r.val B hB];exact (Nat.div_lt_iff_lt_mul hB).mpr r.isLt⟩,
    divided.2+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) r.val 1+32*A)

theorem data {K B : ℕ} (price : ℕ → ℕ) (A : ℕ) (hB : 0<B) (r : Fin (K*B)) :
    (run price A hB r).1=GeneralPaperQuantileBlocks.block hB r := by
  apply Fin.ext
  exact quotient price A r.val B hB

theorem depth (price : ℕ → ℕ) (A n B : ℕ) (hB : 0<B) :
    (GeneralPaperGrowingQuotientBits.run price A n B (n+1)).1.depth≤binaryWordWidth n := by
  have h := GeneralPaperGrowingQuotient.depth_word_bound (n:ℚ) (B:ℚ) (by exact_mod_cast hB) (n+1)
    (by positivity) (by exact_mod_cast fuel_cap n B hB)
  have hd := congrArg GeneralPaperGrowingQuotient.Result.depth (GeneralPaperNaturalGrowingQuotient.data n B (n+1))
  have hq := congrArg GeneralPaperGrowingQuotient.Result.quotient (GeneralPaperNaturalGrowingQuotient.data n B (n+1))
  dsimp only [GeneralPaperNaturalGrowingQuotient.lift] at hd hq
  rw [← hd,← hq] at h
  rw [GeneralPaperGrowingQuotientBits.data]
  exact h.trans (binaryWordWidth_mono (GeneralPaperNaturalGrowingQuotient.operand_bounds n B (n+1) hB).1)

def width (T B : ℕ) : ℕ := 64+16*(binaryWordWidth T+binaryWordWidth B)

theorem work {K B : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (A : ℕ) (hB : 0<B) (r : Fin (K*B)) :
    (run price A hB r).2≤512*(binaryWordWidth (K*B)+1)*(A+price (width (K*B) B)) := by
  have hDiv := GeneralPaperGrowingQuotientBits.work price hMono A r.val B (r.val+1) hB
  have hd := depth price A r.val B hB
  have he := congrArg GeneralPaperGrowingQuotient.Result.depth (GeneralPaperNaturalGrowingQuotient.data r.val B (r.val+1))
  dsimp only [GeneralPaperNaturalGrowingQuotient.lift] at he
  rw [← he,← GeneralPaperGrowingQuotientBits.data price A r.val B (r.val+1)] at hDiv
  have hWord := binaryWordWidth_mono r.isLt.le
  have hShort : GeneralPaperGrowingQuotientBits.width r.val B≤width (K*B) B := by
    unfold GeneralPaperGrowingQuotientBits.width width
    omega
  have hDiv' := hDiv.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono hShort) A))
  have hInc := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) r.val 1 (K*B+1)
    (by omega) (by omega) (by omega)
  have hIncWord := GeneralPaperRayOperandWidthEnvelope.word_add (K*B) 1
  have hOne : binaryWordWidth 1=1 := by decide
  have hInc' := hInc.trans (Nat.mul_le_mul_left 2 (hMono (show 1+binaryWordWidth (K*B+1)≤width (K*B) B by unfold width;omega)))
  change (GeneralPaperGrowingQuotientBits.run price A r.val B (r.val+1)).2+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) r.val 1+32*A≤_
  nlinarith only [hDiv',hInc',hd,hWord,Nat.zero_le (A*binaryWordWidth (K*B)),Nat.zero_le (price (width (K*B) B)*binaryWordWidth (K*B))]

end Blotto.GeneralPaperNativeBlockLabel
