import Blotto.GeneralPaperActualCellPartitions

/-! Query-count monotonicity of complete retained-plan prices. These are
scalar inequalities only: the actual program neither rebuilds plans nor
runs counters/encoding passes to calibrate its analytical bounds.
-/
namespace Blotto.GeneralPaperPlanProfileMonotonicity
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem array_word (W m M : ℕ) (h : m≤M) : arrayWord W m≤arrayWord W M := by
  have hb := binaryWordWidth_mono (Nat.add_le_add_right h 1)
  unfold arrayWord
  omega

theorem indexed (W m M a b c P Q : ℕ) (hM : m≤M) (hP : P≤Q) :
    (m+a)*P+44*(m+b)*arrayWord W (m+c)≤(M+a)*Q+44*(M+b)*arrayWord W (M+c) := by
  have hf := Nat.mul_le_mul (Nat.add_le_add_right hM a) hP
  have hs := Nat.mul_le_mul (Nat.mul_le_mul_left 44 (Nat.add_le_add_right hM b))
    (array_word W (m+c) (M+c) (Nat.add_le_add_right hM c))
  exact Nat.add_le_add hf hs

theorem arithmetic_indexed (m M a b P : ℕ) (hM : m≤M) :
    (m+a)*P+44*(m+b)≤(M+a)*P+44*(M+b) :=
  Nat.add_le_add (Nat.mul_le_mul_right P (Nat.add_le_add_right hM a))
    (Nat.mul_le_mul_left 44 (Nat.add_le_add_right hM b))

theorem cut_width (m M U : ℕ) (h : m≤M) :
    GeneralPaperSignedCutOperands.width m U≤GeneralPaperSignedCutOperands.width M U := by
  have hb := binaryWordWidth_mono (Nat.add_le_add_right h 2)
  unfold GeneralPaperSignedCutOperands.width
  omega

theorem rank_width (m M depth V : ℕ) (h : m≤M) :
    GeneralPaperRankArrayOperands.width m depth V≤GeneralPaperRankArrayOperands.width M depth V := by
  have hb := binaryWordWidth_mono (Nat.add_le_add_right h 1)
  unfold GeneralPaperRankArrayOperands.width
  omega

theorem tail_width (m M k U : ℕ) (h : m≤M) :
    GeneralPaperSignedTailOperands.width m k U≤GeneralPaperSignedTailOperands.width M k U := by
  have hr := rank_width (m+1) (M+1) (35+k) (2*U) (Nat.add_le_add_right h 1)
  have hb := binaryWordWidth_mono (Nat.add_le_add_right h 2)
  unfold GeneralPaperSignedTailOperands.width
  omega

theorem rank_query (price : ℕ → ℕ) (hMono : Monotone price) (W m M depth V : ℕ) (h : m≤M) :
    GeneralPaperRankArrayPrice.queryProfile price W m depth V≤GeneralPaperRankArrayPrice.queryProfile price W M depth V := by
  have hp := hMono (rank_width m M depth V h)
  have hf := Nat.mul_le_mul_left (2048*(depth+1)) (Nat.add_le_add_left hp W)
  have hs := Nat.mul_le_mul_left 4 hp
  exact Nat.add_le_add_right (Nat.add_le_add hf hs) _

theorem rank_profile (price : ℕ → ℕ) (hMono : Monotone price) (W m M k V : ℕ) (h : m≤M) :
    GeneralPaperRankArrayPrice.profile price W m k V≤GeneralPaperRankArrayPrice.profile price W M k V := by
  have hf := indexed W m M 0 1 0 _ _ h (rank_query price hMono W m M (35+k) V h)
  have ht := Nat.mul_le_mul_left 2 (hMono (rank_width m M (35+k) V h))
  exact Nat.add_le_add_right (Nat.add_le_add hf ht) _

theorem rank_arithmetic (m M k : ℕ) (h : m≤M) :
    GeneralPaperRankArrayPrice.arithmeticProfile m k≤GeneralPaperRankArrayPrice.arithmeticProfile M k :=
  Nat.add_le_add_right (arithmetic_indexed m M 0 1 (512*((35+k)+1)^2+135) h) _

theorem cut_profile (price : ℕ → ℕ) (hMono : Monotone price) (W m M U : ℕ) (h : m≤M) :
    GeneralPaperSignedCutPrice.profile price W m U≤GeneralPaperSignedCutPrice.profile price W M U := by
  have hp := hMono (cut_width m M U h)
  have hf := indexed W m M 1 2 1 _ _ h (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hp) (64*W))
  exact Nat.add_le_add_right (Nat.add_le_add hf (Nat.mul_le_mul_left 6 hp)) _

theorem cut_arithmetic (m M : ℕ) (h : m≤M) :
    GeneralPaperSignedCutPrice.arithmeticProfile m≤GeneralPaperSignedCutPrice.arithmeticProfile M :=
  Nat.add_le_add_right (arithmetic_indexed m M 1 2 67 h) _

theorem shift_profile (price : ℕ → ℕ) (hMono : Monotone price) (W m M U : ℕ) (h : m≤M) :
    GeneralPaperCDFShiftPrice.profile price W m U≤GeneralPaperCDFShiftPrice.profile price W M U := by
  have hp := hMono (cut_width m M U h)
  have hf := indexed W m M 0 1 0 _ _ h (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) (32*W))
  exact Nat.add_le_add_right (Nat.add_le_add hf (Nat.mul_le_mul_left 4 hp)) _

theorem shift_arithmetic (m M : ℕ) (h : m≤M) :
    GeneralPaperCDFShiftPrice.arithmeticProfile m≤GeneralPaperCDFShiftPrice.arithmeticProfile M :=
  Nat.add_le_add_right (arithmetic_indexed m M 0 1 34 h) _

theorem positions_profile (price : ℕ → ℕ) (hMono : Monotone price) (W m M U : ℕ) (h : m≤M) :
    GeneralPaperSignedPositionsPrice.profile price W m U≤GeneralPaperSignedPositionsPrice.profile price W M U := by
  have hf := indexed W m M 0 1 0 (3*price (GeneralPaperCataloguePointOperands.width U)+64*W) _ h (Nat.le_refl _)
  have ht := Nat.mul_le_mul_left 4 (hMono (cut_width m M U h))
  exact Nat.add_le_add_right (Nat.add_le_add hf ht) _

theorem positions_arithmetic (m M : ℕ) (h : m≤M) :
    GeneralPaperSignedPositionsPrice.arithmeticProfile m≤GeneralPaperSignedPositionsPrice.arithmeticProfile M :=
  Nat.add_le_add_right (arithmetic_indexed m M 0 1 67 h) _

theorem tail_profile (price : ℕ → ℕ) (hMono : Monotone price) (W m M k U : ℕ) (h : m≤M) :
    GeneralPaperSignedTailPrice.profile price W m k U≤GeneralPaperSignedTailPrice.profile price W M k U := by
  have hc := Nat.mul_le_mul_left 2 (cut_profile price hMono W m M U h)
  have hr := Nat.mul_le_mul_left 2 (rank_profile price hMono W (m+1) (M+1) k (2*U) (Nat.add_le_add_right h 1))
  have ht := Nat.mul_le_mul_left 8 (hMono (tail_width m M k U h))
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc hr) ht) _

theorem tail_arithmetic (m M k : ℕ) (h : m≤M) :
    GeneralPaperSignedTailPrice.arithmeticProfile m k≤GeneralPaperSignedTailPrice.arithmeticProfile M k :=
  Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 2 (cut_arithmetic m M h))
    (Nat.mul_le_mul_left 2 (rank_arithmetic (m+1) (M+1) k (Nat.add_le_add_right h 1)))) _

theorem cdf_profile (price : ℕ → ℕ) (hMono : Monotone price) (W m M k U : ℕ) (h : m≤M) :
    GeneralPaperCDFPairPrice.profile price W m k U≤GeneralPaperCDFPairPrice.profile price W M k U := by
  have hs := Nat.mul_le_mul_left 2 (shift_profile price hMono W m M U h)
  have hr := Nat.mul_le_mul_left 2 (rank_profile price hMono W m M k U h)
  have ht := Nat.mul_le_mul_left 8 (hMono (tail_width m M k U h))
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hs hr) ht) _

theorem cdf_arithmetic (m M k : ℕ) (h : m≤M) :
    GeneralPaperCDFPairPrice.arithmeticProfile m k≤GeneralPaperCDFPairPrice.arithmeticProfile M k :=
  Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 2 (shift_arithmetic m M h))
    (Nat.mul_le_mul_left 2 (rank_arithmetic m M k h))) _

theorem signed_profile (price : ℕ → ℕ) (hMono : Monotone price) (W m M k U : ℕ) (h : m≤M) :
    GeneralPaperSignedUpdatePrice.profile price W m k U≤GeneralPaperSignedUpdatePrice.profile price W M k U := by
  have hp := positions_profile price hMono W m M U h
  have hs := shift_profile price hMono W m M U h
  have hr := rank_profile price hMono W m M k U h
  have ht := Nat.mul_le_mul_left 6 (hMono (tail_width m M k U h))
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp hs) hr) ht) _

theorem signed_arithmetic (m M k : ℕ) (h : m≤M) :
    GeneralPaperSignedUpdatePrice.arithmeticProfile m k≤GeneralPaperSignedUpdatePrice.arithmeticProfile M k :=
  Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (positions_arithmetic m M h) (shift_arithmetic m M h))
    (rank_arithmetic m M k h)) _

theorem loss_profile (price : ℕ → ℕ) (hMono : Monotone price) (W m M k U : ℕ) (h : m≤M) :
    GeneralPaperQueryLossPrice.profile price W m k U≤GeneralPaperQueryLossPrice.profile price W M k U := by
  have hc := cdf_profile price hMono W m M k U h
  have ht := tail_profile price hMono W m M k U h
  have hm := Nat.mul_le_mul_left 4 (hMono (tail_width m M k U h))
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc ht) hm) _

theorem loss_arithmetic (m M k : ℕ) (h : m≤M) :
    GeneralPaperQueryLossPrice.arithmeticProfile m k≤GeneralPaperQueryLossPrice.arithmeticProfile M k :=
  Nat.add_le_add_right (Nat.add_le_add (cdf_arithmetic m M k h) (tail_arithmetic m M k h)) _

end Blotto.GeneralPaperPlanProfileMonotonicity
