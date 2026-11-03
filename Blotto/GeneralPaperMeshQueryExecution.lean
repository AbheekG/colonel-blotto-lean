import Blotto.GeneralPaperCompleteQuotientWork
import Blotto.GeneralPaperEpochNumeratorEnvelope

/-! A mesh query borrows its retained denominator scale, casts each stored
integer once, forms one rational product and executes one bounded quotient.
The returned native annotation addition and depth construction are priced.
-/
namespace Blotto.GeneralPaperMeshQueryExecution
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def castCost (price : ℕ → ℕ) (n : ℕ) : ℕ :=
  price (1+binaryWordWidth n)+price (rationalWordWidth (n:ℚ))

def run (price : ℕ → ℕ) (W mesh depth numerator total : ℕ) : GeneralPaperBoundedQuotient.Result × ℕ :=
  let x := (mesh:ℚ)*(numerator:ℚ)
  let divisor : ℚ := total
  let quotient := GeneralPaperCompleteQuotientPrice.run price W x divisor depth
  (⟨quotient.1.quotient,quotient.1.remainder,quotient.1.work+16⟩,
    quotient.2+castCost price mesh+castCost price numerator+castCost price total+
    GeneralPaperRationalPrimitivePrice.binary price (fun a b => a*b) (mesh:ℚ) (numerator:ℚ)+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) quotient.1.work 16+128*W)

theorem data (price : ℕ → ℕ) (W mesh depth numerator total : ℕ) :
    (run price W mesh depth numerator total).1=GeneralPaperCDFMesh.evaluate numerator total mesh depth := by
  unfold run GeneralPaperCDFMesh.evaluate
  dsimp only
  rw [GeneralPaperCompleteQuotientPrice.data]

def selected (price : ℕ → ℕ) (W k mesh numerator total : ℕ) : GeneralPaperBoundedQuotient.Result × ℕ :=
  let depth := 30+k
  let output := run price W mesh depth numerator total
  (output.1,output.2+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) 30 k+32*W)

theorem selected_data (price : ℕ → ℕ) (W k mesh numerator total : ℕ)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (selected price W k mesh numerator total).1=GeneralPaperCDFMesh.selected k numerator total := by
  rw [selected,data,hMesh]
  rfl

theorem cast_work (price : ℕ → ℕ) (hMono : Monotone price) (n B L : ℕ)
    (hn : binaryWordWidth n≤B) (hL : 1+2*B≤L) : castCost price n≤2*price L := by
  have hHeight := (GeneralPaperBasisDivideBits.nat_height n).mono hn
  have hr := hMono ((rationalWordWidth_of_height hHeight).trans hL)
  have hn' := hMono (show 1+binaryWordWidth n≤L by omega)
  unfold castCost
  omega

theorem annotation_work (price : ℕ → ℕ) (hMono : Monotone price) (x a : ℚ) (A t depth : ℕ) :
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b)
      (GeneralPaperBoundedQuotient.run x a depth).work 16≤2*price (GeneralPaperCompleteQuotientPrice.width A t depth) := by
  rw [GeneralPaperBoundedQuotient.run_work]
  have hl := GeneralPaperParameterCounterWords.linear_word depth
  have hm := binaryWordWidth_mono (show 12*depth+2+16≤12*depth+194 by omega)
  have hs := binaryWordWidth_mono (show 12*depth+2≤12*depth+2+16 by omega)
  have hd := GeneralPaperInitializerControlCounters.word_le_self depth
  have hw := GeneralPaperCompleteQuotientPrice.width_lower A t depth
  have h16 : binaryWordWidth 16=5 := by decide
  exact GeneralPaperIntegerWordPrice.natural_binary price hMono (fun a b => a+b) _ 16 _
    (by omega) (by omega) (by omega)

end Blotto.GeneralPaperMeshQueryExecution
