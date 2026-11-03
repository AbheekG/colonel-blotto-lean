import Blotto.GeneralPaperPreparedClassifierBits

/-! One explicit operand envelope for the complete cached classifier.
The actual constructed root/grid relation reduces all internal magnitudes
to gridBits and the rational budget precision. No encoding query is run.
-/
namespace Blotto.GeneralPaperClassifierEnvelope
set_option autoImplicit false
set_option maxHeartbeats 6000000

def width (c : GeneralPaperPrecallCachePrice.Cache) (B : ℕ) : ℕ :=
  256+4*B+32*c.proxy.gridBits+16*binaryWordWidth c.proxy.Qg+4*binaryWordWidth c.proxy.H

theorem profile_bound (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (B : ℕ) :
    GeneralPaperClassifierBits.profile model W c B≤4194304*(c.proxy.gridBits+6)*(W+model.rat (width c B)) := by
  let P := model.rat (width c B)
  let F := W+P
  have hL := model.monotone (show GeneralPaperProxyQuotientPrice.envelope c B≤width c B by
    unfold GeneralPaperProxyQuotientPrice.envelope width; omega)
  have hR := model.monotone (show GeneralPaperCFOperandPrice.width (c.proxy.gridBits+3) c.proxy.H≤width c B by
    unfold GeneralPaperCFOperandPrice.width width; omega)
  have hS := model.monotone (show GeneralPaperSelectionPoints.width c.proxy.Qg B≤width c B by
    unfold GeneralPaperSelectionPoints.width width; omega)
  have hLP := Nat.mul_le_mul_left (256*(c.proxy.gridBits+2)) (Nat.add_le_add_left hL W)
  have hRP := Nat.mul_le_mul_left (2097152*(c.proxy.gridBits+6)) (Nat.add_le_add_left hR W)
  have hSP := Nat.mul_le_mul_left 512 (Nat.add_le_add_left hS W)
  change _≤256*(c.proxy.gridBits+2)*F at hLP
  change _≤2097152*(c.proxy.gridBits+6)*F at hRP
  change _≤512*F at hSP
  unfold GeneralPaperClassifierBits.profile GeneralPaperCachedRootQueryBits.profile
  change 256*(c.proxy.gridBits+2)*(W+model.rat (GeneralPaperProxyQuotientPrice.envelope c B))+
    2097152*(c.proxy.gridBits+6)*(W+model.rat (GeneralPaperCFOperandPrice.width (c.proxy.gridBits+3) c.proxy.H))+
    64*W+512*(W+model.rat (GeneralPaperSelectionPoints.width c.proxy.Qg B))+64*W≤4194304*(c.proxy.gridBits+6)*F
  have hWF : W≤F := Nat.le_add_right _ _
  nlinarith only [hLP,hRP,hSP,hWF,Nat.zero_le (c.proxy.gridBits*F)]

theorem actual_width (m k B : ℕ) :
    width (GeneralPaperPrecallCachePrice.specification m k) B≤512+8*B+64*(GeneralPaperProxyParameters.prepare m k).gridBits := by
  let c := GeneralPaperProxyParameters.prepare m k
  have hGrid := GeneralPaperProxyParameters.grid_lower m k
  have hH := GeneralPaperProxyParameters.H_positive m k
  have hSquare : c.H≤c.H*c.H := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left c.H (show 1≤c.H by exact hH)
  have hCap : c.H≤c.Qg := by change 4*c.H*c.H≤c.Qg at hGrid; nlinarith only [hGrid,hSquare]
  have hPower : c.Qg=2^c.gridBits := GeneralPaperProxyParameters.grid_power m k
  have hQWord : binaryWordWidth c.Qg≤c.gridBits+1 := by
    apply binaryWordWidth_le_of_lt_pow (by omega : 0<c.gridBits+1)
    rw [hPower]
    exact GeneralPaperBoundedQuotient.dyadic_cap c.gridBits
  have hHWord := binaryWordWidth_mono hCap
  change 256+4*B+32*c.gridBits+16*binaryWordWidth c.Qg+4*binaryWordWidth c.H≤512+8*B+64*c.gridBits
  omega

theorem actual_work (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (hQ : 0<c.proxy.Qg) (b : ℚ)
    (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    (GeneralPaperClassifierBits.run model W c hQ b).2≤4194304*(c.proxy.gridBits+6)*
      (W+model.rat (512+8*B+64*c.proxy.gridBits)) := by
  have h0 := GeneralPaperClassifierBits.work model W m k c hc hQ b hb B hB
  have h1 := profile_bound model W c B
  have hWidth : width c B≤512+8*B+64*c.proxy.gridBits := by rw [hc]; exact actual_width m k B
  exact h0.trans (h1.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hWidth) W)))

end Blotto.GeneralPaperClassifierEnvelope
