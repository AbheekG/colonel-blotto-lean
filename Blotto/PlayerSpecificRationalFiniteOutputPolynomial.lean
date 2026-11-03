import Blotto.PlayerSpecificRationalOutputSourcePolynomial
import Blotto.PlayerSpecificRationalFiniteMeasuredSourceCost
import Blotto.PlayerSpecificResourceSourcePolynomial

/-! The rational-output portion of every accepted finite packet has an
explicit polynomial envelope in the original rational input size, the
dimension and the two output/scalar precisions. -/
namespace Blotto.PlayerSpecificRationalFiniteOutputPolynomial
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def heightCoefficient : ℕ :=
  PlayerSpecificAlgebraicFiniteDrawHeights.coefficient+
    PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1

def outputHeight {N : ℕ} (i : RationalPlayerSpecificInput N) (K : ℕ) : ℕ :=
  heightCoefficient*(N+1)^3*
    (PlayerSpecificInitialPositivePrecision.inputSize i+K+N+1)

def outputWork {N : ℕ} (i : RationalPlayerSpecificInput N) (K P : ℕ) : ℕ :=
  2*PlayerSpecificRationalOutputSourcePolynomial.polynomial N (outputHeight i K) P

theorem combined_height {N : ℕ} (i : RationalPlayerSpecificInput N) (K : ℕ) :
    PlayerSpecificRationalFiniteMeasuredSourceCost.combinedHeight i K≤
      outputHeight i K := by
  let L:=PlayerSpecificInitialPositivePrecision.inputSize i
  let Q:=(N+1)^3*(L+K+N+1)
  have hA : PlayerSpecificRationalFiniteMeasuredSourceCost.algebraicHeight i K≤
      PlayerSpecificAlgebraicFiniteDrawHeights.coefficient*Q := by
    have hw : L+K+1≤L+K+N+1 := by omega
    have hm:=Nat.mul_le_mul_left
      (PlayerSpecificAlgebraicFiniteDrawHeights.coefficient*(N+1)^3) hw
    simpa only [PlayerSpecificRationalFiniteMeasuredSourceCost.algebraicHeight,
      Q,L,mul_assoc] using hm
  have hbase:=PlayerSpecificResourceSourcePolynomial.size_bound N L 0
  have hresource : PlayerSpecificResourceEntryInput.height N L≤
      (PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)*Q := by
    have hpow : (N+1)^2≤(N+1)^3 := by
      calc
        (N+1)^2 = (N+1)^2*1 := by simp
        _ ≤ (N+1)^2*(N+1) := Nat.mul_le_mul_left _ (by omega)
        _ = (N+1)^3 := by ring
    have hwidth : L+N+1≤L+K+N+1 := by omega
    have hproduct := Nat.mul_le_mul hpow hwidth
    have hscaled:=Nat.mul_le_mul_left
      (PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1) hproduct
    have hsize : PlayerSpecificResourceEntryInput.height N L+1≤
        (PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)*(N+1)^2*(L+1) := by
      simpa only [PlayerSpecificResourceEntryInput.height,add_zero] using hbase
    have hscaled' :
        (PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)*(N+1)^2*(L+N+1)≤
        (PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)*Q := by
      simpa only [Q,mul_assoc] using hscaled
    have hsmall : (PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)*(N+1)^2*(L+1)≤
        (PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)*(N+1)^2*(L+N+1) := by
      gcongr
      omega
    exact (by omega : PlayerSpecificResourceEntryInput.height N L≤
      (PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)*(N+1)^2*(L+1)) |>.trans
        (hsmall.trans hscaled')
  unfold PlayerSpecificRationalFiniteMeasuredSourceCost.combinedHeight
  have heq : heightCoefficient*Q=outputHeight i K := by
    simp only [Q,L,outputHeight,mul_assoc]
  rw [←heq]
  apply max_le
  · have hcoef : PlayerSpecificAlgebraicFiniteDrawHeights.coefficient*Q≤
        heightCoefficient*Q := Nat.mul_le_mul_right Q (by
          dsimp only [heightCoefficient]; omega)
    exact hA.trans hcoef
  · have hcoef : (PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)*Q≤
        heightCoefficient*Q := Nat.mul_le_mul_right Q (by
          dsimp only [heightCoefficient]; omega)
    exact hresource.trans hcoef

theorem finite_output_bound {N : ℕ} (i : RationalPlayerSpecificInput N)
    (H K P : ℕ) :
    PlayerSpecificRationalFiniteMeasuredSourceCost.work i H K P≤
      PlayerSpecificFiniteDrawMeasuredSourceCost.work i H K+outputWork i K P := by
  let T:=PlayerSpecificRationalFiniteMeasuredSourceCost.combinedHeight i K
  have houtput:=PlayerSpecificRationalOutputSourcePolynomial.work_with_control N T P
  have hmono:=PlayerSpecificRationalOutputSourcePolynomial.polynomial_mono_height
    N P (combined_height i K)
  have htwo:=Nat.mul_le_mul_left 2 hmono
  have hbound:=houtput.trans htwo
  have hbound' : PlayerSpecificRationalOutputSourceCost.work N
        (PlayerSpecificRationalFiniteMeasuredSourceCost.combinedHeight i K) P+
      3*RationalCostModel.schoolbook.rat
        (PlayerSpecificRationalOutputSourceCost.width N
          (PlayerSpecificRationalFiniteMeasuredSourceCost.combinedHeight i K) P)≤
      outputWork i K P := by
    simpa only [T,outputWork] using hbound
  calc
    PlayerSpecificRationalFiniteMeasuredSourceCost.work i H K P =
        PlayerSpecificFiniteDrawMeasuredSourceCost.work i H K+
        (PlayerSpecificRationalOutputSourceCost.work N
          (PlayerSpecificRationalFiniteMeasuredSourceCost.combinedHeight i K) P+
        3*RationalCostModel.schoolbook.rat
          (PlayerSpecificRationalOutputSourceCost.width N
            (PlayerSpecificRationalFiniteMeasuredSourceCost.combinedHeight i K) P)) := by
        simp only [PlayerSpecificRationalFiniteMeasuredSourceCost.work,Nat.add_assoc]
    _ ≤ PlayerSpecificFiniteDrawMeasuredSourceCost.work i H K+outputWork i K P :=
      Nat.add_le_add_left hbound' _

theorem original_packet_cost {N : ℕ} (i : RationalPlayerSpecificInput N)
    (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r)
    (player : Bool) (H K P : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicFiniteDraw.bitCount N H K) → Bool) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    (PlayerSpecificRationalFiniteMeasuredExecution.run p i.budget player H K P bits).2≤
      PlayerSpecificFiniteDrawMeasuredSourceCost.work i H K+outputWork i K P := by
  have hc:=(PlayerSpecificRationalFiniteMeasuredSourceCost.original_input i r hr
    player H K P bits).2
  exact hc.trans (finite_output_bound i H K P)

end Blotto.PlayerSpecificRationalFiniteOutputPolynomial
