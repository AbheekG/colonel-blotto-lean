import Blotto.GeneralPaperMeshQueryExecution

/-! Full mesh-query prices from bounded cached integer inputs. The quotient
is arithmetic-only in both models; its intermediate heights and counters
come from checked recurrences, rather than supplied phase prices.
-/
namespace Blotto.GeneralPaperMeshQueryWork
open GeneralPaperMeshQueryExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem combine (depth W P quotient c1 c2 c3 product annotation : ℕ)
    (hq : quotient≤(depth+1)*(16*P+64*W)) (h1 : c1≤2*P) (h2 : c2≤2*P)
    (h3 : c3≤2*P) (hp : product≤2*P) (ha : annotation≤2*P) :
    quotient+c1+c2+c3+product+annotation+128*W≤256*(depth+1)*(W+P) := by
  nlinarith only [hq,h1,h2,h3,hp,ha,Nat.zero_le (depth*W),Nat.zero_le (depth*P)]

theorem work (price : ℕ → ℕ) (hMono : Monotone price) (W mesh depth numerator total B : ℕ)
    (hTotal : 0<total) (hNumerator : numerator≤total) (hMesh : mesh<2^depth)
    (hMWord : binaryWordWidth mesh≤B) (hTWord : binaryWordWidth total≤B) :
    (run price W mesh depth numerator total).2≤
      256*(depth+1)*(W+price (GeneralPaperCompleteQuotientPrice.width (2*B) B depth)) := by
  let x := (mesh:ℚ)*(numerator:ℚ)
  let a : ℚ := total
  let quotient := GeneralPaperCompleteQuotientPrice.run price W x a depth
  let L := GeneralPaperCompleteQuotientPrice.width (2*B) B depth
  have hNWord := (binaryWordWidth_mono hNumerator).trans hTWord
  have hM := (GeneralPaperBasisDivideBits.nat_height mesh).mono hMWord
  have hN := (GeneralPaperBasisDivideBits.nat_height numerator).mono hNWord
  have hT := (GeneralPaperBasisDivideBits.nat_height total).mono hTWord
  have hX : RationalHeight x (2*B) := (hM.mul hN).mono (by omega)
  have ha : (0:ℚ)<a := by change (0:ℚ)<(total:ℚ); exact_mod_cast hTotal
  have hn : (numerator:ℚ)≤total := by exact_mod_cast hNumerator
  have hm : (mesh:ℚ)<(2:ℚ)^depth := by exact_mod_cast hMesh
  have hx : (0:ℚ)≤x := by dsimp [x]; positivity
  have hCap : x<a*(2:ℚ)^depth := by
    have h1 := mul_le_mul_of_nonneg_left hn (show (0:ℚ)≤mesh by positivity)
    have h2 := mul_lt_mul_of_pos_left hm ha
    dsimp only [x,a] at *
    nlinarith only [h1,h2]
  have hq := GeneralPaperCompleteQuotientWork.work price hMono W x a ha depth (2*B) B hx hCap hX hT
  have hL : 1+2*B≤L := by dsimp [L,GeneralPaperCompleteQuotientPrice.width,GeneralPaperBoundedQuotient.heightBudget]; omega
  have hMX := (rationalWordWidth_of_height hM).trans hL
  have hNX := (rationalWordWidth_of_height hN).trans hL
  have hXX : rationalWordWidth x≤L := (rationalWordWidth_of_height hX).trans
    (by dsimp [L,GeneralPaperCompleteQuotientPrice.width,GeneralPaperBoundedQuotient.heightBudget]; omega)
  have hc1 := cast_work price hMono mesh B L hMWord hL
  have hc2 := cast_work price hMono numerator B L hNWord hL
  have hc3 := cast_work price hMono total B L hTWord hL
  have hp := GeneralPaperRationalPrimitivePrice.binary_le price hMono (fun a b => a*b) (mesh:ℚ) (numerator:ℚ) L hMX hNX hXX
  have hAnnotation := annotation_work price hMono x a (2*B) B depth
  have hd := GeneralPaperCompleteQuotientPrice.data price W x a depth
  rw [←hd] at hAnnotation
  exact combine depth W (price L) _ _ _ _ _ _ hq hc1 hc2 hc3 hp hAnnotation

theorem arithmetic_work (mesh depth numerator total : ℕ) :
    (run (fun _ => 1) 1 mesh depth numerator total).2≤80*(depth+1)+138 := by
  have hq := GeneralPaperCompleteQuotientWork.arithmetic_work ((mesh:ℚ)*numerator) total depth
  change (GeneralPaperCompleteQuotientPrice.run (fun _ => 1) 1 ((mesh:ℚ)*numerator) total depth).2+
    2+2+2+2+2+128≤_
  omega

theorem selected_arithmetic_work (k mesh numerator total : ℕ) :
    (selected (fun _ => 1) 1 k mesh numerator total).2≤80*(k+31)+172 := by
  have h := arithmetic_work mesh (30+k) numerator total
  change (run (fun _ => 1) 1 mesh (30+k) numerator total).2+2+32≤_
  omega

end Blotto.GeneralPaperMeshQueryWork
