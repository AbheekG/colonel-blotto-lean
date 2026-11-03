import Blotto.PlayerSpecificFactorExecution

/-! One linear-width source envelope covers enumeration, linear-factor
construction, quotient division, all retained rows and enclosing controls. -/
namespace Blotto.PlayerSpecificFactorBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificFactorHeights
set_option autoImplicit false
set_option maxHeartbeats 3000000

def widthCoefficient : ℕ := 8*PlayerSpecificRationalRootContract.widthCoefficient+128*1000000^6+8001024
def workCoefficient : ℕ := 8*PlayerSpecificRationalRootContract.workCoefficient+1000000000
def width (H : ℕ) : ℕ := widthCoefficient*(H+1)

theorem large (H : ℕ) : 1024*(H+1)≤width H := by
  exact Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega)

theorem scalar_width (H U c : ℕ) (hHU : H≤U) (hc : c≤widthCoefficient) : c*(H+1)≤width U :=
  Nat.mul_le_mul hc (by omega)

theorem root_cost (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (H U : ℕ) (hH : HasHeight p H) (hHU : H≤U) :
    (PlayerSpecificRationalRootExecution.run model p).2≤
      8*PlayerSpecificRationalRootContract.workCoefficient*(U+1)*model.rat (width U) := by
  have hi:=input_bound p H hH hlen
  have hsize : PlayerSpecificRationalMagnitude.inputHeight p+1≤8*(U+1) := by omega
  have hw : PlayerSpecificRationalRootContract.widthCoefficient*(PlayerSpecificRationalMagnitude.inputHeight p+1)≤width U := by
    have hm:=Nat.mul_le_mul_left PlayerSpecificRationalRootContract.widthCoefficient hsize
    calc
      _ ≤ PlayerSpecificRationalRootContract.widthCoefficient*(8*(U+1)) := hm
      _ = 8*PlayerSpecificRationalRootContract.widthCoefficient*(U+1) := by ring
      _ ≤ width U := scalar_width U U _ (le_refl _) (by unfold widthCoefficient; omega)
  have hc:=PlayerSpecificRationalRootContract.source_cost model p hp hlen
  have hm:=Nat.mul_le_mul (Nat.mul_le_mul_left PlayerSpecificRationalRootContract.workCoefficient hsize) (model.monotone hw)
  exact hc.trans (hm.trans_eq (by ring))

theorem division_width (H U : ℕ) (hHU : H≤U) : 2*1000000^6*(56*H+37+1)≤width U := by
  have hsmall : 56*H+37+1≤64*(H+1) := by omega
  have hm:=Nat.mul_le_mul_left (2*1000000^6) hsmall
  calc
    _ ≤ 2*1000000^6*(64*(H+1)) := hm
    _ = 128*1000000^6*(H+1) := by ring
    _ ≤ width U := scalar_width H U _ hHU (by unfold widthCoefficient; omega)

theorem frame_cost (model : RationalCostModel) (fuel : ℕ) (p roots : Data) (result : Data×Data)
    (H : ℕ) (hph : HasHeight p H) (hrh : HasHeight roots H)
    (hfh : HasHeight result.1 H) (hsh : HasHeight result.2 H)
    (hpl : p.length≤4) (hrl : roots.length≤3) (hfl : result.1.length≤4)
    (hsl : result.2.length≤4) (hfuel : fuel≤4) :
    price model (PlayerSpecificFactorExecution.frame fuel p roots result)≤400*model.rat (width H) := by
  have hbig:=large H
  have hW : 32≤width H := by omega
  have hHW : 1+2*H≤width H := by omega
  have hp:=PlayerSpecificExtendedCopyCost.row_cost model p H (width H) hph (by omega) hHW hW
  have hr:=PlayerSpecificExtendedCopyCost.row_cost model roots H (width H) hrh (by omega) hHW hW
  have hf:=PlayerSpecificExtendedCopyCost.row_cost model result.1 H (width H) hfh (by omega) hHW hW
  have hs:=PlayerSpecificExtendedCopyCost.row_cost model result.2 H (width H) hsh (by omega) hHW hW
  have hfit:=PlayerSpecificDenseTraceFits.controls_fits (width H) [fuel,roots.length,result.1.length] (by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl <;> omega)
  have hc:=price_bound model (width H) (by omega) _ hfit
  simp only [List.map_cons,List.map_nil,List.length_cons,List.length_nil] at hc
  simp only [PlayerSpecificFactorExecution.frame,price_append]
  nlinarith only [hp,hr,hf,hs,hc]

end Blotto.PlayerSpecificFactorBudget
