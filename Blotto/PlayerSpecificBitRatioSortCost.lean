import Blotto.PlayerSpecificBitRatioSortBudget

/-! Complete source price for actual measured ratio-table construction and
stable native sorting, with explicit polynomial original-input widths. -/
namespace Blotto.PlayerSpecificBitRatioSortCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificBitRatioSortExecution PlayerSpecificBitRatioSortBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem native_profile (N A R : ℕ) (hA : A≤64*R) :
    GeneralPaperNativeRepresentativeSort.profile N A R≤1000000*(N+1)^3*R := by
  let L:=binaryWordWidth (N+1)
  have hL : L≤N+2 := PlayerSpecificRationalTrace.control_width (N+1)
  have hbodyCoef : (80+152+24*L)*64+2≤50000*(N+1) := by omega
  have hbodyA:=Nat.mul_le_mul_left (80+152+24*L) hA
  have hbodyC:=Nat.mul_le_mul_right R hbodyCoef
  have hbody : 2*R+80*A+(152+24*L)*A≤50000*(N+1)*R := by nlinarith only [hbodyA,hbodyC]
  have hcount : N*(L+2)≤4*(N+1)^2 := by
    have hm:=Nat.mul_le_mul_left N (show L+2≤N+4 by omega)
    nlinarith only [hm]
  have hfirst:=Nat.mul_le_mul hcount hbody
  have htailCoef : (12*L+8*N+20+80*(N+1))*64≤10000*(N+1) := by omega
  have htailA:=Nat.mul_le_mul_left (12*L+8*N+20+80*(N+1)) hA
  have htailC:=Nat.mul_le_mul_right R htailCoef
  have htail : (12*L+8*N+20)*A+80*(N+1)*A≤10000*(N+1)*R := by nlinarith only [htailA,htailC]
  have hpower : N+1≤(N+1)^3 := by nlinarith only [Nat.zero_le (N^3)]
  have htailp : (12*L+8*N+20)*A+80*(N+1)*A≤10000*(N+1)^3*R := htail.trans (by
    have hm:=Nat.mul_le_mul_right (10000*R) hpower
    nlinarith only [hm])
  unfold GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile
  dsimp only [L] at hfirst htailp
  have hreserve : 0≤(N+1)^3*R := Nat.zero_le _
  nlinarith only [hfirst,htailp,hreserve]

theorem preparation_cost {N : ℕ} (model : RationalCostModel) (H : ℕ) (v w : FixedArrayTable N ℚ)
    (hv : ∀ j,RationalHeight (v.read j) H) (hw : ∀ j,RationalHeight (w.read j) H) :
    (prepare model (address model (PlayerSpecificWidthExecution.run model (N+1)).1) v w).2≤
      4000*(N+1)*model.rat (width N H) := by
  have hm:=measured_bounds model N H
  have hs:=GeneralPaperControlArrayPrice.indexed_work model.rat
    (address model (PlayerSpecificWidthExecution.run model (N+1)).1) (1000*model.rat (width N H))
    (callback model (address model (PlayerSpecificWidthExecution.run model (N+1)).1) v w)
    hm.1 hm.2.2 (callback_cost model _ H v w hv hw hm.2.1)
  have ha:=Nat.mul_le_mul_left (44*(N+1)) hm.2.1
  exact hs.trans (by nlinarith only [ha])

theorem sorting_cost {N : ℕ} (model : RationalCostModel) (H : ℕ) (v w : FixedArrayTable N ℚ)
    (hv : ∀ j,RationalHeight (v.read j) H) (hw : ∀ j,RationalHeight (w.read j) H) :
    let A:=address model (PlayerSpecificWidthExecution.run model (N+1)).1
    (GeneralPaperNativeRepresentativeSort.run model.rat model.rat A (prepare model A v w).1).2≤
      1000000*(N+1)^3*model.rat (width N H) := by
  have hm:=measured_bounds model N H
  have hvalues : ∀ j,rationalWordWidth ((prepare model (address model (PlayerSpecificWidthExecution.run model (N+1)).1) v w).1.read j)≤width N H := by
    intro j
    rw [ratio_read]
    exact (rationalWordWidth_of_height ((hv j).div (hw j))).trans (by unfold width; omega)
  have hs:=GeneralPaperNativeRepresentativeSort.work model.rat model.rat model.monotone
    (address model (PlayerSpecificWidthExecution.run model (N+1)).1) (width N H) hm.1 _ hvalues hm.2.2
  exact hs.trans (native_profile N _ _ hm.2.1)

theorem total_profile (N R measured prepared sorted frame : ℕ)
    (hm : measured≤512*(N+1)*R) (hp : prepared≤4000*(N+1)*R)
    (hs : sorted≤1000000*(N+1)^3*R) (hf : frame≤4096*(N+1)*R) :
    measured+prepared+sorted+frame≤2000000*(N+1)^3*R := by
  have hpower : N+1≤(N+1)^3 := by nlinarith only [Nat.zero_le (N^3)]
  have hextra:=Nat.mul_le_mul_right (8608*R) hpower
  have hreserve : 0≤(N+1)^3*R := Nat.zero_le _
  nlinarith only [hm,hp,hs,hf,hextra,hreserve]

theorem source_cost {N : ℕ} (model : RationalCostModel) (H : ℕ) (v w : FixedArrayTable N ℚ)
    (hv : ∀ j,RationalHeight (v.read j) H) (hw : ∀ j,RationalHeight (w.read j) H) :
    (run model v w).2≤2000000*(N+1)^3*model.rat (width N H) := by
  have hm:=measurement_cost model N H
  have hp:=preparation_cost model H v w hv hw
  have hs:=sorting_cost model H v w hv hw
  have ha:=Nat.mul_le_mul_left (64*(N+1)) (measured_bounds model N H).2.1
  have hf : 64*(N+1)*address model (PlayerSpecificWidthExecution.run model (N+1)).1≤4096*(N+1)*model.rat (width N H) := by
    nlinarith only [ha]
  exact total_profile N _ _ _ _ _ hm hp hs hf

end Blotto.PlayerSpecificBitRatioSortCost
