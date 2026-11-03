import Blotto.PlayerSpecificFiniteScaleHeights

/-! Polynomial original-input sizes of every actual accepted root,
isolating interval and reduced scale. This is a size contract; complete
recognition source prices remain a separate obligation. -/
namespace Blotto.PlayerSpecificFiniteParameterSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalCells PlayerSpecificRationalCellHeights PlayerSpecificRecognitionInputHeights
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (n L : ℕ) : ℕ := PlayerSpecificFiniteScaleHeights.coefficient*(cellHeight n L+1)

theorem cell_large (n H : ℕ) : H+1≤cellHeight n H := by
  have hn : 1≤n+1 := by omega
  have hm:=Nat.mul_le_mul_right (H+1) hn
  unfold cellHeight
  nlinarith only [hm]

theorem recognition_return {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n)
    (c : Cell) (candidate : PlayerSpecificAlgebraicCandidates.Candidate)
    (hr : PlayerSpecificFiniteRecognition.run model i=some (c,candidate)) :
    CellHeight c (cellHeight n (inputHeight i)) ∧
      HasHeight candidate.polynomial (PlayerSpecificCellCandidateHeights.height (cellHeight n (inputHeight i))) ∧
      RationalHeight candidate.interval.lo (PlayerSpecificCellCandidateHeights.height (cellHeight n (inputHeight i))) ∧
      RationalHeight candidate.interval.hi (PlayerSpecificCellCandidateHeights.height (cellHeight n (inputHeight i))) := by
  have hs:=PlayerSpecificFiniteRecognition.scan_sound model i.budget (PlayerSpecificRationalIntervals.run i) c candidate hr
  have hc:=cells i c hs.1
  have hlarge:=cell_large n (inputHeight i)
  have hb : RationalHeight i.budget (cellHeight n (inputHeight i)) := (original_fields i).1.mono (by omega)
  have hp:=PlayerSpecificRationalIntervals.cubic_nonzero i c hs.1
  exact ⟨hc,PlayerSpecificCellCandidateHeights.accepted model c i.budget _ hc hb (by omega) hp candidate hs.2⟩

theorem actual_sizes {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n)
    (r : PlayerSpecificFiniteParameterReturn.Result) (hr : PlayerSpecificFiniteParameterReturn.run model i=some r) :
    HasHeight r.root.polynomial (height n (inputHeight i)) ∧
      RationalHeight r.root.interval.lo (height n (inputHeight i)) ∧
      RationalHeight r.root.interval.hi (height n (inputHeight i)) ∧
      HasHeight r.scale (height n (inputHeight i)) ∧ r.root.polynomial.length≤4 ∧ r.scale.length≤3 := by
  cases hs : PlayerSpecificFiniteRecognition.run model i with
  | none => rw [PlayerSpecificFiniteParameterReturn.run,hs] at hr; cases hr
  | some chosen =>
    have hfull:=PlayerSpecificFiniteParameterReturn.sound model i r hr
    rw [PlayerSpecificFiniteParameterReturn.run,hs] at hr
    have he:=Option.some.inj hr
    subst r
    have hbounds:=recognition_return model i chosen.1 chosen.2 hs
    have hlarge:=cell_large n (inputHeight i)
    have hb : RationalHeight i.budget (cellHeight n (inputHeight i)) := (original_fields i).1.mono (by omega)
    have hm0 : chosen.2.polynomial≠[] := by intro hz; exact hfull.2.1.ne_zero (by rw [hz]; rfl)
    have hscale:=PlayerSpecificFiniteScaleHeights.scale_height chosen.1 i.budget chosen.2.polynomial
      (cellHeight n (inputHeight i)) hbounds.1 hb hfull.1 hm0 hfull.2.2.1 hbounds.2.1
    have hcap:=PlayerSpecificFiniteScaleHeights.large (cellHeight n (inputHeight i))
    have hlen:=hfull.2.2.2.1.2
    exact ⟨mono hbounds.2.1 hcap,hbounds.2.2.1.mono hcap,hbounds.2.2.2.mono hcap,hscale,hfull.2.2.1,by omega⟩

theorem polynomial_profile (C n L : ℕ) : C*(10*(n+1)*(L+1)+1)≤11*C*(n+1)*(L+1) := by
  have hprod : 1≤(n+1)*(L+1) := Nat.mul_pos (by omega) (by omega)
  have hm:=Nat.mul_le_mul_left C hprod
  nlinarith only [hm]

theorem polynomial_height (n L : ℕ) : height n L≤11*PlayerSpecificFiniteScaleHeights.coefficient*(n+1)*(L+1) :=
  polynomial_profile PlayerSpecificFiniteScaleHeights.coefficient n L

end Blotto.PlayerSpecificFiniteParameterSizes
