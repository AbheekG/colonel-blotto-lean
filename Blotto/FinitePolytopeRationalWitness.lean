import Blotto.FinitePolytopeActiveSquare
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Integer active square systems give rational coordinates with ONE common
denominator q times the absolute integer determinant. The determinant is
bounded by the product of row l1 masses, using Leibniz and the product-of-sums
expansion; no factorial or q-to-dimension loss occurs. The final order-cell
witness derives its positive vertex and active square subsystem from the
original real anchors. No rationalization/vertex oracle is supplied. -/

namespace Blotto.FinitePolytopeRationalWitness
open Set RationalOrderCell FinitePolytopeVertex FinitePolytopeActiveKernel FinitePolytopeActiveSquare
open scoped BigOperators Classical

set_option maxHeartbeats 1000000 in
theorem det_natAbs_le_rowMass {d : Type*} [Fintype d] [DecidableEq d] (matrix : Matrix d d ℤ) :
    matrix.det.natAbs ≤ ∏ row, ∑ column, (matrix row column).natAbs := by
  have h : |matrix.det| ≤ ∏ row, ∑ column, |matrix row column| := by
    calc
      |matrix.det| = |matrix.transpose.det| := by rw [Matrix.det_transpose]
      _ ≤ ∑ permutation : Equiv.Perm d,
          |(Equiv.Perm.sign permutation : ℤ) * ∏ row, matrix row (permutation row)| := by
        rw [Matrix.det_apply']
        simpa only [Matrix.transpose_apply,Int.cast_id] using
          Finset.abs_sum_le_sum_abs (s := Finset.univ)
            (f := fun permutation : Equiv.Perm d => (Equiv.Perm.sign permutation : ℤ) *
              ∏ row, matrix row (permutation row))
      _ = ∑ permutation : Equiv.Perm d, ∏ row, |matrix row (permutation row)| := by
        simp only [abs_mul,Equiv.Perm.sign_abs,one_mul,Finset.abs_prod]
      _ = ∑ f ∈ (Finset.univ.image (fun permutation : Equiv.Perm d => (permutation : d → d))),
          ∏ row, |matrix row (f row)| := by
        rw [Finset.sum_image]
        intro first _ second _ hEqual
        exact Equiv.coe_fn_injective hEqual
      _ ≤ ∑ f : d → d, ∏ row, |matrix row (f row)| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro f _ _
        exact Finset.prod_nonneg (fun _ _ => abs_nonneg _)
      _ = ∏ row, ∑ column, |matrix row column| :=
        (Fintype.prod_sum (fun row column => |matrix row column|)).symm
  simp only [Int.abs_eq_natAbs] at h
  exact_mod_cast h

theorem int_cast_mulVec {d : Type*} [Fintype d] [DecidableEq d]
    (matrix : Matrix d d ℤ) (vector : d → ℤ) :
    (fun coordinate => (matrix.mulVec vector coordinate : ℝ)) =
      ((Int.castRingHom ℝ).mapMatrix matrix).mulVec (fun coordinate => (vector coordinate : ℝ)) := by
  funext coordinate
  simp only [Matrix.mulVec,dotProduct,Int.cast_sum,Int.cast_mul]
  rfl

theorem int_cast_adjugate_mulVec {d : Type*} [Fintype d] [DecidableEq d]
    (matrix : Matrix d d ℤ) (vector : d → ℤ) :
    (fun coordinate => (matrix.adjugate.mulVec vector coordinate : ℝ)) =
      ((Int.castRingHom ℝ).mapMatrix matrix).adjugate.mulVec (fun coordinate => (vector coordinate : ℝ)) := by
  rw [int_cast_mulVec,(Int.castRingHom ℝ).map_adjugate]

theorem denominator_divInt {numerator denominator : ℤ} (_hDenominator : denominator ≠ 0) :
    ((numerator : ℚ) / denominator).den ∣ denominator.natAbs := by
  have h := Rat.den_dvd numerator denominator
  rw [Rat.divInt_eq_div] at h
  exact Int.natCast_dvd.mp h

theorem rational_coordinates_of_active_square {r d : Type*} [Fintype r] [Fintype d] [DecidableEq d]
    (rows : r → LinearRow d) (q : ℕ) (hq : 0 < q) (hIntegral : ∀ row, IntegralAfter q (rows row).bound)
    (vertex : d → ℝ) (selected : d → Active rows vertex)
    (hDet : Matrix.det (fun i j => activeVector rows vertex (selected i) j : Matrix d d ℝ) ≠ 0) :
    ∃ rational : d → ℚ, (∀ coordinate, (rational coordinate : ℝ) = vertex coordinate) ∧
      ∃ determinant : ℤ, determinant ≠ 0 ∧
        determinant = Matrix.det (fun i j => (rows (selected i).1).coefficient j : Matrix d d ℤ) ∧
        ∀ coordinate, (rational coordinate).den ∣ q * determinant.natAbs := by
  choose integerBounds hBounds using hIntegral
  let matrix : Matrix d d ℤ := fun i j => (rows (selected i).1).coefficient j
  let right : d → ℤ := fun i => integerBounds (selected i).1
  let realMatrix : Matrix d d ℝ := (Int.castRingHom ℝ).mapMatrix matrix
  let scaled : d → ℝ := fun coordinate => (q : ℝ) * vertex coordinate
  have hMapDet : (matrix.det : ℝ) = realMatrix.det := (Int.castRingHom ℝ).map_det matrix
  have hRealDet : realMatrix.det ≠ 0 := hDet
  have hIntDet : matrix.det ≠ 0 := by
    intro hZero
    apply hRealDet
    rw [← hMapDet,hZero,Int.cast_zero]
  have hSystem : realMatrix.mulVec scaled = fun coordinate => (right coordinate : ℝ) := by
    funext row
    change (∑ coordinate, ((rows (selected row).1).coefficient coordinate : ℝ) *
      ((q : ℝ) * vertex coordinate)) = (integerBounds (selected row).1 : ℝ)
    calc
      _ = (q : ℝ) * (rows (selected row).1).evaluate vertex := by
        rw [LinearRow.evaluate_coefficients,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro coordinate _
        ring
      _ = (q : ℝ) * ((rows (selected row).1).bound : ℝ) := by
        rw [sub_eq_zero.mp (selected row).2]
      _ = (integerBounds (selected row).1 : ℝ) := by exact_mod_cast hBounds (selected row).1
  let numerator : d → ℤ := matrix.adjugate.mulVec right
  have hNumerator : (fun coordinate => (numerator coordinate : ℝ)) = realMatrix.det • scaled := by
    rw [int_cast_adjugate_mulVec]
    rw [← hSystem,Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec]
  let rational : d → ℚ := fun coordinate => (numerator coordinate : ℚ) / (((q : ℤ) * matrix.det : ℤ) : ℚ)
  have hQ : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hD : (matrix.det : ℝ) ≠ 0 := by exact_mod_cast hIntDet
  have hCast (N D : ℤ) : (((N : ℚ) / (D : ℚ) : ℚ) : ℝ) = (N : ℝ) / (D : ℝ) := by
    rw [Rat.cast_div]
    simp only [Rat.cast_intCast]
  have hCoordinates : ∀ coordinate, (rational coordinate : ℝ) = vertex coordinate := by
    intro coordinate
    have hn := congrFun hNumerator coordinate
    change (numerator coordinate : ℝ) = realMatrix.det * ((q : ℝ) * vertex coordinate) at hn
    rw [← hMapDet] at hn
    change (((numerator coordinate : ℚ) / (((q : ℤ) * matrix.det : ℤ) : ℚ) : ℚ) : ℝ) = _
    rw [hCast,Int.cast_mul,Int.cast_natCast]
    apply (div_eq_iff (mul_ne_zero hQ hD)).mpr
    nlinarith
  refine ⟨rational,hCoordinates,matrix.det,hIntDet,rfl,?_⟩
  intro coordinate
  have hDen : (q : ℤ) * matrix.det ≠ 0 := mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hq)) hIntDet
  simpa only [rational,Int.natAbs_mul,Int.natAbs_natCast] using
    (denominator_divInt (numerator := numerator coordinate) hDen)

/-- All rational coordinates share one denominator bounded by the retained
q(m+2)^(m(K-1)+1) envelope. Strict signs and repetitions follow from the
actual positive feasible rational cell point. -/
theorem order_cell_rational_witness {m K : ℕ} (budgets : Fin 2 → ℚ)
    (original : Variable m K → ℝ) (hOriginal : ∀ v, original v ∈ Icc (0 : ℝ) 1) :
    ∃ rational : Coordinate m K → ℚ,
      FeasibleCell budgets original (fun coordinate => (rational coordinate : ℝ)) ∧
      0 < rational none ∧
      ∃ denominator : ℕ, 0 < denominator ∧
        denominator ≤ commonDenominator budgets * (m + 2) ^ (m * (K - 1) + 1) ∧
        ∀ coordinate, (rational coordinate).den ∣ denominator := by
  obtain ⟨vertex,hVertex,hPositive,selected,hSelected⟩ := order_cell_has_active_square budgets original hOriginal
  obtain ⟨rational,hCoordinates,determinant,hDet,hDetEq,hDenominators⟩ :=
    rational_coordinates_of_active_square (constraint budgets original) (commonDenominator budgets)
      (commonDenominator_positive budgets) (constraint_integralAfter budgets original) vertex selected hSelected
  have hEqual : (fun coordinate => (rational coordinate : ℝ)) = vertex := funext hCoordinates
  have hMass : determinant.natAbs ≤ (m + 2) ^ (m * (K - 1) + 1) := by
    rw [hDetEq]
    apply (det_natAbs_le_rowMass _).trans
    have hRows := Finset.prod_le_prod (s := Finset.univ) (fun row _ =>
      constraint_coefficient_mass budgets original (selected row).1)
    simpa only [Finset.prod_const,Finset.card_univ,coordinate_card] using hRows
  have hDenPositive : 0 < commonDenominator budgets * determinant.natAbs :=
    Nat.mul_pos (commonDenominator_positive budgets) (Int.natAbs_pos.mpr hDet)
  refine ⟨rational,?_,?_,commonDenominator budgets * determinant.natAbs,hDenPositive,
    Nat.mul_le_mul_left _ hMass,hDenominators⟩
  · rw [hEqual]
    exact hVertex
  · have h : (0 : ℝ) < (rational none : ℝ) := (hCoordinates none).symm ▸ hPositive
    exact_mod_cast h

end Blotto.FinitePolytopeRationalWitness
