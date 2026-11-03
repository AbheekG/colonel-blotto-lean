import Blotto.PlayerSpecificRationalCells

/-! Actual rational-input ratio sorting and interval construction. The
complete cell list casts exactly to the preserved real recognition input. -/
namespace Blotto.PlayerSpecificRationalIntervals
open PlayerSpecificRationalCells PlayerSpecificSweep PlayerSpecificSweepBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

def fields {n : ℕ} (i : RationalPlayerSpecificInput n) : List (ℚ×ℚ) :=
  (PlayerSpecificRationalRecognition.ids i).map (fun j => (i.valuesA.weight j,i.valuesB.weight j))
def run {n : ℕ} (i : RationalPlayerSpecificInput n) : List Cell :=
  let row:=fields i
  build (initial row) 0 (suffixes row).2.1

theorem fields_length {n : ℕ} (i : RationalPlayerSpecificInput n) : (fields i).length=n := by
  simp only [fields,List.length_map,PlayerSpecificRationalRecognition.ids_length]

theorem count {n : ℕ} (i : RationalPlayerSpecificInput n) : (run i).length=n+1 := by
  have h:=congrArg List.length (suffixes_fields (fields i))
  simp only [List.length_map,fields_length] at h
  rw [run,PlayerSpecificRationalCells.count,h]

theorem cast_value {n : ℕ} (i : RationalPlayerSpecificInput n) :
    (run i).map castCell=PlayerSpecificRecognition.intervals i.valuesA.values i.valuesB.values
      (PlayerSpecificRationalRecognition.ids i) := by
  rw [run,build_cast]
  rw [(suffixes_cast (fields i)).2,initial_cast]
  simp only [fields,List.map_map,Function.comp_def,castPair,PlayerSpecificRecognition.intervals,RationalFieldSelector.values,Rat.cast_zero]

theorem fits {n : ℕ} (i : RationalPlayerSpecificInput n) (c : Cell) (hc : c∈run i) :
    ∃ low high,(low++high).Perm (List.finRange n) ∧
      PlayerSpecificCells.Fits i.valuesA.values.weight i.valuesB.values.weight low high (castCell c) := by
  have hm : castCell c∈(run i).map castCell := List.mem_map.mpr ⟨c,hc,rfl⟩
  rw [cast_value] at hm
  exact PlayerSpecificRecognition.intervals_fit i.valuesA.values i.valuesB.values (PlayerSpecificRationalRecognition.ids i)
    (PlayerSpecificRationalRecognition.ids_perm i) (PlayerSpecificRationalRecognition.ids_order i) _ hm

theorem cubic_cast (c : Cell) (b : ℚ) :
    PlayerSpecificSquarefreeAlgorithm.realPolynomial (PlayerSpecificDensePolynomial.cubic c.state.coefficients b)=
      PlayerSpecificPolynomial.polynomial (castCell c).state.coefficients (b:ℝ) := by
  rw [PlayerSpecificSquarefreeAlgorithm.realPolynomial,PlayerSpecificDensePolynomial.cubic_semantics]
  simp only [PlayerSpecificPolynomial.polynomial,Polynomial.map_add,Polynomial.map_sub,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,castCell,castState,castCoefficients,map_mul]
  rfl

theorem cubic_nonzero {n : ℕ} (i : RationalPlayerSpecificInput n) (c : Cell) (hc : c∈run i) :
    PlayerSpecificDensePolynomial.semantics (PlayerSpecificDensePolynomial.cubic c.state.coefficients i.budget)≠0 := by
  obtain ⟨low,high,hperm,hfit⟩:=fits i c hc
  have hn:=PlayerSpecificRecognition.cell_nonzero i.valuesA.values i.valuesB.values low high hperm _ hfit (i.budget:ℝ)
  intro hz
  apply hn
  rw [←cubic_cast,PlayerSpecificSquarefreeAlgorithm.realPolynomial,hz,Polynomial.map_zero]

theorem cubic_value (c : Cell) (b : ℚ) (x : ℝ) :
    PlayerSpecificSturmVariations.realEvaluate (PlayerSpecificDensePolynomial.cubic c.state.coefficients b) x=
      PlayerSpecificCubic.cubic (castCell c).state.coefficients (b:ℝ) x := by
  rw [←PlayerSpecificSquarefreeAlgorithm.real_evaluate,cubic_cast,PlayerSpecificPolynomial.eval]

end Blotto.PlayerSpecificRationalIntervals
