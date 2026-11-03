import Blotto.BinarySequentialPayloadDecoder

/-! Source bit prices for the sequential decoder's actual merge operands and
returned child tails. Each recursive call has a conservative four-primitive
length/control price (two tests, split and subtraction), copies and bookkeeping.
The linear primitive interpretation is explicit. No array-copy charge occurs.
Native primitive/reference/packet/stack allocation is not calibrated here. -/
namespace Blotto.BinarySequentialPayloadCost
open BinarySequentialPayloadDecoder BinaryPayload
set_option autoImplicit false

def mergePrice (primitive : ℕ → ℕ) (length : ℕ) (bits : List Bool) : ℕ :=
  let low := length/2
  let first := run low bits
  let second := run (length-low) first.1.2
  let shifted := second.1.1 <<< low
  binaryWordWidth first.1.1+binaryWordWidth second.1.1+binaryWordWidth shifted+
    binaryWordWidth (first.1.1+shifted)+primitive (binaryWordWidth second.1.1+low)+
      primitive (max (binaryWordWidth first.1.1) (binaryWordWidth shifted))

theorem merge_price_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (length : ℕ) (bits : List Bool) (hLength : 1 < length) :
    mergePrice primitive length bits ≤ (4+2*c)*length := by
  let low := length/2
  let high := length-low
  let x := (run low bits).1.1
  let y := (run high (run low bits).1.2).1.1
  let z := y <<< low
  have hLow : 0 < low := by dsimp [low]; omega
  have hHigh : 0 < high := by dsimp [high,low]; omega
  have hSum : high+low = length := by dsimp [high,low]; omega
  have hx := binaryWordWidth_le_of_lt_pow hLow (run_bound low bits)
  have hy := binaryWordWidth_le_of_lt_pow hHigh (run_bound high (run low bits).1.2)
  change binaryWordWidth x ≤ low at hx
  change binaryWordWidth y ≤ high at hy
  have hzVal : z < 2^length := by
    dsimp only [z]
    rw [Nat.shiftLeft_eq]
    calc
      y*2^low < 2^high*2^low := Nat.mul_lt_mul_of_pos_right (run_bound _ _) (Nat.two_pow_pos low)
      _ = 2^length := by rw [← pow_add,hSum]
  have hz := binaryWordWidth_le_of_lt_pow (by omega : 0 < length) hzVal
  have hOutVal : x+z < 2^length := by
    have h := run_bound length bits
    rw [run_merge_value length bits hLength] at h
    exact h
  have hOut := binaryWordWidth_le_of_lt_pow (by omega : 0 < length) hOutVal
  have hShift := (hPrimitive (binaryWordWidth y+low)).trans
    (Nat.mul_le_mul_left c (show binaryWordWidth y+low ≤ length by omega))
  have hAdd := (hPrimitive (max (binaryWordWidth x) (binaryWordWidth z))).trans
    (Nat.mul_le_mul_left c (show max (binaryWordWidth x) (binaryWordWidth z) ≤ length by omega))
  change binaryWordWidth x+binaryWordWidth y+binaryWordWidth z+binaryWordWidth (x+z)+
    primitive (binaryWordWidth y+low)+primitive (max (binaryWordWidth x) (binaryWordWidth z)) ≤ (4+2*c)*length
  nlinarith [show low ≤ length by dsimp [low]; omega,show high ≤ length by dsimp [high,low]; omega]

def scalarPrice (primitive : ℕ → ℕ) (length : ℕ) : ℕ :=
  12*binaryWordWidth (length+2)+4*primitive (binaryWordWidth (length+2))+16

def scalarBound (c length : ℕ) : ℕ := (12+4*c)*binaryWordWidth (length+2)+16

theorem scalar_price_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (length : ℕ) : scalarPrice primitive length ≤ scalarBound c length := by
  have h := hPrimitive (binaryWordWidth (length+2))
  unfold scalarPrice scalarBound
  nlinarith only [h]

theorem scalarBound_mono (c : ℕ) : Monotone (scalarBound c) := by
  intro a b hab
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (binaryWordWidth_mono (by omega : a+2 ≤ b+2))) 16

def nodes (length : ℕ) : ℕ :=
  if length ≤ 1 then 1 else nodes (length/2)+nodes (length-length/2)+1
termination_by length
decreasing_by all_goals omega

theorem nodes_exact (length : ℕ) : nodes length = if length = 0 then 1 else 2*length-1 := by
  unfold nodes
  split
  · rename_i h
    interval_cases length <;> rfl
  · rename_i h
    rw [nodes_exact,nodes_exact,ite_eq_right (by omega : length/2 ≠ 0),
      ite_eq_right (by omega : length-length/2 ≠ 0),ite_eq_right (by omega : length ≠ 0)]
    omega
termination_by length
decreasing_by all_goals omega

theorem nodes_bound (length : ℕ) : nodes length ≤ 2*length+1 := by
  rw [nodes_exact]
  split <;> omega

def work (primitive : ℕ → ℕ) (length : ℕ) (bits : List Bool) : ℕ :=
  if length = 0 then scalarPrice primitive length else if length = 1 then 1+scalarPrice primitive length else
    let low := length/2
    let first := run low bits
    work primitive low bits+work primitive (length-low) first.1.2+
      mergePrice primitive length bits+scalarPrice primitive length
termination_by length
decreasing_by all_goals omega

theorem work_majorant (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (length : ℕ) (bits : List Bool) (capacity : ℕ) (hCapacity : length ≤ capacity) :
    work primitive length bits ≤ length+(4+2*c)*mergeSize length+nodes length*scalarBound c capacity := by
  have hs := (scalar_price_bound primitive c hPrimitive length).trans (scalarBound_mono c hCapacity)
  unfold work
  split
  · rename_i hz
    subst length
    rw [mergeSize,ite_eq_left (show 0 ≤ 1 by decide),nodes,ite_eq_left (show 0 ≤ 1 by decide)]
    simpa only [Nat.mul_zero,Nat.zero_add,Nat.one_mul] using hs
  · split
    · rename_i hOne
      subst length
      rw [mergeSize,ite_eq_left (show 1 ≤ 1 by decide),nodes,ite_eq_left (show 1 ≤ 1 by decide)]
      simpa only [Nat.mul_zero,Nat.add_zero,Nat.one_mul] using Nat.add_le_add_left hs 1
    · rename_i hZero hOne
      have hLength : 1 < length := by omega
      have hl := work_majorant primitive c hPrimitive (length/2) bits capacity (by omega)
      have hh := work_majorant primitive c hPrimitive (length-length/2) (run (length/2) bits).1.2 capacity (by omega)
      have hm := merge_price_bound primitive c hPrimitive length bits hLength
      dsimp only
      rw [mergeSize,ite_eq_right (by omega : ¬length ≤ 1),nodes,ite_eq_right (by omega : ¬length ≤ 1)]
      nlinarith only [hl,hh,hm,hs,show length/2+(length-length/2) = length by omega]
termination_by length
decreasing_by all_goals omega

theorem work_log_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (length : ℕ) (bits : List Bool) :
    work primitive length bits ≤ length+(4+2*c)*length*binaryWordWidth length+
      (2*length+1)*((12+4*c)*binaryWordWidth (length+2)+16) := by
  have hw := work_majorant primitive c hPrimitive length bits length (Nat.le_refl _)
  have hm := Nat.mul_le_mul_left (4+2*c) (mergeSize_word_bound length)
  have hn := Nat.mul_le_mul_right (scalarBound c length) (nodes_bound length)
  unfold scalarBound at *
  nlinarith only [hw,hm,hn]

end Blotto.BinarySequentialPayloadCost
