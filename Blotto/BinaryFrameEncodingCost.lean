import Blotto.BinaryRatListFrame
import Blotto.RationalExpressionWordWidth

/-! Prices the existing frame encoder's width/sign/test-bit primitives and
logical bit-cell construction/copying. A linear natural primitive envelope
is explicit. Concatenation permits copying the complete accumulated buffer
at each row entry; this avoids any ownership/amortization assumption. Row
production, addressing and concrete backend implementation remain separate. -/

namespace Blotto.BinaryPayload
open scoped BigOperators

def encodingBitWork (primitive : ℕ → ℕ) (length n : ℕ) : ℕ :=
  ∑ j : Fin length, (binaryWordWidth n + binaryWordWidth j.val +
    primitive (binaryWordWidth n + binaryWordWidth j.val) + 1)

theorem encodingBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (length n : ℕ) :
    encodingBitWork primitive length n ≤ length * ((1 + c) * (binaryWordWidth n + length) + 1) := by
  have hPoint : ∀ j : Fin length, binaryWordWidth n + binaryWordWidth j.val +
      primitive (binaryWordWidth n + binaryWordWidth j.val) + 1 ≤
        (1 + c) * (binaryWordWidth n + length) + 1 := by
    intro j
    have hj : binaryWordWidth j.val ≤ length := by
      have h := Nat.log2_le_self j.val
      unfold binaryWordWidth
      omega
    have hp := (hPrimitive (binaryWordWidth n + binaryWordWidth j.val)).trans
      (Nat.mul_le_mul_left c (Nat.add_le_add_left hj _))
    nlinarith
  calc
    _ ≤ ∑ _j : Fin length, ((1 + c) * (binaryWordWidth n + length) + 1) :=
      Finset.sum_le_sum (fun j _ => hPoint j)
    _ = _ := by simp

end Blotto.BinaryPayload
namespace Blotto.BinaryNatFrame

def encodingBitWork (primitive : ℕ → ℕ) (n : ℕ) : ℕ :=
  primitive (binaryWordWidth n) + BinaryPayload.encodingBitWork primitive (binaryWordWidth n) n +
    2 * binaryWordWidth n + 1

theorem encodingBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (n : ℕ) :
    encodingBitWork primitive n ≤ 2 * (1 + c) * binaryWordWidth n * binaryWordWidth n +
      (c + 3) * binaryWordWidth n + 1 := by
  have hp := BinaryPayload.encodingBitWork_bound primitive c hPrimitive (binaryWordWidth n) n
  have hw := hPrimitive (binaryWordWidth n)
  unfold encodingBitWork
  nlinarith

theorem encodingBitWork_uniform_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (n W : ℕ) (hWidth : binaryWordWidth n ≤ W) :
    encodingBitWork primitive n ≤ (4 * c + 6) * (W + 1) ^ 2 := by
  have h := encodingBitWork_bound primitive c hPrimitive n
  have hs : binaryWordWidth n * binaryWordWidth n ≤ W * W := Nat.mul_self_le_mul_self hWidth
  have hq := Nat.mul_le_mul_left (2 * (1 + c)) hs
  have hl := Nat.mul_le_mul_left (c + 3) hWidth
  nlinarith

end Blotto.BinaryNatFrame
namespace Blotto.BinaryRatFrame

def encodingBitWork (primitive : ℕ → ℕ) (q : ℚ) : ℕ :=
  3 * rationalWordWidth q + primitive (rationalWordWidth q) +
    BinaryNatFrame.encodingBitWork primitive q.num.natAbs + BinaryNatFrame.encodingBitWork primitive q.den +
      (BinaryNatFrame.encode q.num.natAbs).length + 1

theorem encodingBitWork_uniform_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (q : ℚ) (W : ℕ) (hWidth : rationalWordWidth q ≤ W) :
    encodingBitWork primitive q ≤ (10 * c + 20) * (W + 1) ^ 2 := by
  have hN : binaryWordWidth q.num.natAbs ≤ W := by unfold rationalWordWidth at hWidth; omega
  have hD : binaryWordWidth q.den ≤ W := by unfold rationalWordWidth at hWidth; omega
  have hn := BinaryNatFrame.encodingBitWork_uniform_bound primitive c hPrimitive q.num.natAbs W hN
  have hd := BinaryNatFrame.encodingBitWork_uniform_bound primitive c hPrimitive q.den W hD
  have hp := (hPrimitive (rationalWordWidth q)).trans (Nat.mul_le_mul_left c hWidth)
  unfold encodingBitWork
  rw [BinaryNatFrame.encode_length]
  nlinarith

end Blotto.BinaryRatFrame
namespace Blotto.BinaryRatListFrame
open scoped BigOperators

-- Follows flatMapTR's successive append calls and final buffer-to-list pass.
def concatenationCopyWork : List ℚ → ℕ → ℕ
  | [], accumulated => accumulated
  | q :: rest, accumulated =>
    let next := accumulated + (BinaryRatFrame.encode q).length
    next + concatenationCopyWork rest next

theorem concatenationCopyWork_bound (values : List ℚ) (accumulated : ℕ) :
    concatenationCopyWork values accumulated ≤ (values.length + 1) * (accumulated + (encode values).length) := by
  induction values generalizing accumulated with
  | nil => simp [concatenationCopyWork, encode]
  | cons q rest ih =>
    have ht := ih (accumulated + (BinaryRatFrame.encode q).length)
    simp only [concatenationCopyWork, encode, List.flatMap_cons, List.length_append, List.length_cons] at ht ⊢
    nlinarith

def encodingBitWork (primitive : ℕ → ℕ) (values : List ℚ) : ℕ :=
  (values.map (BinaryRatFrame.encodingBitWork primitive)).sum +
    concatenationCopyWork values 0 + values.length

theorem encodingBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (values : List ℚ) (W : ℕ)
    (hWidth : ∀ q ∈ values, rationalWordWidth q ≤ W) :
    encodingBitWork primitive values ≤ values.length * (10 * c + 20) * (W + 1) ^ 2 +
      (values.length + 1) * values.length * (2 * W + 1) + values.length := by
  have hc : (values.map (BinaryRatFrame.encodingBitWork primitive)).sum ≤
      values.length * ((10 * c + 20) * (W + 1) ^ 2) := by
    induction values with
    | nil => simp
    | cons q values ih =>
      have hq := BinaryRatFrame.encodingBitWork_uniform_bound primitive c hPrimitive q W (hWidth q (by simp))
      have hr := ih (fun x hx => hWidth x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hw : (values.map rationalWordWidth).sum ≤ values.length * W := by
    clear hc
    induction values with
    | nil => simp
    | cons q values ih =>
      have hq := hWidth q (by simp)
      have hr := ih (fun x hx => hWidth x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hLength : (encode values).length ≤ values.length * (2 * W + 1) := by
    rw [encode_length]
    nlinarith
  have hCopy := Nat.mul_le_mul_left (values.length + 1) hLength
  have hConcat := concatenationCopyWork_bound values 0
  simp only [Nat.zero_add] at hConcat
  unfold encodingBitWork
  nlinarith

def rowEncodingBitWork {n : ℕ} (primitive : ℕ → ℕ) (row : Fin n → ℚ) : ℕ :=
  BinaryNatFrame.encodingBitWork primitive n + encodingBitWork primitive (List.ofFn row) +
    (BinaryNatFrame.encode n).length + n

theorem rowEncodingBitWork_bound {n : ℕ} (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (row : Fin n → ℚ) (W : ℕ)
    (hWidth : ∀ j, rationalWordWidth (row j) ≤ W) :
    rowEncodingBitWork primitive row ≤
      (4 * c + 6) * (binaryWordWidth n + 1) ^ 2 + n * (10 * c + 20) * (W + 1) ^ 2 +
        (n + 1) * n * (2 * W + 1) + 2 * binaryWordWidth n + 1 + 2 * n := by
  have hRow := encodingBitWork_bound primitive c hPrimitive (List.ofFn row) W
    (by intro q hq; rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩; exact hWidth j)
  simp only [List.length_ofFn] at hRow
  have hDim := BinaryNatFrame.encodingBitWork_uniform_bound primitive c hPrimitive n (binaryWordWidth n) le_rfl
  unfold rowEncodingBitWork
  rw [BinaryNatFrame.encode_length]
  omega

end Blotto.BinaryRatListFrame
