import Blotto.GeneralPaperEncodedLabelStorage

/-! Structural backtracking storage follows successful and failing native
branches. Frames borrow retained DP tables/tags, keep finite predecessor
indices and retain a left result while the right branch runs. Concatenation
counts old lists, output/copied cells and the left-copy recursion stack.
The observer is erased; no backtracking replay executes in the selector. -/
namespace Blotto.GeneralPaperTypedDecodeStorage
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP GeneralPaperEncodedLabelStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def frame (W K J H : ℕ) : ℕ :=
  256*W+4*GeneralPaperEncodedFixedVector.rankWord J+
    2*GeneralPaperEncodedScalarStorage.natBits H+GeneralPaperEncodedFixedVector.rankWord K+16

def peak {K J : ℕ} (W H : ℕ) : {h : ℕ} → Computation Tag K J h → Fin J → ℕ
  | _,.leaf states,label =>
    frame W K J H+match states.read label with
      | none => 0
      | some chosen => listFootprint W [chosen.predecessor]
  | _,.node left right states,label =>
    frame W K J H+match states.read label with
      | none => 0
      | some chosen =>
        match decode left chosen.predecessor.1 with
        | none => peak W H left chosen.predecessor.1
        | some ls =>
          match decode right chosen.predecessor.2 with
          | none => max (peak W H left chosen.predecessor.1)
              (listFootprint W ls+peak W H right chosen.predecessor.2)
          | some rs => max (peak W H left chosen.predecessor.1)
              (max (listFootprint W ls+peak W H right chosen.predecessor.2) (appendWindow W ls rs))

def profile (W K J H h : ℕ) : ℕ :=
  2^h*bufferCoefficient W K+(h+1)*frame W K J H

theorem bounded {K J h : ℕ} (W H : ℕ) (computed : Computation Tag K J h) (label : Fin J) :
    peak W H computed label≤profile W K J H h := by
  induction computed generalizing label with
  | leaf states =>
    cases hs : states.read label with
    | none => simp only [peak,hs,profile,pow_zero,one_mul]; omega
    | some chosen =>
      have hl := list_power W 0 [chosen.predecessor] (by simp)
      simp only [pow_zero,one_mul] at hl
      simp only [peak,hs,profile,pow_zero,one_mul]
      unfold bufferCoefficient
      nlinarith only [hl]
  | @node h left right states ihl ihr =>
    have hl := ihl
    have hr := ihr
    cases hs : states.read label with
    | none =>
      simp only [peak,hs,profile]
      nlinarith only [Nat.zero_le (2^(h+1)*bufferCoefficient W K),Nat.zero_le (h*frame W K J H)]
    | some chosen =>
      have hleft := hl chosen.predecessor.1
      have hright := hr chosen.predecessor.2
      unfold profile at hleft hright ⊢
      cases hls : decode left chosen.predecessor.1 with
      | none =>
        simp only [peak,hs,hls]
        rw [pow_succ]
        nlinarith only [hleft,Nat.zero_le (2^h*bufferCoefficient W K)]
      | some ls =>
        have hlen := GeneralPaperTypedDecodeLength.length left chosen.predecessor.1 ls hls
        have hlist := list_power W h ls hlen.le
        have hreserve := Nat.mul_le_mul_left (2^h)
          (show GeneralPaperEncodedFixedVector.rankWord K+34*W≤bufferCoefficient W K by unfold bufferCoefficient; omega)
        have hkeep : listFootprint W ls+peak W H right chosen.predecessor.2≤
            2^(h+1)*bufferCoefficient W K+(h+1)*frame W K J H := by
          rw [pow_succ]
          nlinarith only [hlist,hright,hreserve]
        have hleft' : peak W H left chosen.predecessor.1≤
            2^(h+1)*bufferCoefficient W K+(h+1)*frame W K J H := by
          rw [pow_succ]
          nlinarith only [hleft,Nat.zero_le (2^h*bufferCoefficient W K)]
        cases hrs : decode right chosen.predecessor.2 with
        | none =>
          have hm := max_le hleft' hkeep
          simp only [peak,hs,hls,hrs]
          nlinarith only [hm]
        | some rs =>
          have hrlen := GeneralPaperTypedDecodeLength.length right chosen.predecessor.2 rs hrs
          have ha := append_window W h ls rs hlen.le hrlen.le
          have hm := max_le hleft' (max_le hkeep (ha.trans (Nat.le_add_right _ _)))
          simp only [peak,hs,hls,hrs]
          nlinarith only [hm]

theorem returned {K J h : ℕ} (A W : ℕ) (computed : Computation Tag K J h) (label : Fin J)
    (labels : List (Fin K)) (hs : (GeneralPaperTypedDecodeExecution.run A computed label).1=some labels) :
    listFootprint W labels≤2^h*(GeneralPaperEncodedFixedVector.rankWord K+34*W) :=
  list_power W h labels (GeneralPaperTypedDecodeExecution.length A computed label labels hs).le

theorem controls {K J : ℕ} (W H h : ℕ) (label left right : Fin J) (hh : h≤H) :
    GeneralPaperEncodedScalarStorage.natBits h+
      GeneralPaperEncodedFixedVector.rankBits label+GeneralPaperEncodedFixedVector.rankBits left+
      GeneralPaperEncodedFixedVector.rankBits right+64*W≤frame W K J H := by
  have hheight := Nat.add_le_add_left (binaryWordWidth_mono hh) 1
  have hl := GeneralPaperEncodedFixedVector.rank_bound label
  have ha := GeneralPaperEncodedFixedVector.rank_bound left
  have hb := GeneralPaperEncodedFixedVector.rank_bound right
  unfold frame GeneralPaperEncodedScalarStorage.natBits
  omega

end Blotto.GeneralPaperTypedDecodeStorage
