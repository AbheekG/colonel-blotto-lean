import Blotto.GeneralPaperRankReturnPrice

/-! Complete bit cost of the actual binary search. The index interval and
fuel provide all midpoint/control/return operand caps. Code comparands are
bounded by V, later supplied by the actual source code/cut arrays.
-/
namespace Blotto.GeneralPaperRankBits
open GeneralPaperRankExecution GeneralPaperRankOperands
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W : ℕ)
    (values : FixedArrayTable n ℕ) (cut depth V fuel lo hi : ℕ)
    (hOrder : lo≤hi) (hHi : hi≤n) (hSize : n<2^depth) (hFuel : fuel≤depth)
    (hCut : cut≤V) (hValues : ∀ i,values.read i≤V) :
    (run true primitive W values cut depth fuel lo hi).2≤512*(fuel+1)*(W+primitive (width depth V)) := by
  let N := magnitude n depth V
  let L := width depth V
  let B := W+primitive L
  have hN := basic n depth V
  have hWord := word_bound n depth V hSize
  have w (a : ℕ) (ha : a≤N) : 1+binaryWordWidth a≤L :=
    (Nat.add_le_add_left (binaryWordWidth_mono ha) 1).trans hWord
  induction fuel generalizing lo hi with
  | zero =>
    have ht := GeneralPaperIntegerWordPrice.compare_le primitive hMono 0 0 L (w _ (by omega)) (w _ (by omega))
    change 64*W+GeneralPaperIntegerWordPrice.compare primitive 0 0≤512*(0+1)*B
    dsimp only [B]
    omega
  | succ fuel ih =>
    have hc := GeneralPaperRankOperands.control_work primitive hMono W n depth V fuel lo hi hFuel hOrder hHi hSize
    change GeneralPaperRankExecution.control primitive W fuel lo hi≤4*primitive L+64*W at hc
    rw [run]
    dsimp only
    split
    · rename_i hOpen
      have hm := GeneralPaperRankMidpoint.midpoint_inside n depth lo hi hOpen hHi hSize
      have hMid : (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient<n := hm.2.trans_le hHi
      have hd := GeneralPaperRankMidpointPrice.data true primitive W n depth lo hi hOrder hHi hSize
      have hp := GeneralPaperRankOperands.midpoint_work primitive hMono W n depth V lo hi hOrder hHi hSize
      change (GeneralPaperRankMidpointPrice.run true primitive W depth lo hi).2≤8*primitive L+64*W at hp
      have hg := GeneralPaperIntegerWordPrice.compare_le primitive hMono
        (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient n L
        (w _ (by dsimp only [N]; omega)) (w _ (by dsimp only [N]; omega))
      have hv := GeneralPaperIntegerWordPrice.compare_le primitive hMono (values.read ⟨_,hMid⟩) cut L
        (w _ ((hValues _).trans (by dsimp only [N]; omega)))
        (w _ (hCut.trans (by dsimp only [N]; omega)))
      simp only [hd,GeneralPaperRankMidpointPrice.specification,hMid,dite_eq_left]
      split
      · have hChildCost := ih ((GeneralPaperRankMidpoint.midpoint depth lo hi).quotient+1) hi (by omega) hHi (by omega)
        have hf := GeneralPaperRankReturnPrice.work true primitive hMono W depth V fuel values cut
          ((GeneralPaperRankMidpoint.midpoint depth lo hi).quotient+1) hi (GeneralPaperRankMidpointPrice.specification depth lo hi)
          (by omega) hHi hSize (by omega) (GeneralPaperRankMidpoint.midpoint_work _ _ _)
        change _≤6*primitive L+96*W at hf
        dsimp only [GeneralPaperRankMidpointPrice.specification] at hf
        change _≤512*(fuel+1)*B at hChildCost
        have hInc := (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b)
          (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient 1 N
          (by dsimp only [N]; omega) (by dsimp only [N]; omega) (by dsimp only [N]; omega)).trans
            (Nat.mul_le_mul_left 2 (hMono hWord))
        change _≤512*(fuel+1+1)*B
        change _≤2*primitive L at hInc
        dsimp only [B] at hChildCost ⊢
        nlinarith only [hc,hp,hg,hv,hChildCost,hf,hInc]
      · have hChildCost := ih lo (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient hm.1 (by omega) (by omega)
        have hf := GeneralPaperRankReturnPrice.work true primitive hMono W depth V fuel values cut lo
          (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient (GeneralPaperRankMidpointPrice.specification depth lo hi)
          hm.1 (by omega) hSize (by omega) (GeneralPaperRankMidpoint.midpoint_work _ _ _)
        change _≤6*primitive L+96*W at hf
        dsimp only [GeneralPaperRankMidpointPrice.specification] at hf
        change _≤512*(fuel+1)*B at hChildCost
        change _≤512*(fuel+1+1)*B
        dsimp only [B] at hChildCost ⊢
        nlinarith only [hc,hp,hg,hv,hChildCost,hf]
    · change _≤512*(fuel+1+1)*B
      dsimp only [B]
      nlinarith only [hc,Nat.zero_le fuel]

end Blotto.GeneralPaperRankBits
