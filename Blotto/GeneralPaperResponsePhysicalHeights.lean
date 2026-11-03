import Blotto.GeneralPaperSourceRowsModelsContract

/-! Open responses share one physical shift. A sum prefix is a bounded
threshold sum plus an integer multiple of that same shift. Its height is
O(m*Lambda), rather than m times the physical coordinate height. -/
namespace Blotto.GeneralPaperResponsePhysicalHeights
open GeneralPaperCodeAlphabet GeneralPaperTagBudgetTransfer
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def shiftHeight (m qbar C : ℕ) : ℕ :=
  8+binaryWordWidth m+binaryWordWidth qbar+(m+2)*binaryWordWidth C

theorem shift_denominator_word (m qbar C : ℕ) : binaryWordWidth (shiftDenominator m qbar C)≤shiftHeight m qbar C := by
  have h0 := binaryWordWidth_mul 4 m
  have h1 := binaryWordWidth_mul (4*m) qbar
  have h2 := GeneralPaperNatPowerOperands.power_width C (m+2)
  have h3 := binaryWordWidth_mul (4*m*qbar) (C^(m+2))
  rw [show binaryWordWidth 4=3 by decide] at h0
  unfold shiftDenominator shiftHeight
  omega

theorem shift_height (m qbar C : ℕ) : RationalHeight (shift m qbar C) (shiftHeight m qbar C) := by
  have h := (GeneralPaperBasisDivideBits.nat_height (shiftDenominator m qbar C)).inv
  simpa only [shift,one_div] using h.mono (shift_denominator_word m qbar C)

theorem decoded_threshold (a : Alphabet) (response : Bool) (code : ℕ) (c : Choice)
    (hc : (GeneralPaperCodeDecode.decode a response code).choice=some c) :
    RationalHeight c.threshold.value (binaryWordWidth a.C) := by
  have h := GeneralPaperCodeRecordStorage.decoded_bounds a response code c hc
  have hv := RationalHeight.fraction (c.threshold.num:ℤ) c.threshold.den (binaryWordWidth a.C)
    c.threshold.den_pos (by simpa only [Int.natAbs_natCast] using h.1.trans_lt (lt_pow_binaryWordWidth a.C))
    (h.2.trans_lt (lt_pow_binaryWordWidth a.C))
  simpa only [Farey.Fraction.value,Int.cast_natCast] using hv

def openCount {n : ℕ} (choices : Fin n → Choice) : ℕ := ∑ i,if (choices i).opened then 1 else 0

theorem open_count_le {n : ℕ} (choices : Fin n → Choice) : openCount choices≤n := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    show (if (choices i).opened then 1 else 0)≤(1:ℕ) by split <;> omega)
  simpa only [openCount,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.mul_one,Nat.cast_id] using h

theorem physical_sum {n : ℕ} (choices : Fin n → Choice) (delta : ℚ) :
    (∑ i,(choices i).physical delta)=(∑ i,(choices i).threshold.value)+(openCount choices:ℚ)*delta := by
  simp only [Choice.physical,Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i,if (choices i).opened then delta else 0)=
        ∑ i,((if (choices i).opened then 1 else 0:ℕ):ℚ)*delta := by
      apply Finset.sum_congr rfl
      intro i _
      cases (choices i).opened <;> simp
    _=(openCount choices:ℚ)*delta := by
      rw [←Finset.sum_mul]
      simp only [openCount,Nat.cast_sum]

def prefixHeight (m s H : ℕ) : ℕ := (s+1)*m+binaryWordWidth m+H+2

theorem prefix_height {n m : ℕ} (choices : Fin n → Choice) (hn : n≤m) (s H : ℕ)
    (h : ∀ i,RationalHeight (choices i).threshold.value s) (delta : ℚ) (hd : RationalHeight delta H) :
    RationalHeight (∑ i,(choices i).physical delta) (prefixHeight m s H) := by
  have ht := RationalHeight.list_sum (l:=List.ofFn (fun i => (choices i).threshold.value)) (by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact h i)
  simp only [List.sum_ofFn,List.length_ofFn] at ht
  have ho := (GeneralPaperBasisDivideBits.nat_height (openCount choices)).mono
    (binaryWordWidth_mono ((open_count_le choices).trans hn))
  have hp := ht.add (ho.mul hd)
  rw [physical_sum]
  apply hp.mono
  have hnm := Nat.mul_le_mul_left (s+1) hn
  unfold prefixHeight
  omega

def bidHeight (s H : ℕ) : ℕ := s+H+1

theorem bid_height (c : Choice) (s H : ℕ) (h : RationalHeight c.threshold.value s)
    (delta : ℚ) (hd : RationalHeight delta H) : RationalHeight (c.physical delta) (bidHeight s H) := by
  cases hc : c.opened with
  | false =>
    simpa only [Choice.physical,hc,Bool.false_eq_true,ite_false,add_zero] using
      h.mono (show s≤bidHeight s H by unfold bidHeight; omega)
  | true => simpa only [Choice.physical,hc,ite_true,bidHeight] using h.add hd

def word (m s H t : ℕ) : ℕ := 16+2*(prefixHeight m s H+bidHeight s H+t)

theorem prefix_word {n m : ℕ} (choices : Fin n → Choice) (hn : n≤m) (s H t : ℕ)
    (h : ∀ i,RationalHeight (choices i).threshold.value s) (delta : ℚ) (hd : RationalHeight delta H) :
    rationalWordWidth (∑ i,(choices i).physical delta)≤word m s H t := by
  have hp := rationalWordWidth_of_height (prefix_height choices hn s H h delta hd)
  unfold word
  omega

theorem bid_word (m s H t : ℕ) (c : Choice) (h : RationalHeight c.threshold.value s)
    (delta : ℚ) (hd : RationalHeight delta H) : rationalWordWidth (c.physical delta)≤word m s H t := by
  have hp := rationalWordWidth_of_height (bid_height c s H h delta hd)
  unfold word
  omega

end Blotto.GeneralPaperResponsePhysicalHeights
