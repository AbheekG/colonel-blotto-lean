import Blotto.GeneralPaperClosedBidStorage

/-! Rational budget-check stack ownership. Descent frames borrow the row;
unwind keeps only the child total, next coordinate, new total and current
primitive scratch. No whole-row arithmetic time is used as its workspace. -/
namespace Blotto.GeneralPaperRowBudgetStorage
open GeneralPaperRowBudgetExecution GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def frame (W m count : ℕ) : ℕ := fields W [m,count]+128*W+1
def frameProfile (W m : ℕ) : ℕ := 2*(1+binaryWordWidth (m+1))+162*W+1

theorem frame_bound (W m count : ℕ) (hc : count≤m) : frame W m count≤frameProfile W m := by
  have hm := binaryWordWidth_mono (show m≤m+1 by omega)
  have hk := binaryWordWidth_mono (show count≤m+1 by omega)
  unfold frame frameProfile fields natBits
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

def localWindow {m : ℕ} (model : RationalCostModel) (W : ℕ) (row : FixedArrayTable m ℚ)
    (count : ℕ) (hc : count+1≤m) : ℕ :=
  let old := (scan model.rat (fun w => w) W row count (by omega)).1.1
  let q := row.read ⟨count,by omega⟩
  rationalWordWidth old+rationalWordWidth q+rationalWordWidth (old+q)+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a+b) old q+
    model.rat (RationalExpression.pairWidth q 0)+256*W+2

def tailProfile (model : RationalCostModel) (W m s t : ℕ) : ℕ :=
  8*model.rat (width m s t)+512*W+4

theorem prefix_word {m : ℕ} (model : RationalCostModel) (W s t : ℕ) (row : FixedArrayTable m ℚ)
    (h : ∀ j,RationalHeight (row.read j) s) (count : ℕ) (hc : count≤m) :
    rationalWordWidth (scan model.rat (fun w => w) W row count hc).1.1≤width m s t := by
  have hs := rationalWordWidth_of_height (scan_height model.rat (fun w => w) W s row h count hc)
  have hm := Nat.mul_le_mul_left (s+1) hc
  unfold width
  omega

theorem coordinate_word {m : ℕ} (s t : ℕ) (row : FixedArrayTable m ℚ)
    (h : ∀ j,RationalHeight (row.read j) s) (j : Fin m) : rationalWordWidth (row.read j)≤width m s t := by
  have hs := rationalWordWidth_of_height (h j)
  unfold width
  omega

theorem local_bound {m : ℕ} (model : RationalCostModel) (W s t : ℕ) (row : FixedArrayTable m ℚ)
    (h : ∀ j,RationalHeight (row.read j) s) (count : ℕ) (hc : count+1≤m) :
    localWindow model W row count hc≤tailProfile model W m s t := by
  let old := (scan model.rat (fun w => w) W row count (by omega)).1.1
  let q := row.read ⟨count,by omega⟩
  let L := width m s t
  have ho : rationalWordWidth old≤L := prefix_word model W s t row h count (by omega)
  have hq : rationalWordWidth q≤L := coordinate_word s t row h ⟨count,by omega⟩
  have hn : rationalWordWidth (old+q)≤L := prefix_word model W s t row h (count+1) hc
  have hz : rationalWordWidth (0:ℚ)≤L := by
    rw [show rationalWordWidth (0:ℚ)=3 by decide]
    unfold L width
    omega
  have hb := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b) old q L ho hq hn
  have hp : model.rat (RationalExpression.pairWidth q 0)≤model.rat L := model.monotone (max_le hq hz)
  have ho' := ho.trans (model.word_le _)
  have hq' := hq.trans (model.word_le _)
  have hn' := hn.trans (model.word_le _)
  change rationalWordWidth old+rationalWordWidth q+rationalWordWidth (old+q)+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a+b) old q+
    model.rat (RationalExpression.pairWidth q 0)+256*W+2≤8*model.rat L+512*W+4
  omega

def peak {m : ℕ} (model : RationalCostModel) (W : ℕ) (row : FixedArrayTable m ℚ) :
    (count : ℕ) → count≤m → ℕ
  | 0,_ => frame W m 0+rationalWordWidth (0:ℚ)+model.rat (rationalWordWidth (0:ℚ))+128*W+1
  | k+1,hk => frame W m (k+1)+max (peak model W row k (by omega)) (localWindow model W row k hk)

theorem peak_bound {m : ℕ} (model : RationalCostModel) (W s t : ℕ) (row : FixedArrayTable m ℚ)
    (h : ∀ j,RationalHeight (row.read j) s) (count : ℕ) (hc : count≤m) :
    peak model W row count hc≤(count+1)*frameProfile W m+tailProfile model W m s t := by
  induction count with
  | zero =>
    have hf := frame_bound W m 0 hc
    have hz : rationalWordWidth (0:ℚ)≤width m s t := by
      rw [show rationalWordWidth (0:ℚ)=3 by decide]; unfold width; omega
    have hp := model.monotone hz
    have hw := hz.trans (model.word_le _)
    simp only [peak,Nat.zero_add,Nat.one_mul]
    unfold tailProfile
    omega
  | succ k ih =>
    have hf := frame_bound W m (k+1) hc
    have hi := ih (by omega)
    have hl := local_bound model W s t row h k hc
    have hm := max_le hi (hl.trans (Nat.le_add_left _ _))
    rw [peak]
    nlinarith only [hf,hm]

def finalWindow {m : ℕ} (model : RationalCostModel) (W : ℕ) (row : FixedArrayTable m ℚ) (B : ℚ) : ℕ :=
  let total := (scan model.rat (fun w => w) W row m le_rfl).1.1
  rationalWordWidth total+rationalWordWidth B+model.rat (RationalExpression.pairWidth total B)+128*W+2

theorem final_bound {m : ℕ} (model : RationalCostModel) (W s t : ℕ) (row : FixedArrayTable m ℚ)
    (h : ∀ j,RationalHeight (row.read j) s) (B : ℚ) (hB : RationalHeight B t) :
    finalWindow model W row B≤tailProfile model W m s t := by
  have hs := prefix_word model W s t row h m le_rfl
  have hb := rationalWordWidth_of_height hB
  have hb' : rationalWordWidth B≤width m s t := by unfold width; omega
  have hp := model.monotone (max_le hs hb')
  have hs' := hs.trans (model.word_le _)
  have hb'' := hb'.trans (model.word_le _)
  unfold finalWindow tailProfile RationalExpression.pairWidth
  dsimp only
  omega

def window {m : ℕ} (model : RationalCostModel) (W : ℕ) (row : FixedArrayTable m ℚ) (B : ℚ) : ℕ :=
  rationalWordWidth B+max (peak model W row m le_rfl) (finalWindow model W row B)

def profile (model : RationalCostModel) (W m s t : ℕ) : ℕ :=
  (1+2*t)+(m+1)*frameProfile W m+tailProfile model W m s t

theorem bounded {m : ℕ} (model : RationalCostModel) (W s t : ℕ) (row : FixedArrayTable m ℚ)
    (h : ∀ j,RationalHeight (row.read j) s) (B : ℚ) (hB : RationalHeight B t) :
    window model W row B≤profile model W m s t := by
  have hp := peak_bound model W s t row h m le_rfl
  have hf := final_bound model W s t row h B hB
  have hm := max_le hp (hf.trans (Nat.le_add_left _ _))
  have hb := rationalWordWidth_of_height hB
  unfold window profile
  omega

end Blotto.GeneralPaperRowBudgetStorage
