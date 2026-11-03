import Blotto.GeneralPaperClosedBidExecution

/-! Literal one-pass hard-budget check on a retained rational whole row.
All entries are tested for nonnegativity, every sum prefix is priced, and
the final total is compared to the player's at-most budget, including m=0. -/
namespace Blotto.GeneralPaperRowBudgetExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def scan {m : ℕ} (price index : ℕ → ℕ) (W : ℕ) (row : FixedArrayTable m ℚ) :
    (count : ℕ) → count≤m → (ℚ × Bool) × ℕ
  | 0,_ => ((0,true),price (rationalWordWidth (0:ℚ))+32*W)
  | k+1,hk =>
    let earlier := scan price index W row k (by omega)
    let q := row.read ⟨k,by omega⟩
    let nonnegative := decide (0≤q)
    ((earlier.1.1+q,earlier.1.2 && nonnegative),earlier.2+
      GeneralPaperRationalPrimitivePrice.binary price (fun a b => a+b) earlier.1.1 q+
      price (RationalExpression.pairWidth q 0)+PaperIndexedArrayConstruction.stepWork index W k+32*W)

def run {m : ℕ} (price index : ℕ → ℕ) (W : ℕ) (row : FixedArrayTable m ℚ) (B : ℚ) : Bool × ℕ :=
  let checked := scan price index W row m le_rfl
  let within := decide (checked.1.1≤B)
  (checked.1.2 && within,checked.2+price (RationalExpression.pairWidth checked.1.1 B)+32*W)

theorem scan_total {m : ℕ} (price index : ℕ → ℕ) (W : ℕ) (row : FixedArrayTable m ℚ)
    (count : ℕ) (hc : count≤m) :
    (scan price index W row count hc).1.1=∑ i : Fin count,row.read ⟨i.val,by omega⟩ := by
  induction count with
  | zero => simp only [scan,Finset.univ_eq_empty,Finset.sum_empty]
  | succ k ih =>
    rw [scan]
    dsimp only
    rw [ih (by omega),Fin.sum_univ_castSucc]
    rfl

theorem scan_nonnegative {m : ℕ} (price index : ℕ → ℕ) (W : ℕ) (row : FixedArrayTable m ℚ)
    (count : ℕ) (hc : count≤m) :
    (scan price index W row count hc).1.2=true ↔ ∀ i : Fin count,0≤row.read ⟨i.val,by omega⟩ := by
  induction count with
  | zero => simp only [scan,IsEmpty.forall_iff]
  | succ k ih =>
    rw [scan]
    dsimp only
    rw [Bool.and_eq_true,decide_eq_true_eq,ih (by omega)]
    constructor
    · rintro ⟨hPrefix,hLast⟩ i
      exact Fin.lastCases hLast (fun j => hPrefix j) i
    · intro h
      exact ⟨fun i => h i.castSucc,h (Fin.last k)⟩

theorem correct {m : ℕ} (price index : ℕ → ℕ) (W : ℕ) (row : FixedArrayTable m ℚ) (B : ℚ) :
    (run price index W row B).1=true ↔ (∀ j,0≤row.read j) ∧ (∑ j,row.read j)≤B := by
  unfold run
  dsimp only
  rw [Bool.and_eq_true,decide_eq_true_eq,scan_total,scan_nonnegative]

theorem scan_height {m : ℕ} (price index : ℕ → ℕ) (W s : ℕ) (row : FixedArrayTable m ℚ)
    (h : ∀ j,RationalHeight (row.read j) s) (count : ℕ) (hc : count≤m) :
    RationalHeight (scan price index W row count hc).1.1 ((s+1)*count+1) := by
  induction count with
  | zero => simp only [scan,Nat.mul_zero,Nat.zero_add]; norm_num [RationalHeight]
  | succ k ih =>
    have hs := (ih (by omega)).add (h ⟨k,by omega⟩)
    rw [scan]
    dsimp only
    convert hs using 1; ring

def width (m s t : ℕ) : ℕ := 1+2*((s+1)*m+s+t+4)

def bitProfile (model : RationalCostModel) (W m s t : ℕ) : ℕ :=
  (3*m+2)*model.rat (width m s t)+128*(m+1)*W

theorem scan_work {m : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (W s t : ℕ)
    (row : FixedArrayTable m ℚ) (h : ∀ j,RationalHeight (row.read j) s)
    (hW : 1≤W) (hi : ∀ i≤m,index (binaryWordWidth (i+1))≤W)
    (count : ℕ) (hc : count≤m) :
    (scan model.rat index W row count hc).2≤(3*count+1)*model.rat (width m s t)+(96*count+32)*W := by
  let L := width m s t
  have hZero : rationalWordWidth (0:ℚ)≤L := by
    rw [show rationalWordWidth (0:ℚ)=3 by decide]; unfold L width; omega
  have hz := model.monotone hZero
  dsimp only [L] at hz
  induction count with
  | zero => simp only [scan,Nat.mul_zero,Nat.zero_add,Nat.one_mul]; omega
  | succ k ih =>
    let old := scan model.rat index W row k (by omega)
    let q := row.read ⟨k,by omega⟩
    have hOld := rationalWordWidth_of_height (scan_height model.rat index W s row h k (by omega))
    have hFull := rationalWordWidth_of_height (scan_height model.rat index W s row h (k+1) hc)
    have hq := rationalWordWidth_of_height (h ⟨k,by omega⟩)
    have hk := Nat.mul_le_mul_left (s+1) (show k≤m by omega)
    have hk' := Nat.mul_le_mul_left (s+1) hc
    have hOld' : rationalWordWidth old.1.1≤L := by dsimp only [old,L]; unfold width; omega
    have hq' : rationalWordWidth q≤L := by dsimp only [q,L]; unfold width; omega
    have hFull' : rationalWordWidth (old.1.1+q)≤L := by
      change rationalWordWidth (scan model.rat index W row (k+1) hc).1.1≤L
      dsimp only [L]; unfold width; omega
    have hadd := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone
      (fun a b => a+b) old.1.1 q L hOld' hq' hFull'
    have htest := model.monotone (max_le hq' hZero)
    have hIndex := hi k (by omega)
    have hEarlier := ih (by omega)
    rw [scan]
    dsimp only
    change old.2+GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a+b) old.1.1 q+
      model.rat (RationalExpression.pairWidth q 0)+PaperIndexedArrayConstruction.stepWork index W k+32*W≤_
    unfold RationalExpression.pairWidth at htest ⊢
    unfold PaperIndexedArrayConstruction.stepWork
    nlinarith only [hEarlier,hadd,htest,hIndex,hW]

theorem bit_work {m : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (W s t : ℕ)
    (row : FixedArrayTable m ℚ) (h : ∀ j,RationalHeight (row.read j) s) (B : ℚ) (hB : RationalHeight B t)
    (hW : 1≤W) (hi : ∀ i≤m,index (binaryWordWidth (i+1))≤W) :
    (run model.rat index W row B).2≤bitProfile model W m s t := by
  have hs := scan_work model index W s t row h hW hi m le_rfl
  have hTotal := rationalWordWidth_of_height (scan_height model.rat index W s row h m le_rfl)
  have hb := rationalWordWidth_of_height hB
  have hw : max (rationalWordWidth (scan model.rat index W row m le_rfl).1.1) (rationalWordWidth B)≤width m s t := by
    unfold width; omega
  have hp := model.monotone hw
  unfold run bitProfile RationalExpression.pairWidth
  dsimp only
  nlinarith only [hs,hp]

theorem scan_arithmetic {m : ℕ} (row : FixedArrayTable m ℚ) (count : ℕ) (hc : count≤m) :
    (scan (fun _ => 1) (fun _ => 1) 1 row count hc).2=77*count+33 := by
  induction count with
  | zero => rfl
  | succ k ih =>
    rw [scan]
    dsimp only
    rw [ih (by omega)]
    unfold GeneralPaperRationalPrimitivePrice.binary PaperIndexedArrayConstruction.stepWork
    dsimp only
    omega

theorem arithmetic_work {m : ℕ} (row : FixedArrayTable m ℚ) (B : ℚ) :
    (run (fun _ => 1) (fun _ => 1) 1 row B).2=77*m+66 := by
  unfold run
  dsimp only
  rw [scan_arithmetic]

end Blotto.GeneralPaperRowBudgetExecution
