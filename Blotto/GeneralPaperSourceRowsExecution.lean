import Blotto.GeneralPaperRowBudgetExecution

/-! Decode and check the already-produced code table once. The row builder
stores complete rational bids, then checks that whole row before retaining
it. The outer loop accumulates the check flag and pushes one row reference.
Neither source construction nor coordinate resampling occurs here. -/
namespace Blotto.GeneralPaperSourceRowsExecution
open GeneralPaperCodeAlphabet GeneralPaperSummaryArrayExecution
open GeneralPaperDecodeBucketExecution (primitive)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def index (bits : Bool) : ℕ → ℕ := if bits then fun w => w else fun _ => 1
def address (bits : Bool) (W n : ℕ) : ℕ := if bits then arrayWord W n else W

def row {m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) : FixedArrayTable m ℚ × ℕ :=
  let A := address bits W m
  PaperIndexedArrayConstruction.run (index bits) A (fun j =>
    let bid := GeneralPaperClosedBidExecution.run bits model W a (codes.read j)
    (bid.1,bid.2+64*A))

theorem row_data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W qbar : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) : (row bits model W a codes).1=
      FixedArrayTable.ofFn (fun j => GeneralPaperCatalogueRationalTrajectory.decodeValue m qbar a (codes.read j)) := by
  unfold row
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  exact GeneralPaperClosedBidExecution.data bits model W m qbar a (codes.read j)

theorem row_height {m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) (j : Fin m) :
    RationalHeight ((row bits model W a codes).1.read j) (binaryWordWidth a.C) := by
  rw [row_data bits model W 0,FixedArrayTable.read_ofFn]
  exact GeneralPaperSourceScoreHeights.decoded_height m 0 a (codes.read j)

def rowBitProfile (model : RationalCostModel) (W m : ℕ) (a : Alphabet) : ℕ :=
  m*(GeneralPaperClosedBidExecution.bitProfile model W a+64*arrayWord W m)+44*(m+1)*arrayWord W m

def rowArithmeticProfile (m : ℕ) (a : Alphabet) : ℕ :=
  m*(GeneralPaperClosedBidExecution.arithmeticProfile a+64)+44*(m+1)

theorem row_bit_work {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) (hc : ∀ j,codes.read j≤8*a.C) :
    (row true model W a codes).2≤rowBitProfile model W m a := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m)
    (GeneralPaperClosedBidExecution.bitProfile model W a+64*arrayWord W m)
    (fun j => let bid := GeneralPaperClosedBidExecution.run true model W a (codes.read j)
      (bid.1,bid.2+64*arrayWord W m))
    (GeneralPaperSummaryArrayControls.array_word_positive W m)
    (GeneralPaperSummaryArrayControls.array_index W m) (fun j =>
      Nat.add_le_add_right (GeneralPaperClosedBidExecution.bit_work model W a (codes.read j) (hc j)) _)
  exact h

theorem row_arithmetic_work {m : ℕ} (model : RationalCostModel) (a : Alphabet) (codes : FixedArrayTable m ℕ) :
    (row false model 1 a codes).2≤rowArithmeticProfile m a := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1
    (GeneralPaperClosedBidExecution.arithmeticProfile a+64)
    (fun j => let bid := GeneralPaperClosedBidExecution.run false model 1 a (codes.read j)
      (bid.1,bid.2+64)) (Nat.le_refl 1) (fun _ _ => Nat.le_refl 1) (fun j =>
        Nat.add_le_add_right (GeneralPaperClosedBidExecution.arithmetic_work model a (codes.read j)) _)
  simpa only [row,rowArithmeticProfile,index,address,Bool.false_eq_true,ite_false,Nat.mul_one] using h

def fill {T m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) :
    (count : ℕ) → count≤T → (Array (FixedArrayTable m ℚ) × Bool) × ℕ
  | 0,_ => ((#[],true),PaperIndexedArrayConstruction.initialWork (index bits) (address bits W T) T)
  | k+1,hk =>
    let earlier := fill bits model W a codes B k (by omega)
    let decoded := row bits model W a (codes.read ⟨k,by omega⟩)
    let checked := GeneralPaperRowBudgetExecution.run (primitive bits model) (index bits)
      (address bits W m) decoded.1 B
    ((earlier.1.1.push decoded.1,earlier.1.2 && checked.1),earlier.2+decoded.2+checked.2+
      PaperIndexedArrayConstruction.stepWork (index bits) (address bits W T) k+64*address bits W T)

theorem fill_data {T m : ℕ} (bits : Bool) (model : RationalCostModel) (W qbar : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) (count : ℕ) (hc : count≤T) :
    (fill bits model W a codes B count hc).1.1=Array.ofFn (fun i : Fin count =>
      FixedArrayTable.ofFn (fun j => GeneralPaperCatalogueRationalTrajectory.decodeValue m qbar a
        ((codes.read ⟨i.val,by omega⟩).read j))) := by
  induction count with
  | zero => simp only [fill,Array.ofFn_zero]
  | succ k ih =>
    rw [fill]
    dsimp only
    rw [ih (by omega),Array.ofFn_succ,row_data bits model W qbar]
    rfl

def run {T m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) :
    (FixedArrayTable T (FixedArrayTable m ℚ) × Bool) × ℕ :=
  let produced := fill bits model W a codes B T le_rfl
  ((⟨produced.1.1,by rw [fill_data bits model W 0,Array.size_ofFn]⟩,produced.1.2),produced.2)

theorem data {T m : ℕ} (bits : Bool) (model : RationalCostModel) (W qbar : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) : (run bits model W a codes B).1.1=
      FixedArrayTable.ofFn (fun i => FixedArrayTable.ofFn (fun j =>
        GeneralPaperCatalogueRationalTrajectory.decodeValue m qbar a ((codes.read i).read j))) := by
  unfold run FixedArrayTable.ofFn
  dsimp only
  congr 1
  exact fill_data bits model W qbar a codes B T le_rfl

theorem fill_checks {T m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) (count : ℕ) (hc : count≤T) :
    (fill bits model W a codes B count hc).1.2=true ↔ ∀ i : Fin count,
      (∀ j,0≤GeneralPaperCatalogueRationalTrajectory.decodeValue m 0 a ((codes.read ⟨i.val,by omega⟩).read j)) ∧
      (∑ j,GeneralPaperCatalogueRationalTrajectory.decodeValue m 0 a ((codes.read ⟨i.val,by omega⟩).read j))≤B := by
  induction count with
  | zero => simp only [fill,IsEmpty.forall_iff]
  | succ k ih =>
    rw [fill]
    dsimp only
    rw [Bool.and_eq_true,ih (by omega),GeneralPaperRowBudgetExecution.correct,
      row_data bits model W 0]
    simp only [FixedArrayTable.read_ofFn]
    constructor
    · rintro ⟨hPrefix,hLast⟩ i
      exact Fin.lastCases hLast (fun j => hPrefix j) i
    · intro h
      exact ⟨fun i => h i.castSucc,h (Fin.last k)⟩

theorem checks {T m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) :
    (run bits model W a codes B).1.2=true ↔ ∀ i,
      (∀ j,0≤((run bits model W a codes B).1.1.read i).read j) ∧
      (∑ j,((run bits model W a codes B).1.1.read i).read j)≤B := by
  rw [data bits model W 0]
  simp only [FixedArrayTable.read_ofFn]
  exact fill_checks bits model W a codes B T le_rfl

def bitProfile (model : RationalCostModel) (W T m t : ℕ) (a : Alphabet) : ℕ :=
  T*(rowBitProfile model W m a+GeneralPaperRowBudgetExecution.bitProfile model (arrayWord W m)
    m (binaryWordWidth a.C) t+64*arrayWord W T)+44*(T+1)*arrayWord W T

def arithmeticProfile (T m : ℕ) (a : Alphabet) : ℕ :=
  T*(rowArithmeticProfile m a+(77*m+66)+64)+44*(T+1)

theorem fill_bit_work {T m : ℕ} (model : RationalCostModel) (W t : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) (hB : RationalHeight B t)
    (hCode : ∀ i j,(codes.read i).read j≤8*a.C) (count : ℕ) (hc : count≤T) :
    (fill true model W a codes B count hc).2≤
      count*(rowBitProfile model W m a+GeneralPaperRowBudgetExecution.bitProfile model (arrayWord W m)
        m (binaryWordWidth a.C) t+64*arrayWord W T)+
        PaperIndexedArrayConstruction.overhead (fun w => w) (arrayWord W T) T count := by
  induction count with
  | zero => simp only [fill,PaperIndexedArrayConstruction.overhead,index,address,ite_true,
      Nat.zero_mul,Nat.zero_add,le_refl]
  | succ k ih =>
    have hd := row_bit_work model W a (codes.read ⟨k,by omega⟩) (hCode _)
    have hb := GeneralPaperRowBudgetExecution.bit_work model (fun w => w) (arrayWord W m)
      (binaryWordWidth a.C) t (row true model W a (codes.read ⟨k,by omega⟩)).1
      (row_height true model W a _) B hB
      (GeneralPaperSummaryArrayControls.array_word_positive W m)
      (GeneralPaperSummaryArrayControls.array_index W m)
    have hi := ih (by omega)
    rw [fill,PaperIndexedArrayConstruction.overhead]
    simp only [primitive,index,address,ite_true]
    nlinarith only [hd,hb,hi]

theorem bit_work {T m : ℕ} (model : RationalCostModel) (W t : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) (hB : RationalHeight B t)
    (hCode : ∀ i j,(codes.read i).read j≤8*a.C) :
    (run true model W a codes B).2≤bitProfile model W T m t a := by
  have h := fill_bit_work model W t a codes B hB hCode T le_rfl
  have ho := GeneralPaperControlArrayPrice.overhead (fun w => w) (arrayWord W T) T T
    (GeneralPaperSummaryArrayControls.array_word_positive W T) le_rfl
    (GeneralPaperSummaryArrayControls.array_index W T)
  unfold run bitProfile
  dsimp only
  omega

theorem fill_arithmetic_work {T m : ℕ} (model : RationalCostModel) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) (count : ℕ) (hc : count≤T) :
    (fill false model 1 a codes B count hc).2≤
      count*(rowArithmeticProfile m a+(77*m+66)+64)+
        PaperIndexedArrayConstruction.overhead (fun _ => 1) 1 T count := by
  induction count with
  | zero => simp only [fill,PaperIndexedArrayConstruction.overhead,index,address,
      Bool.false_eq_true,ite_false,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ k ih =>
    have hd := row_arithmetic_work model a (codes.read ⟨k,by omega⟩)
    have hb := GeneralPaperRowBudgetExecution.arithmetic_work
      (row false model 1 a (codes.read ⟨k,by omega⟩)).1 B
    have hi := ih (by omega)
    rw [fill,PaperIndexedArrayConstruction.overhead]
    simp only [primitive,index,address,Bool.false_eq_true,ite_false,Nat.mul_one]
    nlinarith only [hd,hb,hi]

theorem arithmetic_work {T m : ℕ} (model : RationalCostModel) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) :
    (run false model 1 a codes B).2≤arithmeticProfile T m a := by
  have h := fill_arithmetic_work model a codes B T le_rfl
  have ho := GeneralPaperControlArrayPrice.overhead (fun _ => 1) 1 T T le_rfl le_rfl (fun _ _ => le_rfl)
  unfold run arithmeticProfile
  dsimp only
  omega

end Blotto.GeneralPaperSourceRowsExecution
