import Blotto.GeneralPaperOuterEpochPrice

/-! Initialize four sparse forest arrays. Each entry is one uniform node;
initialization never enumerates the exponentially many represented codes. -/
namespace Blotto.GeneralPaperForestInitialPrice
open GeneralPaperCatalogueTreeCache GeneralPaperIntervalCache
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def family (bits : Bool) (index : ℕ → ℕ) (W m height : ℕ) : FixedArrayTable m (Node height) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W)
    (fun _ => (.uniform height 0,(if bits then 1+binaryWordWidth height else 1)+64*W))

def run (bits : Bool) (index : ℕ → ℕ) (W m lambda : ℕ) : Trees m lambda × ℕ :=
  let height := lambda+1
  let p := family bits index W m lambda
  let q := family bits index W m lambda
  let l := family bits index W m height
  let u := family bits index W m height
  (⟨p.1,q.1,l.1,u.1⟩,p.2+q.2+l.2+u.2+
    GeneralPaperNaturalPrimitivePrice.binary index (fun a b => a+b) lambda 1+256*W)

def profile (W m lambda : ℕ) : ℕ :=
  4*(m*(1+binaryWordWidth (lambda+1)+64*W)+44*(m+1)*arrayWord W m)+2*(1+binaryWordWidth (lambda+1))+256*W

def arithmeticProfile (m : ℕ) : ℕ := 4*(65*m+44*(m+1))+2+256

theorem data (bits : Bool) (index : ℕ → ℕ) (W m lambda : ℕ) : (run bits index W m lambda).1=initial m lambda := by
  simp only [run,family,PaperIndexedArrayConstruction.run_data]
  rfl

theorem family_work (W m lambda height : ℕ) (hh : height≤lambda+1) :
    (family true (fun x => x) W m height).2≤m*(1+binaryWordWidth (lambda+1)+64*W)+44*(m+1)*arrayWord W m := by
  exact GeneralPaperControlArrayPrice.indexed_work (fun x => x) (arrayWord W m) _ _
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
    (fun _ => Nat.add_le_add_right (Nat.add_le_add_left (binaryWordWidth_mono hh) 1) _)

theorem family_arithmetic_work (m height : ℕ) :
    (family false (fun _ => 1) 1 m height).2≤65*m+44*(m+1) := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 65
    (fun _ : Fin m => (Node.uniform height 0,65)) (Nat.le_refl _)
    (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  calc
    _≤m*65+44*(m+1)*1 := h
    _=65*m+44*(m+1) := by ring

theorem work (W m lambda : ℕ) : (run true (fun x => x) W m lambda).2≤profile W m lambda ∧
    (run false (fun _ => 1) 1 m lambda).2≤arithmeticProfile m := by
  have hp := family_work W m lambda lambda (by omega)
  have hl := family_work W m lambda (lambda+1) (Nat.le_refl _)
  have hi := GeneralPaperNaturalPrimitivePrice.binary_le (fun x => x) (fun _ _ h => h) (fun a b => a+b) lambda 1 (lambda+1) (by omega) (by omega) (Nat.le_refl _)
  have hpu := family_arithmetic_work m lambda
  have hlu := family_arithmetic_work m (lambda+1)
  constructor
  · change _≤4*(m*(1+binaryWordWidth (lambda+1)+64*W)+44*(m+1)*arrayWord W m)+2*(1+binaryWordWidth (lambda+1))+256*W
    change _+_+_+_+_+256*W≤_
    omega
  · change _+_+_+_+2+256≤4*(65*m+44*(m+1))+2+256
    omega

end Blotto.GeneralPaperForestInitialPrice
