import Blotto.GeneralPaperCodeEvaluatePrice

/-! Complete fixed-candidate scan prices. Every suffix uses its native
selection/counter certificates; the five-element length bound is derived
by the caller and is never recomputed as an execution pass.
-/
namespace Blotto.GeneralPaperCodeScanPrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls GeneralPaperCodeScanExecution
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def stepProfile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCodeEvaluatePrice.profile model W a+5*model.rat (operandWidth a.lambda)+128*W

def profile (model : RationalCostModel) (W : ℕ) (a : Alphabet) (count : ℕ) : ℕ := count*stepProfile model W a+64*W

def arithmeticProfile (a : Alphabet) (count : ℕ) : ℕ :=
  count*(GeneralPaperCodeEvaluatePrice.arithmeticProfile a+133)+64

theorem bit_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (hLo : lo≤8*a.C) (hHi : hi≤8*a.C) (codes : List ℕ) (hLength : codes.length≤5)
    (hCodes : ∀ code∈codes,code≤8*a.C) :
    (scan true model W a response lo hi codes).2≤profile model W a codes.length := by
  revert hLength hCodes
  induction codes with
  | nil => intro _ _; simp only [scan,profile,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons code rest ih =>
    intro hLength hCodes
    let tested := evaluate true model W a response lo hi code
    let later := scan true model W a response lo hi rest
    let chosen := GeneralPaperCodePickPrice.run model.rat W tested.1.selected later.1.selected
    have ht := GeneralPaperCodeEvaluatePrice.bit_work model W a response lo hi code hLo hHi (hCodes _ List.mem_cons_self)
    have hl := ih (by simp only [List.length_cons] at hLength; omega)
      (fun c hc => hCodes c (List.mem_cons_of_mem _ hc))
    have hp := GeneralPaperCodePickPrice.bit_work model W a tested.1.selected later.1.selected
      (evaluate_selected_bound true model W a response lo hi code)
      (scan_selected_bound true model W a response lo hi rest)
    have ha := GeneralPaperCodeScanOperands.additions_work model W a response lo hi code rest hLength
    change tested.2≤_ at ht
    change later.2≤_ at hl
    change chosen.2≤_ at hp
    change additions model.rat tested.1.work later.1.work≤_ at ha
    have hStep : tested.2+chosen.2+additions model.rat tested.1.work later.1.work+64*W≤stepProfile model W a := by
      unfold stepProfile
      omega
    rw [scan]
    dsimp only
    simp only [primitive,ite_true]
    change tested.2+later.2+chosen.2+additions model.rat tested.1.work later.1.work+64*W≤_
    calc
      _ = later.2+(tested.2+chosen.2+additions model.rat tested.1.work later.1.work+64*W) := by omega
      _ ≤ profile model W a rest.length+stepProfile model W a := Nat.add_le_add hl hStep
      _ = profile model W a (code::rest).length := by unfold profile; simp only [List.length_cons]; ring

theorem arithmetic_work (model : RationalCostModel) (a : Alphabet) (response : Bool) (lo hi : ℕ) (codes : List ℕ) :
    (scan false model 1 a response lo hi codes).2≤arithmeticProfile a codes.length := by
  induction codes with
  | nil => simp only [scan,arithmeticProfile,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons code rest ih =>
    let tested := evaluate false model 1 a response lo hi code
    let later := scan false model 1 a response lo hi rest
    let chosen := GeneralPaperCodePickPrice.run (fun _ => 1) 1 tested.1.selected later.1.selected
    have ht := GeneralPaperCodeEvaluatePrice.arithmetic_work model a response lo hi code
    have hp := GeneralPaperCodePickPrice.arithmetic_work tested.1.selected later.1.selected
    change tested.2≤_ at ht
    change later.2≤_ at ih
    change chosen.2≤_ at hp
    have hStep : tested.2+chosen.2+4+64≤GeneralPaperCodeEvaluatePrice.arithmeticProfile a+133 := by omega
    rw [scan]
    dsimp only
    change tested.2+later.2+chosen.2+4+64≤_
    calc
      _ = later.2+(tested.2+chosen.2+4+64) := by omega
      _ ≤ arithmeticProfile a rest.length+(GeneralPaperCodeEvaluatePrice.arithmeticProfile a+133) := Nat.add_le_add ih hStep
      _ = arithmeticProfile a (code::rest).length := by unfold arithmeticProfile; simp only [List.length_cons]; ring

end Blotto.GeneralPaperCodeScanPrice
