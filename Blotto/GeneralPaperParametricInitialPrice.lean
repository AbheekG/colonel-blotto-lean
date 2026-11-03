import Blotto.GeneralPaperRayBracketContainment

/-! Build the actual score-zero affine initial table once. The fixed block
price includes the two zero literals, empty predecessor and control/refs.
-/
namespace Blotto.GeneralPaperParametricInitialPrice
open GeneralPaperRayAffineScoreStep
open scoped BigOperators
set_option autoImplicit false

def run (indexPrimitive : ℕ → ℕ) (W S K : ℕ) : Table S K × ℕ :=
  PaperIndexedArrayConstruction.run indexPrimitive W
    (fun s => (if s.val=0 then some ⟨⟨0,0⟩,[]⟩ else none,32*W))

theorem data (indexPrimitive : ℕ → ℕ) (W S K : ℕ) :
    (run indexPrimitive W S K).1=GeneralPaperRayAffineScoreInput.initial S K := by
  simp only [run,PaperIndexedArrayConstruction.run_data,GeneralPaperRayAffineScoreInput.initial]

theorem bit_work (W S K : ℕ) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (run (fun w => w) W S K).2≤120*(S+1)*W := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun s : Fin (S+1) => (if s.val=0 then some (⟨⟨0,0⟩,[]⟩ : GeneralPaperRayAffineMinimum.Choice K) else none,32*W))
  change (run (fun w => w) W S K).2≤_ at hh
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hh
  have ho := GeneralPaperScoreDPBits.array_overhead S W hW hIndex
  nlinarith only [hh,ho]

theorem arithmetic_work (S K : ℕ) : (run (fun _ => 1) 1 S K).2≤120*(S+1) := by
  have hh := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1
    (fun s : Fin (S+1) => (if s.val=0 then some (⟨⟨0,0⟩,[]⟩ : GeneralPaperRayAffineMinimum.Choice K) else none,32*1))
  change (run (fun _ => 1) 1 S K).2=_ at hh
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hh
  have ho := GeneralPaperUnitArrayOverhead.score_overhead S
  nlinarith only [hh,ho]

end Blotto.GeneralPaperParametricInitialPrice
