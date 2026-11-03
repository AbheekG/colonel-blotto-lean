import Blotto.GeneralPaperUnitArrayOverhead

/-! The same affine step with unit rational and index primitives. This
checks real-RAM arithmetic without introducing operand-width charges.
-/
namespace Blotto.GeneralPaperAffineArithmeticStep
open GeneralPaperRayAffineScoreStep
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {S K : ℕ} (sample : ℚ) (field : Field K) (previous : Table S K) : Table S K × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun s =>
    GeneralPaperAffineMinimumPrice.scanRun (fun _ => 1) 1 sample
      (GeneralPaperAffineCandidatePrice.run (fun _ => 1) 1 field previous s) (List.finRange K))

theorem data {S K : ℕ} (sample : ℚ) (field : Field K) (previous : Table S K) :
    (run sample field previous).1=GeneralPaperRayAffineScoreStep.step sample field previous := by
  simp only [run,PaperIndexedArrayConstruction.run_data,GeneralPaperAffineMinimumPrice.scan_data,
    GeneralPaperAffineCandidatePrice.data,GeneralPaperRayAffineScoreStep.step]

theorem work {S K : ℕ} (D E A B R s : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)≤R)
    (sample : ℚ) (ht : RationalHeight sample s) (field : Field K) (previous : Table S K)
    (hf : ∀ l,GeneralPaperRayAffineBound.Bounded D E A B (field.read l).2)
    (hp : ∀ i,GeneralPaperAffineMinimumPrice.Bounded D E A B (previous.read i)) :
    (run sample field previous).2≤GeneralPaperAffineStepPrice.profile S K 1 1 := by
  have hEach (i : Fin (S+1)) :
      (GeneralPaperAffineMinimumPrice.scanRun (fun _ => 1) 1 sample
        (GeneralPaperAffineCandidatePrice.run (fun _ => 1) 1 field previous i) (List.finRange K)).2≤
          (140+13)*K+2 := by
    have hs := GeneralPaperAffineMinimumPrice.scan_work (fun _ => 1) (fun _ _ _ => le_rfl)
      1 D E (A+A) (B+B) R s (96+4) hD hE hR sample ht
      (GeneralPaperAffineCandidatePrice.run (fun _ => 1) 1 field previous i) (List.finRange K)
      (fun l _ => GeneralPaperAffineCandidatePrice.bounded (fun _ => 1) 1 D E A B field previous hf hp i l)
      (fun l _ => GeneralPaperAffineCandidatePrice.work (fun _ => 1) (fun _ _ _ => le_rfl)
        1 D E A B R hD hE hR field previous hf hp i l)
    simpa only [List.length_finRange] using hs
  have hSum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hEach i)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hSum
  have ha := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1
    (fun i => GeneralPaperAffineMinimumPrice.scanRun (fun _ => 1) 1 sample
      (GeneralPaperAffineCandidatePrice.run (fun _ => 1) 1 field previous i) (List.finRange K))
  change (run sample field previous).2=_ at ha
  rw [ha]
  unfold GeneralPaperAffineStepPrice.profile
  have ho := GeneralPaperUnitArrayOverhead.score_overhead S
  nlinarith only [hSum,ho]

end Blotto.GeneralPaperAffineArithmeticStep
