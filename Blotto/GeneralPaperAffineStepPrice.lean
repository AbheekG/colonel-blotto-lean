import Blotto.GeneralPaperAffineCandidatePrice

/-! Materialize one actual affine DP layer. Each score invokes its candidate
scan once; each candidate adds a shared predecessor, and every comparison
prices both affine evaluations. Unit and Rat interpretations share the data.
-/
namespace Blotto.GeneralPaperAffineStepPrice
open GeneralPaperRayAffine GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

def run {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (sample : ℚ) (field : Field K) (previous : Table S K) :
    Table S K × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (fun s =>
    GeneralPaperAffineMinimumPrice.scanRun primitive W sample
      (GeneralPaperAffineCandidatePrice.run primitive W field previous s) (List.finRange K))

theorem data {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (sample : ℚ) (field : Field K) (previous : Table S K) :
    (run primitive W sample field previous).1=GeneralPaperRayAffineScoreStep.step sample field previous := by
  simp only [run,PaperIndexedArrayConstruction.run_data,GeneralPaperAffineMinimumPrice.scan_data,
    GeneralPaperAffineCandidatePrice.data,GeneralPaperRayAffineScoreStep.step]

def profile (S K W P : ℕ) : ℕ := (S+1)*((140*W+13*P)*K+2*W)+88*(S+1)*W

theorem work {S K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E A B R s : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)≤R)
    (sample : ℚ) (ht : RationalHeight sample s) (field : Field K) (previous : Table S K)
    (hf : ∀ l,GeneralPaperRayAffineBound.Bounded D E A B (field.read l).2)
    (hp : ∀ i,GeneralPaperAffineMinimumPrice.Bounded D E A B (previous.read i))
    (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (run primitive W sample field previous).2≤profile S K W (primitive (1+2*(R+s+1))) := by
  let P := primitive (1+2*(R+s+1))
  have hPrimitive := hMono (show 1+2*R≤1+2*(R+s+1) by omega)
  have hEach (i : Fin (S+1)) :
      (GeneralPaperAffineMinimumPrice.scanRun primitive W sample
        (GeneralPaperAffineCandidatePrice.run primitive W field previous i) (List.finRange K)).2≤
          (140*W+13*P)*K+2*W := by
    have hc (l : Fin K) : (GeneralPaperAffineCandidatePrice.run primitive W field previous i l).2≤96*W+4*P := by
      have hh := GeneralPaperAffineCandidatePrice.work primitive hMono W D E A B R hD hE hR field previous hf hp i l
      omega
    have hs := GeneralPaperAffineMinimumPrice.scan_work primitive hMono W D E (A+A) (B+B) R s (96*W+4*P)
      hD hE hR sample ht (GeneralPaperAffineCandidatePrice.run primitive W field previous i) (List.finRange K)
      (fun l _ => GeneralPaperAffineCandidatePrice.bounded primitive W D E A B field previous hf hp i l) (fun l _ => hc l)
    simp only [List.length_finRange] at hs
    change _≤(96*W+4*P+44*W+9*P)*K+2*W at hs
    nlinarith only [hs]
  have hSum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hEach i)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hSum
  have ha := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun i => GeneralPaperAffineMinimumPrice.scanRun primitive W sample
      (GeneralPaperAffineCandidatePrice.run primitive W field previous i) (List.finRange K))
  change (run primitive W sample field previous).2≤_ at ha
  have ho := GeneralPaperScoreDPBits.array_overhead S W hW hIndex
  unfold profile
  exact ha.trans (Nat.add_le_add hSum ho)

end Blotto.GeneralPaperAffineStepPrice
