import Blotto.GeneralPaperCrossingBatchPrice

/-! Discharge candidate and pair-batch cost premises with the actual native
affine DP field and previous layer. Their processed-field invariant supplies
the original common-lattice caps; no candidate or crossing-cost oracle.
-/
namespace Blotto.GeneralPaperNativeAffinePrices
open GeneralPaperRayAffine GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep
open GeneralPaperRayAffineDPSize GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem field_cap {K : ℕ} (D E m X V P : ℕ) (hm : 1≤m) (field : Field K)
    (hf : FieldBounded D E X V field) :
    ∀ l,GeneralPaperRayAffineBound.Bounded D E (interceptCap m X P) (slopeCap m V) (field.read l).2 := by
  have hc := scale_caps m X V P 1 hm
  simp only [Nat.one_mul] at hc
  exact fun l => GeneralPaperRayAffineBound.mono (hf l) hc.1 hc.2

theorem table_cap {S K : ℕ} (D E m X V P n : ℕ) (hn : n≤m) (previous : Table S K)
    (hp : TableBounded D E X V n previous) :
    ∀ s,GeneralPaperAffineMinimumPrice.Bounded D E (interceptCap m X P) (slopeCap m V) (previous.read s) := by
  have hc := scale_caps m X V P n hn
  exact fun s chosen hh => GeneralPaperRayAffineBound.mono (hp s chosen hh).1 hc.1 hc.2

def expressionRun {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (field : Field K) (previous : Table S K)
    (s : Fin (S+1)) (l : Fin K) : Option Affine × ℕ :=
  let current := GeneralPaperAffineCandidatePrice.run primitive W field previous s l
  (current.1.map Choice.expression,current.2+8*W)

theorem expression_data {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (field : Field K) (previous : Table S K)
    (s : Fin (S+1)) (l : Fin K) :
    (expressionRun primitive W field previous s l).1=
      GeneralPaperRayStableMinimum.expressions (GeneralPaperRayAffineScoreStep.candidate field previous) s l := by
  simp only [expressionRun,GeneralPaperAffineCandidatePrice.data,GeneralPaperRayStableMinimum.expressions]

def crossingsRun {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (field : Field K) (previous : Table S K) : List ℚ × ℕ :=
  GeneralPaperCrossingBatchPrice.run primitive W (expressionRun primitive W field previous)

theorem crossings_data {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (field : Field K) (previous : Table S K) :
    (crossingsRun primitive W field previous).1=GeneralPaperRayAffineScoreStep.crossings field previous := by
  simp only [crossingsRun,GeneralPaperCrossingBatchPrice.data,expression_data,GeneralPaperRayAffineScoreStep.crossings]

def profile (S K W P : ℕ) : ℕ := GeneralPaperCrossingBatchPrice.profile S K W P (104*W+4*P)

theorem crossings_work {S K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : FieldBounded D E X V field)
    (hp : TableBounded D E X V n previous) :
    (crossingsRun primitive W field previous).2≤profile S K W (primitive (1+2*width D E m X V P)) := by
  have hField := field_cap D E m X V P (by omega) field hf
  have hPrevious := table_cap D E m X V P n (by omega) previous hp
  have hCaps := scale_caps m X V P (n+1) hn
  have hBound (s : Fin (S+1)) (l : Fin K) (f : Affine)
      (hh : (expressionRun primitive W field previous s l).1=some f) :
      GeneralPaperRayAffineBound.Bounded D E (interceptCap m X P) (slopeCap m V) f := by
    rw [expression_data] at hh
    obtain ⟨c,hc,he⟩ := Option.map_eq_some_iff.mp hh
    rw [←he]
    have hb := GeneralPaperRayAffineDPSize.candidate D E X V n field previous hf hp s l c hc
    exact GeneralPaperRayAffineBound.mono hb.1 hCaps.1 hCaps.2
  have hCost (s : Fin (S+1)) (l : Fin K) :
      (expressionRun primitive W field previous s l).2≤104*W+4*primitive (1+2*width D E m X V P) := by
    have hh := GeneralPaperAffineCandidatePrice.work primitive hMono W D E (interceptCap m X P)
      (slopeCap m V) (width D E m X V P) hD hE le_rfl field previous hField hPrevious s l
    change (GeneralPaperAffineCandidatePrice.run primitive W field previous s l).2+8*W≤_
    omega
  exact GeneralPaperCrossingBatchPrice.work primitive hMono W D E (interceptCap m X P)
    (slopeCap m V) (width D E m X V P) _ hD hE le_rfl _ hBound hCost

theorem profile_bound (S K W P : ℕ) : profile S K W P≤1024*(S+2)*(K+1)^2*(W+P) := by
  let slack := (704*S*K^2+1728*K^2+2022*S*K+4070*K+982*S+1988)*W+
    (1007*S*K^2+2031*K^2+2048*S*K+4096*K+1024*S+2048)*P
  have he : profile S K W P+slack=1024*(S+2)*(K+1)^2*(W+P) := by
    unfold profile GeneralPaperCrossingBatchPrice.profile GeneralPaperCrossingPairsPrice.profile
    dsimp only [slack]
    ring
  omega

theorem step_work {S K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (sample : ℚ) (ht : RationalHeight sample (2*width D E m X V P+3))
    (field : Field K) (previous : Table S K) (hf : FieldBounded D E X V field)
    (hp : TableBounded D E X V n previous) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (GeneralPaperAffineStepPrice.run primitive W sample field previous).2≤
      GeneralPaperAffineStepPrice.profile S K W (primitive (6*width D E m X V P+9)) := by
  have hh := GeneralPaperAffineStepPrice.work primitive hMono W D E (interceptCap m X P)
    (slopeCap m V) (width D E m X V P) (2*width D E m X V P+3) hD hE le_rfl sample ht field previous
    (field_cap D E m X V P (by omega) field hf) (table_cap D E m X V P n (by omega) previous hp) hW hIndex
  have he : 1+2*(width D E m X V P+(2*width D E m X V P+3)+1)=6*width D E m X V P+9 := by ring
  rw [he] at hh
  exact hh

end Blotto.GeneralPaperNativeAffinePrices
