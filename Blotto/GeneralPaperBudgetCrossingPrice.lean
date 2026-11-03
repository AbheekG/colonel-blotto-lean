import Blotto.GeneralPaperNativeAffinePrices

/-! Price the final high-score budget-crossing batch, including guards,
stored-table reads, actual rational crossings and the score iterator. It
returns exactly the selected native batch and has only S+1 possible roots.
-/
namespace Blotto.GeneralPaperBudgetCrossingPrice
open GeneralPaperRayAffine GeneralPaperRayAffineScoreStep GeneralPaperRayAffineDPSize GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 4000000

def candidateRun {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (table : Table S K)
    (h : ℕ) (beta : ℚ) (s : Fin (S+1)) : Option ℚ × ℕ :=
  if h<s.val then
    match table.read s with
    | none => (none,16*W)
    | some c =>
      let root := GeneralPaperAffineCrossingPrice.run primitive W (GeneralPaperRayBudgetCrossings.constant beta) c.expression
      (root.1,root.2+16*W)
  else (none,16*W)

theorem candidate_data {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (table : Table S K)
    (h : ℕ) (beta : ℚ) (s : Fin (S+1)) :
    (candidateRun primitive W table h beta s).1=GeneralPaperRayBudgetCrossings.candidate table h beta s := by
  unfold candidateRun GeneralPaperRayBudgetCrossings.candidate
  split
  · cases table.read s <;> simp only [GeneralPaperAffineCrossingPrice.data]
  · rfl

def run {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (table : Table S K) (h : ℕ) (beta : ℚ) : List ℚ × ℕ :=
  let result := GeneralPaperPricedListStream.filterMap W (candidateRun primitive W table h beta) (List.finRange (S+1))
  (result.1,result.2+16*(S+2)*W)

theorem data {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (table : Table S K) (h : ℕ) (beta : ℚ) :
    (run primitive W table h beta).1=GeneralPaperRayBudgetCrossings.batch table h beta := by
  simp only [run,GeneralPaperPricedListStream.filterMap_data,candidate_data,GeneralPaperRayBudgetCrossings.batch]

def profile (S W P : ℕ) : ℕ := (S+1)*(88*W+9*P)+(16*(S+2)+2)*W

theorem work {S K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : Table S K) (hp : TableBounded D E X V n table) (h : ℕ) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) :
    (run primitive W table h beta).2≤profile S W (primitive (1+2*width D E m X V P)) := by
  have hTable := GeneralPaperNativeAffinePrices.table_cap D E m X V P n hn table hp
  have hP : P≤ interceptCap m X P := by
    unfold interceptCap
    nlinarith only [Nat.zero_le ((m+1)*X),Nat.zero_le (m*P)]
  have hConst : GeneralPaperRayAffineBound.Bounded D E (interceptCap m X P) (slopeCap m V)
      (GeneralPaperRayBudgetCrossings.constant beta) :=
    ⟨hb.mono hP,(GeneralPaperRayRationalBound.Bounded.zero E).mono (Nat.zero_le _)⟩
  have hEach (s : Fin (S+1)) : (candidateRun primitive W table h beta s).2≤
      80*W+9*primitive (1+2*width D E m X V P) := by
    unfold candidateRun
    split
    · cases he : table.read s with
      | none => dsimp only; omega
      | some c =>
        have hr := GeneralPaperAffineCrossingPrice.work primitive hMono W D E (interceptCap m X P)
          (slopeCap m V) (width D E m X V P) hD hE le_rfl
          (GeneralPaperRayBudgetCrossings.constant beta) c.expression hConst (hTable s c he)
        change (GeneralPaperAffineCrossingPrice.run primitive W (GeneralPaperRayBudgetCrossings.constant beta) c.expression).2+16*W≤_
        omega
    · omega
  have hh := GeneralPaperPricedListStream.filterMap_work W
    (80*W+9*primitive (1+2*width D E m X V P)) (candidateRun primitive W table h beta)
    (List.finRange (S+1)) (fun s _ => hEach s)
  simp only [List.length_finRange] at hh
  change _+16*(S+2)*W≤_
  unfold profile
  nlinarith only [hh]

theorem profile_bound (S W P : ℕ) : profile S W P≤128*(S+2)*(W+P) := by
  let slack := (24*S+134)*W+(119*S+247)*P
  have he : profile S W P+slack=128*(S+2)*(W+P) := by unfold profile; dsimp only [slack]; ring
  omega

end Blotto.GeneralPaperBudgetCrossingPrice
