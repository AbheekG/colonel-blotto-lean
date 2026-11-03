import Blotto.GeneralPaperParametricInitialPrice

/-! Shared recursive control for the two actual priced parametric programs.
It constructs the initial table once and executes each later stage once.
The abstract callback prices here are discharged by the native arithmetic
and bit stages in the concrete wrappers; this alone is not a compiler bound.
-/
namespace Blotto.GeneralPaperParametricRecursionPrice
open GeneralPaperRayAffineScoreStep GeneralPaperRayCrossingRefinement GeneralPaperRayParametricDP
set_option autoImplicit false
set_option maxHeartbeats 4500000

abbrev Stage (S K : ℕ) := Field K → Table S K → ℚ → ℚ → Option (Bracket × Table S K) × ℕ

def run {S K : ℕ} (W : ℕ) (initial : Unit → Table S K × ℕ) (stage : Stage S K) :
    List (Field K) → ℚ → ℚ → Option (Output S K) × ℕ
  | [],lo,hi =>
    let current := initial ()
    (some ⟨⟨lo,hi⟩,current.1⟩,current.2+16*W)
  | field::rest,lo,hi =>
    let earlier := run W initial stage rest lo hi
    match earlier.1 with
    | none => (none,earlier.2+8*W)
    | some previous =>
      let current := stage field previous.table previous.bracket.lower previous.bracket.upper
      (current.1.map (fun out => ⟨out.1,out.2⟩),earlier.2+current.2+24*W)

theorem data {S K : ℕ} (query : ℚ → Bool × ℕ) (W : ℕ)
    (initial : Unit → Table S K × ℕ) (stage : Stage S K)
    (hInitial : (initial ()).1=GeneralPaperRayAffineScoreInput.initial S K)
    (hStage : ∀ field previous lo hi,(stage field previous lo hi).1=
      GeneralPaperRayParametricStage.stage query field previous lo hi)
    (fields : List (Field K)) (lo hi : ℚ) :
    (run W initial stage fields lo hi).1=GeneralPaperRayParametricDP.run query S fields lo hi := by
  induction fields with
  | nil => simp only [run,hInitial,GeneralPaperRayParametricDP.run]
  | cons field rest ih =>
    rw [run,GeneralPaperRayParametricDP.run,ih]
    cases GeneralPaperRayParametricDP.run query S rest lo hi with
    | none => rfl
    | some previous =>
      simp only [hStage]
      cases GeneralPaperRayParametricStage.stage query field previous.table previous.bracket.lower previous.bracket.upper <;> rfl

def profile (r W I C : ℕ) : ℕ := I+16*W+r*(C+24*W)

theorem work {S K : ℕ} (query : ℚ → Bool × ℕ) (W I C : ℕ)
    (initial : Unit → Table S K × ℕ) (stage : Stage S K)
    (hInitial : (initial ()).1=GeneralPaperRayAffineScoreInput.initial S K)
    (hStage : ∀ field previous lo hi,(stage field previous lo hi).1=
      GeneralPaperRayParametricStage.stage query field previous lo hi)
    (pool : List (Field K)) (lo hi : ℚ) (hInitialWork : (initial ()).2≤I)
    (hStageWork : ∀ field rest,(field::rest).Sublist pool → ∀ previous,
      GeneralPaperRayParametricDP.run query S rest lo hi=some previous →
        (stage field previous.table previous.bracket.lower previous.bracket.upper).2≤C)
    (fields : List (Field K)) (hSub : fields.Sublist pool) :
    (run W initial stage fields lo hi).2≤profile fields.length W I C := by
  induction fields with
  | nil =>
    change (initial ()).2+16*W≤_
    unfold profile
    simp only [List.length_nil,Nat.zero_mul,Nat.add_zero]
    omega
  | cons field rest ih =>
    have hRest : rest.Sublist pool := (List.Sublist.cons (a:=field) (List.Sublist.refl rest)).trans hSub
    have hPrevious := ih hRest
    rw [run]
    cases hp : (run W initial stage rest lo hi).1 with
    | none =>
      dsimp only
      unfold profile at hPrevious ⊢
      simp only [List.length_cons]
      nlinarith only [hPrevious,Nat.zero_le C]
    | some previous =>
      have hNative : GeneralPaperRayParametricDP.run query S rest lo hi=some previous := by
        rw [←data query W initial stage hInitial hStage]
        exact hp
      have hCurrent := hStageWork field rest hSub previous hNative
      dsimp only
      unfold profile at hPrevious ⊢
      simp only [List.length_cons]
      nlinarith only [hPrevious,hCurrent]

end Blotto.GeneralPaperParametricRecursionPrice
