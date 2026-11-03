import Blotto.GeneralPaperHighBlockerPrice

/-! Shared one-pass high-search control for the actual unit/bit programs.
Concrete wrappers instantiate and prove the input/loop/final/recovery
contracts; these abstract callback premises alone do not complete a bound.
-/
namespace Blotto.GeneralPaperHighSearchPriceControl
open RationalOrderCell GeneralPaperRayAffineScoreStep
set_option autoImplicit false
set_option maxHeartbeats 4500000

abbrev Loop (S K : ℕ) := List (Field K) → ℚ → ℚ → Option (GeneralPaperRayParametricDP.Output S K) × ℕ
abbrev Finish (S K : ℕ) := Table S K → ℚ → ℚ → Option GeneralPaperRayCrossingRefinement.Bracket × ℕ
abbrev Recover (m S K : ℕ) := Table S K → ℚ → ℚ → Option (FixedArrayTable m (Fin K)) × ℕ

def run {m S K : ℕ} (W : ℕ) (inputs : Unit → List (Field K) × ℕ) (loop : Loop S K)
    (finish : Finish S K) (recover : Recover m S K) (lo hi : ℚ) : Option (GeneralPaperRayHighSearch.Answer m K) × ℕ :=
  let fields := inputs ()
  let stages := loop fields.1 lo hi
  match stages.1 with
  | none => (none,fields.2+stages.2+8*W)
  | some out =>
    let final := finish out.table out.bracket.lower out.bracket.upper
    match final.1 with
    | none => (none,fields.2+stages.2+final.2+16*W)
    | some b =>
      let row := recover out.table b.lower b.upper
      (row.1.map (fun labels => ⟨b.lower,labels⟩),fields.2+stages.2+final.2+row.2+24*W)

theorem data {m S K : ℕ} (W : ℕ) (inputs : Unit → List (Field K) × ℕ) (loop : Loop S K)
    (finish : Finish S K) (recover : Recover m S K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) (h : ℕ) (beta : ℚ)
    (hInputs : (inputs ()).1=GeneralPaperRayAffineScoreInput.fields matrix x w)
    (hLoop : ∀ fields lo hi,(loop fields lo hi).1=GeneralPaperRayParametricDP.run
      (GeneralPaperRayPricedPredicate.query matrix x w S h beta) S fields lo hi)
    (hFinish : ∀ table lo hi,(finish table lo hi).1=GeneralPaperRayFinalBudget.finish matrix table x w h beta lo hi)
    (hRecover : ∀ table lo hi,(recover table lo hi).1=GeneralPaperRayHighBlocker.extract m table h beta lo hi)
    (lo hi : ℚ) :
    (run W inputs loop finish recover lo hi).1=GeneralPaperRayHighSearch.prepared matrix S h beta x w lo hi := by
  unfold run GeneralPaperRayHighSearch.prepared
  simp only [hInputs,hLoop]
  cases GeneralPaperRayParametricDP.run (GeneralPaperRayPricedPredicate.query matrix x w S h beta) S
      (GeneralPaperRayAffineScoreInput.fields matrix x w) lo hi with
  | none => rfl
  | some out =>
    simp only [hFinish]
    cases GeneralPaperRayFinalBudget.finish matrix out.table x w h beta out.bracket.lower out.bracket.upper with
    | none => rfl
    | some b =>
      simp only [hRecover]
      cases GeneralPaperRayHighBlocker.extract m out.table h beta b.lower b.upper <;> rfl

def profile (I C F B W : ℕ) : ℕ := I+C+F+B+24*W

theorem work {m S K : ℕ} (W I C F B : ℕ) (inputs : Unit → List (Field K) × ℕ) (loop : Loop S K)
    (finish : Finish S K) (recover : Recover m S K) (lo hi : ℚ)
    (hInputs : (inputs ()).2≤I) (hLoop : (loop (inputs ()).1 lo hi).2≤C)
    (hFinish : ∀ out,(loop (inputs ()).1 lo hi).1=some out →
      (finish out.table out.bracket.lower out.bracket.upper).2≤F)
    (hRecover : ∀ out b,(loop (inputs ()).1 lo hi).1=some out →
      (finish out.table out.bracket.lower out.bracket.upper).1=some b →
        (recover out.table b.lower b.upper).2≤B) :
    (run W inputs loop finish recover lo hi).2≤profile I C F B W := by
  rw [run]
  cases hd : (loop (inputs ()).1 lo hi).1 with
  | none => dsimp only; unfold profile; omega
  | some out =>
    dsimp only
    have hf := hFinish out hd
    cases he : (finish out.table out.bracket.lower out.bracket.upper).1 with
    | none => dsimp only; unfold profile; omega
    | some b =>
      have hb := hRecover out b hd he
      dsimp only
      unfold profile
      omega

end Blotto.GeneralPaperHighSearchPriceControl
