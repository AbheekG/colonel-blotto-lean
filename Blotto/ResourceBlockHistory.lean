import Blotto.ImplicitLeafUpdateHistory
import Blotto.MonotoneResourceCuts

/-! Computed binary resource cuts drive the actual sparse rounded block history.
Monotonic decoding on valid codes derives the canonical opposing half-tie loss,
including zero ties and duplicate resource plateaus. The particular Farey
decoder and its arithmetic cost remain explicit later implementation work. -/

namespace Blotto
open scoped Classical
namespace ImplicitLeafCounts

def computedWeak {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (past : List (Fin a)) (x : Fin a) : ℤ :=
  (MonotoneResourceCuts.weak (caps (selected past x)) (decode (selected past x)) (opponent past x)).1

def computedStrict {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (past : List (Fin a)) (x : Fin a) : ℤ :=
  (MonotoneResourceCuts.strict (caps (selected past x)) (decode (selected past x)) (opponent past x)).1

def resourceLoss {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (past : List (Fin a)) (x : Fin a) (code : Fin (caps (selected past x) + 1)) : ℚ :=
  SparseMW.rationalShare (opponent past x) (decode (selected past x) code.val)

def resourceBlockHistory {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) : List (Fin a) → Fin m → List Block :=
  blockHistory caps selected (computedWeak caps decode selected opponent) (computedStrict caps decode selected opponent) eta theta

theorem computedCuts_order {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (past : List (Fin a)) (x : Fin a) :
    computedWeak caps decode selected opponent past x ≤ computedStrict caps decode selected opponent past x := by
  unfold computedWeak computedStrict
  exact_mod_cast MonotoneResourceCuts.cuts_order (caps (selected past x)) (decode (selected past x))
    (hm (selected past x)) (opponent past x)

theorem computedCuts_loss {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (past : List (Fin a)) (x : Fin a) (code : Fin (caps (selected past x) + 1)) :
    resourceLoss caps decode selected opponent past x code =
      cutLoss caps selected (computedWeak caps decode selected opponent) (computedStrict caps decode selected opponent) past x code :=
  (MonotoneResourceCuts.regionLoss_exact _ _ (hm _) _ code.val (by omega)).symm

theorem resourceLoss_unit {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ) :
    ∀ past x code, 0 ≤ resourceLoss caps decode selected opponent past x code ∧
      resourceLoss caps decode selected opponent past x code ≤ 1 :=
  fun _ _ _ => SparseMW.rationalShare_unit _ _

theorem resourceBlockHistory_partition {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (past : List (Fin a)) : ∀ field,
    Partition (caps field) (resourceBlockHistory caps decode selected opponent eta theta past field) :=
  blockHistory_partition caps selected _ _ eta theta past

theorem resourceBlockHistory_positive {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) : ∀ field,
    Positive (resourceBlockHistory caps decode selected opponent eta theta past field) :=
  blockHistory_positive caps selected _ _ eta theta heta htheta past

theorem resourceBlockHistory_refines {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (past : List (Fin a)) : ∀ field (code : Fin (caps field + 1)),
    labelMass (resourceBlockHistory caps decode selected opponent eta theta past field) code.val =
      SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1)
        selected (resourceLoss caps decode selected opponent) eta theta past field code :=
  blockHistory_refines_loss caps selected _ _ (resourceLoss caps decode selected opponent)
    (computedCuts_loss caps decode hm selected opponent) eta theta past

theorem resourceBlockHistory_length {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (past : List (Fin a)) : ∀ field,
    (resourceBlockHistory caps decode selected opponent eta theta past field).length ≤
      1 + 2 * SparseMW.fieldUpdateCount selected past field :=
  blockHistory_length caps selected _ _ eta theta past

theorem computedCuts_visits {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (past : List (Fin a)) (x : Fin a) :
    (MonotoneResourceCuts.weak (caps (selected past x)) (decode (selected past x)) (opponent past x)).2 +
      (MonotoneResourceCuts.strict (caps (selected past x)) (decode (selected past x)) (opponent past x)).2 ≤
        2 * binaryWordWidth (caps (selected past x) + 1) :=
  MonotoneResourceCuts.cuts_visits _ _ _

theorem resourceBlockHistory_leafGuide_length {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (field : Fin m) (hr : ∀ code ≤ caps field, 0 ≤ decode field code)
    (hzero : decode field 0 = 0) (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) :
    ((CumulativeGuideSorting.guideAtoms
      (leafAtoms (caps field) (resourceBlockHistory caps decode selected opponent eta theta past field)
        (fun code => decode field code.val)) (1 + delta)).length : ℝ) ≤
      1 + 2 * (Real.log ((caps field + 1 : ℕ) : ℝ) +
        (SparseMW.fieldUpdateCount selected past field : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ))) / (delta : ℝ) := by
  apply rounded_leafGuide_length_bound (sizes := fun field => caps field + 1) selected
    (resourceLoss caps decode selected opponent) eta theta heta htheta
    (resourceLoss_unit caps decode selected opponent) past field (caps field) rfl
    (resourceBlockHistory caps decode selected opponent eta theta past field)
    (resourceBlockHistory_partition caps decode selected opponent eta theta past field)
    (resourceBlockHistory_positive caps decode selected opponent eta theta heta htheta past field)
    (resourceBlockHistory_refines caps decode hm selected opponent eta theta past field)
    (fun code => decode field code.val) (fun code => hr code.val (by omega)) hzero delta hd hu

end ImplicitLeafCounts
end Blotto
