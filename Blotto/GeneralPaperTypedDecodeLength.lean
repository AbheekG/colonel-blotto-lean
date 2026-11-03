import Blotto.GeneralPaperRootSelectPrice

/-! Any successful decode of a typed retained computation has exactly one
option per padded leaf. This also covers computations with missing states;
no DP soundness or separate validation pass is required for the length. -/
namespace Blotto.GeneralPaperTypedDecodeLength
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem node {K J h : ℕ} (left right : Computation Tag K J h)
    (states : GeneralPaperOrderedProfitScatter.Table Tag (Fin J × Fin J) J) (label : Fin J)
    (chosen : GeneralPaperOrderedMinimum.Selection Tag (Fin J × Fin J)) (hs : states.read label=some chosen) :
    decode (.node left right states) label=
      (decode left chosen.predecessor.1).bind (fun ll =>
        (decode right chosen.predecessor.2).bind (fun rr => some (ll++rr))) := by
  rw [decode,hs]
  rfl

theorem length {K J h : ℕ} (computed : Computation Tag K J h) (label : Fin J) (labels : List (Fin K))
    (hd : decode computed label=some labels) : labels.length=2^h := by
  induction computed generalizing label labels with
  | leaf states =>
    cases hs : states.read label with
    | none => simp only [decode,hs,Option.map_none] at hd; cases hd
    | some chosen =>
      have he : [chosen.predecessor]=labels := by simpa only [decode,hs,Option.map_some,Option.some.injEq] using hd
      rw [←he]
      rfl
  | @node h left right states ihl ihr =>
    cases hs : states.read label with
    | none => simp only [decode,hs] at hd; cases hd
    | some chosen =>
      rw [node left right states label chosen hs] at hd
      cases hl : decode left chosen.predecessor.1 with
      | none => simp only [hl,Option.bind_none] at hd; cases hd
      | some ll =>
        cases hr : decode right chosen.predecessor.2 with
        | none => simp only [hl,hr,Option.bind_some] at hd; cases hd
        | some rr =>
          have he : ll++rr=labels := by simpa only [hl,hr,Option.bind_some,Option.some.injEq] using hd
          rw [←he,List.length_append,ihl _ _ hl,ihr _ _ hr,pow_succ]
          omega

end Blotto.GeneralPaperTypedDecodeLength
