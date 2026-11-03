import Blotto.GeneralPaperTypedDecodeLength

/-! Follow stored typed predecessor indices once. Only successful child
lists are concatenated, with a single priced left-reference traversal.
An unsuccessful child stops its branch, preserving native Option behavior. -/
namespace Blotto.GeneralPaperTypedDecodeExecution
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {K J : ℕ} (A : ℕ) : {h : ℕ} → Computation Tag K J h → Fin J → Option (List (Fin K)) × ℕ
  | _,.leaf states,label =>
    match states.read label with
    | none => (none,64*A)
    | some chosen => (some [chosen.predecessor],128*A)
  | _,.node left right states,label =>
    match states.read label with
    | none => (none,64*A)
    | some chosen =>
      let ll := run A left chosen.predecessor.1
      match ll.1 with
      | none => (none,ll.2+128*A)
      | some ls =>
        let rr := run A right chosen.predecessor.2
        match rr.1 with
        | none => (none,ll.2+rr.2+128*A)
        | some rs =>
          let appended := GeneralPaperPricedListAppend.run A ls rs
          (some appended.1,ll.2+rr.2+appended.2+128*A)

theorem data {K J h : ℕ} (A : ℕ) (computed : Computation Tag K J h) (label : Fin J) :
    (run A computed label).1=decode computed label := by
  induction computed generalizing label with
  | leaf states => cases hs : states.read label <;> simp only [run,decode,hs,Option.map_none,Option.map_some]
  | @node h left right states ihl ihr =>
    cases hs : states.read label with
    | none => simp only [run,decode,hs]
    | some chosen =>
      rw [GeneralPaperTypedDecodeLength.node left right states label chosen hs]
      simp only [run,hs,ihl]
      cases hl : decode left chosen.predecessor.1 with
      | none => simp only [Option.bind_none]
      | some ll =>
        simp only [ihr,Option.bind_some]
        cases hr : decode right chosen.predecessor.2 <;>
          simp only [Option.bind_some,Option.bind_none,GeneralPaperPricedListAppend.data]

theorem length {K J h : ℕ} (A : ℕ) (computed : Computation Tag K J h) (label : Fin J) (labels : List (Fin K))
    (hd : (run A computed label).1=some labels) : labels.length=2^h := by
  rw [data] at hd
  exact GeneralPaperTypedDecodeLength.length computed label labels hd

end Blotto.GeneralPaperTypedDecodeExecution
