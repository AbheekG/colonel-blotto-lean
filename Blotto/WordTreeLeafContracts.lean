import Blotto.WordMachineFallback
import Blotto.RationalMachineLaw

/-! Leaf predicates transfer through output maps and dependent continuations
without demanding a property at unreachable continuation inputs. -/

namespace Blotto.WordChoiceTree

theorem forLeaves_map_iff {α β : Type*} (T : WordChoiceTree α) (f : α → β) (P : β → Prop) :
    (T.map f).decode.ForLeaves P ↔ T.decode.ForLeaves (fun x => P (f x)) := by
  induction T with
  | leaf x => rfl
  | fork a b hb hab upper lower hu hl =>
    change ((_ ∧ _) ↔ (_ ∧ _))
    exact and_congr hu hl

theorem bind_forLeaves_of {α β : Type*} (T : WordChoiceTree α) (f : α → WordChoiceTree β)
    (P : α → Prop) (Q : β → Prop) (hT : T.decode.ForLeaves P)
    (hF : ∀ x, P x → (f x).decode.ForLeaves Q) : (T.bind f).decode.ForLeaves Q := by
  induction T with
  | leaf x => exact hF x hT
  | fork a b hb hab upper lower hu hl => exact ⟨hu hT.1, hl hT.2⟩

end Blotto.WordChoiceTree
