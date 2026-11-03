import Blotto.GeneralPaperPositiveSelectionLifetime

/-! A selected-label list lookup retains only traversal references and
indices. Probability copies own rational words; endpoint callbacks retain
row references, whose payload remains owned by the full descriptor. -/
namespace Blotto.GeneralPaperCompactionCallbackLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperPreparedPositiveLabels (Selection)
open GeneralPaperPreparedSegmentCompaction (readWork weightItem leftItem rightItem itemBound)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def lookupFoot {n r : ℕ} {l : RationalSegmentLottery n r} (A : ℕ) (chosen : Selection l) (i : Fin (count l)) : ℕ :=
  let frame := fields A [i.val, chosen.size, (chosen.read i).val] + 32 * A
  (i.val + 2) * frame + 64 * A

def lookupProfile (A r : ℕ) : ℕ := (r + 2) * (3 * (natBits (r + 1) + A) + 64 * A) + 64 * A

theorem lookup_bound {n r : ℕ} {l : RationalSegmentLottery n r} (A : ℕ) (chosen : Selection l) (i : Fin (count l)) :
    lookupFoot A chosen i ≤ lookupProfile A r := by
  have hSize := GeneralPaperPreparedPositiveLabels.size_le chosen
  have hCount : count l ≤ r := by rw [← GeneralPaperPreparedPositiveLabels.size_eq chosen]; exact hSize
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (r + 1)
    [i.val, chosen.size, (chosen.read i).val] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · omega
      · omega
      · exact (chosen.read i).isLt.le.trans (Nat.le_succ r))
  change fields A _ ≤ 3 * (natBits (r + 1) + A) + 32 * A at hFields
  have hScale := Nat.mul_le_mul (show i.val + 2 ≤ r + 2 by omega) (Nat.add_le_add_right hFields (32 * A))
  exact (Nat.add_le_add_right hScale (64 * A)).trans_eq (by unfold lookupProfile; ring)

def footprint {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (chosen : Selection l) (A : ℕ) (i : Fin (count l)) : ℕ :=
  lookupFoot A chosen i + 2 * rationalWordWidth (weightItem p chosen A i).1 +
    fields A [i.val, chosen.size, readWork A p.weights.data.size i.val,
      (weightItem p chosen A i).2, (leftItem p chosen A i).2, (rightItem p chosen A i).2] + 256 * A

def profile (A r s : ℕ) : ℕ :=
  lookupProfile A r + 2 * (1 + 2 * s) + 6 * (natBits (r + itemBound A r s + 1) + A) + 288 * A

theorem bounded {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (chosen : Selection l) (A : ℕ) (h : ∀ j, RationalHeight (l.weight j) s) (i : Fin (count l)) :
    footprint p chosen A i ≤ profile A r s := by
  have hLookup := lookup_bound A chosen i
  have hItems := GeneralPaperPreparedSegmentCompaction.item_work p chosen A h i
  have hWeight : rationalWordWidth (weightItem p chosen A i).1 ≤ 1 + 2 * s := by
    change rationalWordWidth (p.weights.read (chosen.read i)) ≤ _
    rw [p.weight_correct]
    exact rationalWordWidth_of_height (h _)
  have hSize := GeneralPaperPreparedPositiveLabels.size_le chosen
  have hCount : count l ≤ r := by rw [← GeneralPaperPreparedPositiveLabels.size_eq chosen]; exact hSize
  have hRead : readWork A p.weights.data.size i.val ≤ itemBound A r s := by
    have hh := hItems.2.1
    change readWork A p.weights.data.size i.val + 32 * A + 32 ≤ _ at hh
    omega
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (r + itemBound A r s + 1)
    [i.val, chosen.size, readWork A p.weights.data.size i.val,
      (weightItem p chosen A i).2, (leftItem p chosen A i).2, (rightItem p chosen A i).2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 6 * (natBits (r + itemBound A r s + 1) + A) + 32 * A at hFields
  unfold footprint profile
  omega

end Blotto.GeneralPaperCompactionCallbackLifetime
