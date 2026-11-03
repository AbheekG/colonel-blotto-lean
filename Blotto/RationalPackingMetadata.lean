import Blotto.RationalPackingLabels
import Blotto.IndexedLoopMetadataWork

/-! Packing control and label metadata follow the actual cached fit/reject
scan. Every closed group pays its reversal loop and member labels. Rational
payload work, physical addresses/allocator records/ownership remain separate. -/

namespace Blotto.RationalPackingMetadata

def labelWork (primitive : ℕ → ℕ) {n : ℕ} (j : Fin n) : ℕ :=
  4 * binaryWordWidth (j.val + 1) + 3 * primitive (binaryWordWidth (j.val + 1)) + 6

def labelBound (c n : ℕ) : ℕ := (4 + 3 * c) * binaryWordWidth (n + 4) + 6

theorem labelWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    {n : ℕ} (j : Fin n) : labelWork primitive j ≤ labelBound c n := by
  have hWidth := binaryWordWidth_mono (show j.val + 1 ≤ n + 4 by omega)
  have hp := (hPrimitive (binaryWordWidth (j.val + 1))).trans (Nat.mul_le_mul_left c hWidth)
  unfold labelWork labelBound
  nlinarith

def reversalWork (primitive : ℕ → ℕ) {n : ℕ} (current : List (Fin n)) : ℕ :=
  (current.map (labelWork primitive)).sum + indexedLoopMetadataBitWork primitive 0 current.length

theorem reversalWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    {n : ℕ} (current : List (Fin n)) (hLength : current.length ≤ n) :
    reversalWork primitive current ≤ current.length * labelBound c n + indexedLoopMetadataBound c n := by
  have hLabels : (current.map (labelWork primitive)).sum ≤ current.length * labelBound c n := by
    calc
      _ ≤ (current.map (fun _ => labelBound c n)).sum := List.sum_le_sum (fun j _ => labelWork_bound primitive c hPrimitive j)
      _ = _ := by simp
  have hLoop := (indexedLoopMetadataBitWork_bound primitive c hPrimitive current.length).trans (indexedLoopMetadataBound_mono c hLength)
  exact Nat.add_le_add hLabels hLoop

def groupCellWork (primitive : ℕ → ℕ) (length : ℕ) : ℕ :=
  4 * binaryWordWidth (length + 1) + 2 * primitive (binaryWordWidth (length + 1)) + 4

def groupCellBound (c n : ℕ) : ℕ := (4 + 2 * c) * binaryWordWidth (n + 4) + 4

theorem groupCellWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (length n : ℕ) (hLength : length ≤ n) : groupCellWork primitive length ≤ groupCellBound c n := by
  have hWidth := binaryWordWidth_mono (show length + 1 ≤ n + 4 by omega)
  have hp := (hPrimitive (binaryWordWidth (length + 1))).trans (Nat.mul_le_mul_left c hWidth)
  unfold groupCellWork groupCellBound
  nlinarith

def bodyWork (primitive : ℕ → ℕ) {n : ℕ} (j : Fin n) (remaining : ℕ) : ℕ :=
  8 * binaryWordWidth (remaining + 1) + 4 * primitive (binaryWordWidth (remaining + 1)) + 8 +
    4 * binaryWordWidth (j.val + 1) + 2 * primitive (binaryWordWidth (j.val + 1)) + 6

def bodyBound (c n : ℕ) : ℕ := (12 + 6 * c) * binaryWordWidth (n + 4) + 14

theorem bodyWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    {n : ℕ} (j : Fin n) (remaining : ℕ) (hRemaining : remaining ≤ n) : bodyWork primitive j remaining ≤ bodyBound c n := by
  have hRest := binaryWordWidth_mono (show remaining + 1 ≤ n + 4 by omega)
  have hIndex := binaryWordWidth_mono (show j.val + 1 ≤ n + 4 by omega)
  have hRestPrice := (hPrimitive (binaryWordWidth (remaining + 1))).trans (Nat.mul_le_mul_left c hRest)
  have hIndexPrice := (hPrimitive (binaryWordWidth (j.val + 1))).trans (Nat.mul_le_mul_left c hIndex)
  unfold bodyWork bodyBound
  nlinarith

def scanWork (primitive : ℕ → ℕ) {n : ℕ} (L : Fin n → ℚ) (B : ℚ) : List (Fin n) → ℚ → List (Fin n) → ℕ
  | current, _, [] => reversalWork primitive current + groupCellWork primitive current.length
  | current, s, x :: rest =>
      let next := s + L x
      if next ≤ B then bodyWork primitive x (rest.length + 1) + scanWork primitive L B (x :: current) next rest
      else bodyWork primitive x (rest.length + 1) + reversalWork primitive current + groupCellWork primitive current.length +
        scanWork primitive L B [x] (L x) rest

theorem scanWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    {n : ℕ} (L : Fin n → ℚ) (B : ℚ) (current : List (Fin n)) (s : ℚ) (rest : List (Fin n))
    (hLength : current.length + rest.length ≤ n) :
    scanWork primitive L B current s rest ≤ rest.length * bodyBound c n +
      (current.length + rest.length) * labelBound c n +
        (rationalPackSumsAux L B current s rest).length * (indexedLoopMetadataBound c n + groupCellBound c n) := by
  induction rest generalizing current s with
  | nil =>
    have hRev := reversalWork_bound primitive c hPrimitive current (by simpa only [List.length_nil, Nat.add_zero] using hLength)
    have hCell := groupCellWork_bound primitive c hPrimitive current.length n (by simpa only [List.length_nil, Nat.add_zero] using hLength)
    simp only [scanWork, rationalPackSumsAux, List.length_nil, List.length_singleton, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.one_mul]
    omega
  | cons x rest ih =>
    have hRest : rest.length + 1 ≤ n := by simp only [List.length_cons] at hLength; omega
    have hBody := bodyWork_bound primitive c hPrimitive x (rest.length + 1) hRest
    rw [scanWork, rationalPackSumsAux]
    split_ifs with hFit
    · have hRec := ih (x :: current) (s + L x) (by simp only [List.length_cons] at hLength ⊢; omega)
      simp only [List.length_cons] at hRec ⊢
      nlinarith
    · have hRec := ih [x] (L x) (by simp only [List.length_cons, List.length_nil]; omega)
      have hCurrent : current.length ≤ n := by simp only [List.length_cons] at hLength; omega
      have hRev := reversalWork_bound primitive c hPrimitive current hCurrent
      have hCell := groupCellWork_bound primitive c hPrimitive current.length n hCurrent
      simp only [List.length_cons, List.length_nil] at hRec ⊢
      nlinarith

def packedWork (primitive : ℕ → ℕ) {n : ℕ} (L : Fin n → ℚ) (B : ℚ) : List (Fin n) → ℕ
  | [] => 0
  | x :: rest => labelWork primitive x + scanWork primitive L B [x] (L x) rest

def packedBound (c n : ℕ) : ℕ :=
  n * bodyBound c n + (n + 1) * labelBound c n + 3 * (indexedLoopMetadataBound c n + groupCellBound c n)

theorem packedBound_mono_fields (c : ℕ) : Monotone (packedBound c) := by
  intro a b hab
  have hWidth := binaryWordWidth_mono (Nat.add_le_add_right hab 4)
  have hBody : bodyBound c a ≤ bodyBound c b := by unfold bodyBound; gcongr
  have hLabel : labelBound c a ≤ labelBound c b := by unfold labelBound; gcongr
  have hCell : groupCellBound c a ≤ groupCellBound c b := by unfold groupCellBound; gcongr
  have hLoop := indexedLoopMetadataBound_mono c hab
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hab hBody)
    (Nat.mul_le_mul (Nat.add_le_add_right hab 1) hLabel))
    (Nat.mul_le_mul_left 3 (Nat.add_le_add hLoop hCell))

theorem packedWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    {n : ℕ} (L : Fin n → ℚ) (B : ℚ) (items : List (Fin n)) (hLength : items.length ≤ n)
    (hGroups : (rationalPackedGroups L B items).length ≤ 3) : packedWork primitive L B items ≤ packedBound c n := by
  cases items with
  | nil => exact Nat.zero_le _
  | cons x rest =>
    have hScan := scanWork_bound primitive c hPrimitive L B [x] (L x) rest
      (by simp only [List.length_cons, List.length_nil] at hLength ⊢; omega)
    have hLabel := labelWork_bound primitive c hPrimitive x
    have hRest : rest.length ≤ n := by simp only [List.length_cons] at hLength; omega
    have hMembers : 1 + rest.length ≤ n := by simp only [List.length_cons] at hLength; omega
    have hBody := Nat.mul_le_mul_right (bodyBound c n) hRest
    have hReversed := Nat.mul_le_mul_right (labelBound c n) hMembers
    change (rationalPackSumsAux L B [x] (L x) rest).length ≤ 3 at hGroups
    have hClosed := Nat.mul_le_mul_right (indexedLoopMetadataBound c n + groupCellBound c n) hGroups
    simp only [List.length_cons, List.length_nil] at hScan
    unfold packedWork packedBound
    nlinarith

end Blotto.RationalPackingMetadata

namespace Blotto.RationalTerminalLotto

theorem packingMetadataWork_bound {n : ℕ} (i : RationalTerminalLotto n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) :
    RationalPackingMetadata.packedWork primitive i.length i.B i.uniformItems ≤ RationalPackingMetadata.packedBound c n := by
  have hLength : i.uniformItems.length ≤ n := (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))
  have hGroups : (rationalPackedGroups i.length i.B i.uniformItems).length ≤ 3 := by
    have he := congrArg List.length (rationalPackedGroups_groups i.length i.B i.uniformItems)
    have hEq : (rationalPackedGroups i.length i.B i.uniformItems).length = i.groups.length := by
      simpa only [List.length_map, groups] using he
    rw [hEq]
    rcases i.groups_count with h | h <;> omega
  exact RationalPackingMetadata.packedWork_bound primitive c hPrimitive i.length i.B i.uniformItems hLength hGroups

end Blotto.RationalTerminalLotto
