import Blotto.GeneralPaperWordEncodingLifetime

/-! Count-word rows are encoded once from the stored count array. Recursive
activations retain their encoded head, child rows and price records. The
sum reserve covers descent/unwind without expanding the categorical range. -/
namespace Blotto.GeneralPaperBooleanRowsLifetime
open GeneralPaperEncodedScalarStorage (natBits fields listFootprint)
open GeneralPaperStoredBooleanCache (rows)
open GeneralPaperEqualRetainedStorage (wordFoot wordProfile word_bound)
set_option autoImplicit false
set_option maxHeartbeats 2000000

def entryFoot {c width : ℕ} (A : ℕ) (row : Fin c × FixedBinaryWord width) : ℕ :=
  natBits row.1.val + wordFoot A row.2 + 32 * A

def entryProfile (A c width : ℕ) : ℕ := 1 + binaryWordWidth c + wordProfile A width + 32 * A

def listProfile (A c width length : ℕ) : ℕ := length * (entryProfile A c width + 2 * A) + 32 * A

theorem payload {c width : ℕ} (A : ℕ) (items : List (Fin c × FixedBinaryWord width)) (length : ℕ) (h : items.length ≤ length) :
    listFootprint A (entryFoot A) items ≤ listProfile A c width length := by
  have hList := GeneralPaperEncodedScalarStorage.list_bound A (entryProfile A c width) (entryFoot A) items (by
    intro row _
    have hLabel := binaryWordWidth_mono row.1.isLt.le
    have hWord := word_bound A row.2
    unfold entryFoot entryProfile natBits
    omega)
  exact hList.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _)

def time (model : RationalCostModel) (A c width L : ℕ) : ℕ :=
  c * GeneralPaperStoredBooleanCache.rowBound model A c width L + 32 * A + 32

def localFoot {c : ℕ} (counts : FixedArrayTable c ℕ) (model : RationalCostModel) (A width : ℕ)
    (i : Fin c) (rest : List (Fin c)) : ℕ :=
  let encoded := GeneralPaperStoredWordEncoding.word model A width (counts.read i)
  let child := rows counts model A width rest
  let actual := rows counts model A width (i :: rest)
  natBits i.val + GeneralPaperWordEncodingLifetime.window model A width (counts.read i) + wordFoot A encoded.1 +
    fields A [i.val, encoded.2, child.2, actual.2] + 128 * A

def localProfile (model : RationalCostModel) (A c width L : ℕ) : ℕ :=
  1 + binaryWordWidth c + GeneralPaperWordEncodingLifetime.windowProfile model A width L + wordProfile A width +
    4 * (natBits (c + time model A c width L + 1) + A) + 160 * A

theorem local_bound {c : ℕ} (counts : FixedArrayTable c ℕ) (model : RationalCostModel) (A width L : ℕ)
    (h : ∀ i, binaryWordWidth (counts.read i) ≤ L) (i : Fin c) (rest : List (Fin c)) (hl : (i :: rest).length ≤ c) :
    localFoot counts model A width i rest ≤ localProfile model A c width L := by
  let encoded := GeneralPaperStoredWordEncoding.word model A width (counts.read i)
  let child := rows counts model A width rest
  let actual := rows counts model A width (i :: rest)
  have hWord := GeneralPaperWordEncodingLifetime.word_bound model A width (counts.read i) L (h i)
  have hPayload := word_bound A encoded.1
  have hLabel : natBits i.val ≤ 1 + binaryWordWidth c := Nat.add_le_add_left (binaryWordWidth_mono i.isLt.le) 1
  have hWork : actual.2 ≤ time model A c width L :=
    (GeneralPaperStoredBooleanCache.rows_work counts model A width L h (i :: rest)).trans
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) _) _)
  have hTotal : actual.2 = encoded.2 + child.2 + 64 * (A + binaryWordWidth (i.val + 1) + 1) := rfl
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (c + time model A c width L + 1)
    [i.val, encoded.2, child.2, actual.2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 4 * (natBits (c + time model A c width L + 1) + A) + 32 * A at hFields
  change natBits i.val + GeneralPaperWordEncodingLifetime.window model A width (counts.read i) + wordFoot A encoded.1 +
    fields A [i.val, encoded.2, child.2, actual.2] + 128 * A ≤ _
  unfold localProfile
  omega

def live {c : ℕ} (counts : FixedArrayTable c ℕ) (model : RationalCostModel) (A width : ℕ) : List (Fin c) → ℕ
  | [] => fields A [(rows counts model A width []).2] + 64 * A
  | i :: rest => localFoot counts model A width i rest +
      listFootprint A (entryFoot A) (rows counts model A width (i :: rest)).1 + live counts model A width rest

def profile (model : RationalCostModel) (A c width L : ℕ) : ℕ :=
  (c + 1) * (localProfile model A c width L + listProfile A c width c + 64 * A)

theorem bounded {c : ℕ} (counts : FixedArrayTable c ℕ) (model : RationalCostModel) (A width L : ℕ)
    (h : ∀ i, binaryWordWidth (counts.read i) ≤ L) (items : List (Fin c)) (hl : items.length ≤ c) :
    live counts model A width items ≤ (items.length + 1) *
      (localProfile model A c width L + listProfile A c width c + 64 * A) := by
  induction items with
  | nil =>
    have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (c + time model A c width L + 1)
      [32 * A + 32] (by intro x hx; rw [List.mem_singleton.mp hx]; unfold time; omega)
    simp only [List.length_singleton, one_mul] at hFields
    simp only [live, rows, List.length_nil, Nat.zero_add, one_mul]
    unfold localProfile
    omega
  | cons i rest ih =>
    have hLocal := local_bound counts model A width L h i rest hl
    have hPayload := payload A (rows counts model A width (i :: rest)).1 c (by
      rw [GeneralPaperStoredBooleanCache.rows_data, List.length_map]; exact hl)
    have hChild := ih (by simp only [List.length_cons] at hl; omega)
    simp only [live, List.length_cons]
    nlinarith only [hLocal, hPayload, hChild]

theorem all_rows {c : ℕ} (counts : FixedArrayTable c ℕ) (model : RationalCostModel) (A width L : ℕ)
    (h : ∀ i, binaryWordWidth (counts.read i) ≤ L) :
    live counts model A width (GeneralPaperEqualRouteConstruction.indices counts.data.size counts.size) ≤ profile model A c width L := by
  have hIds : (GeneralPaperEqualRouteConstruction.indices counts.data.size counts.size).length = c := by
    rw [GeneralPaperEqualRouteConstruction.indices_eq, List.length_finRange]
  have hLive := bounded counts model A width L h _ hIds.le
  rw [hIds] at hLive
  exact hLive

end Blotto.GeneralPaperBooleanRowsLifetime
