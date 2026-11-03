import Blotto.BinaryGroupRouteEmissionWork

/-! Source route-array construction has an explicit conservative copy model:
each selected write may copy the complete old and new coefficient region.
Assignments, initialization and structural list/record visits are included.
The same original Euclidean division supplies every coefficient.  Addresses
and scalar field encodings retain their separate interpreter obligation. -/

namespace Blotto.BinaryPRGWordControllerRouteCopyWork
open BinaryRationalNormalization BinaryRationalEncoding
open scoped BigOperators

def words {m : ℕ} (route : BinaryGroupRoutes.Route m) : ℕ :=
  4 + BinaryRationalExpression.payloadWords route.2

def tableWords {n m : ℕ} (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) : ℕ :=
  ∑ j, words (table.read j)

theorem tableWords_bound {n m : ℕ} (table : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (P : ℕ) (h : ∀ j, words (table.read j) ≤ P) : tableWords table ≤ n * P := by
  unfold tableWords
  calc
    _ ≤ ∑ _j : Fin n, P := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

def patchWithWork {n m : ℕ} (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) :
    List (Fin n × BinaryGroupRoutes.Route m) → FixedArrayTable n (BinaryGroupRoutes.Route m) × ℕ
  | [] => (table, 1)
  | entry :: rest =>
      let next := table.write entry.1 entry.2
      let later := patchWithWork next rest
      (later.1, tableWords table + tableWords next + later.2 + 4)

theorem patchWithWork_erasure {n m : ℕ} (table : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (entries : List (Fin n × BinaryGroupRoutes.Route m)) :
    (patchWithWork table entries).1 = table.patch entries := by
  induction entries generalizing table with
  | nil => rfl
  | cons entry rest ih => exact ih (table.write entry.1 entry.2)

theorem patchWithWork_bound {n m : ℕ} (table : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (entries : List (Fin n × BinaryGroupRoutes.Route m)) (P : ℕ)
    (hTable : ∀ j, words (table.read j) ≤ P) (hEntries : ∀ entry ∈ entries, words entry.2 ≤ P) :
    (patchWithWork table entries).2 ≤ entries.length * (2 * n * P + 4) + 1 := by
  induction entries generalizing table with
  | nil => simp [patchWithWork]
  | cons entry rest ih =>
      have hFirst := hEntries entry (by simp)
      have hNext : ∀ j, words ((table.write entry.1 entry.2).read j) ≤ P := by
        intro j
        rw [FixedArrayTable.read_write]
        split
        · exact hFirst
        · exact hTable j
      have hLater := ih (table.write entry.1 entry.2) hNext (fun next hn => hEntries next (by simp [hn]))
      have hOldWords := tableWords_bound table P hTable
      have hNewWords := tableWords_bound (table.write entry.1 entry.2) P hNext
      unfold patchWithWork
      dsimp only
      simp only [List.length_cons]
      nlinarith

def prepareWithWork {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) : FixedArrayTable n (BinaryGroupRoutes.Route m) × ℕ :=
  let initial := FixedArrayTable.ofFn (fun _ => (none, BinaryRationalOpcode.zero))
  let entries := BinaryGroupRoutes.assignments length groups
  let result := patchWithWork initial entries
  (result.1, n * (n + 1) * words (m := m) (none, BinaryRationalOpcode.zero) + 2 * n +
    12 * entries.length + 4 * m + result.2 + 1)

theorem prepareWithWork_erasure {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) :
    (prepareWithWork length groups).1 = BinaryGroupRoutes.prepare length groups :=
  by
    unfold prepareWithWork BinaryGroupRoutes.prepare
    dsimp only
    rw [patchWithWork_erasure]

theorem assignments_length_bound {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord))
    (hMembers : ∀ g, (groups.read g).1.length ≤ n) :
    (BinaryGroupRoutes.assignments length groups).length ≤ m * n := by
  have hList : ∀ items : List (Fin m),
      (items.flatMap (fun g => (groups.read g).1.map (fun j =>
        (j,(some g, BinaryRationalOpcode.apply .div (length.read j) (groups.read g).2))))).length ≤ items.length * n := by
    intro items
    induction items with
    | nil => simp
    | cons g rest ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
        have hMember := hMembers g
        nlinarith
  exact (hList (List.finRange m)).trans_eq (by rw [List.length_finRange])

def bound (n m s : ℕ) : ℕ := n * (n + 1) * (7 + 8 * s) + 2 * n +
  12 * (m * n) + 4 * m + (m * n) * (2 * n * (7 + 8 * s) + 4) + 2

theorem prepareWithWork_bound {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord))
    (hL : ∀ j, CanonicalWord (length.read j)) (hT : ∀ g, CanonicalWord (groups.read g).2)
    (s : ℕ) (hLH : ∀ j, RationalHeight (value (length.read j)) s)
    (hTH : ∀ g, RationalHeight (value (groups.read g).2) s)
    (hMembers : ∀ g, (groups.read g).1.length ≤ n) :
    (prepareWithWork length groups).2 ≤ bound n m s := by
  have hInitial : ∀ j : Fin n, words ((FixedArrayTable.ofFn (fun _ : Fin n =>
      ((none, BinaryRationalOpcode.zero) : BinaryGroupRoutes.Route m))).read j) ≤ 7 + 8 * s := by
    intro j
    rw [FixedArrayTable.read_ofFn]
    change 6 ≤ 7 + 8 * s
    omega
  have hEntries : ∀ entry ∈ BinaryGroupRoutes.assignments length groups, words entry.2 ≤ 7 + 8 * s := by
    intro entry he
    obtain ⟨g,hg,he⟩ := List.mem_flatMap.mp he
    obtain ⟨j,hj,he⟩ := List.mem_map.mp he
    subst entry
    have hC := BinaryReflectedFourSetup.opcode_canonical .div (length.read j) (groups.read g).2 (hL j) (hT g)
    have hValue := BinaryRationalOpcode.apply_value .div (length.read j) (groups.read g).2 (hL j).1 (hT g).1
    have hHeight : RationalHeight (value (BinaryRationalOpcode.apply .div (length.read j) (groups.read g).2)) (s + s) := by
      rw [hValue]
      exact (hLH j).div (hTH g)
    have hWidth := hC.2.trans (rationalWordWidth_of_height hHeight)
    have hPayload := BinaryRationalExpression.payloadWords_bound _ (1 + 2 * (s + s)) hWidth
    unfold words
    dsimp only
    omega
  have hPatch := patchWithWork_bound
    (FixedArrayTable.ofFn (fun _ : Fin n => (none, BinaryRationalOpcode.zero)))
    (BinaryGroupRoutes.assignments length groups) (7 + 8 * s) hInitial hEntries
  have hLength := assignments_length_bound length groups hMembers
  unfold prepareWithWork bound
  dsimp only
  have hCopy := Nat.mul_le_mul_right (2 * n * (7 + 8 * s) + 4) hLength
  change n * (n + 1) * 6 + 2 * n + 12 * _ + 4 * m + _ + 1 ≤ _
  have hInitialWords := Nat.mul_le_mul_left (n * (n + 1)) (by omega : 6 ≤ 7 + 8 * s)
  omega

end Blotto.BinaryPRGWordControllerRouteCopyWork
