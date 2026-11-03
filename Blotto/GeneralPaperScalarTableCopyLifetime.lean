import Blotto.GeneralPaperReferenceArrayCopyLifetime

/-! Literal scalar-copy scratch and every cursor of the actual scalar-table
copy. Both source and destination payload sums use the same additive cap;
the maximum entry is reserved only for the currently active scalar copy. -/
namespace Blotto.GeneralPaperScalarTableCopyLifetime
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def scalarPrice (S D P : ℕ) : ℕ := P + 32 * (S + D + 1)

def scalarWindow {α : Type*} (S D : ℕ) (encode : α → ℕ) (x : α) : ℕ :=
  let actual := GeneralPaperReferenceCopy.scalar S D encode x
  encode actual.1 + fields S [S,D,actual.2] + 64 * (S + D + 1)

def scalarProfile (S D P : ℕ) : ℕ :=
  P + 3 * (natBits (scalarPrice S D P) + S) + 32 * S + 64 * (S + D + 1)

theorem scalar_bound {α : Type*} (S D P : ℕ) (encode : α → ℕ) (x : α)
    (h : encode x ≤ P) : scalarWindow S D encode x ≤ scalarProfile S D P := by
  have hWork : (GeneralPaperReferenceCopy.scalar S D encode x).2 ≤ scalarPrice S D P := by
    dsimp only [GeneralPaperReferenceCopy.scalar,scalarPrice]
    omega
  have hf := fields_bound S (natBits (scalarPrice S D P))
    [S,D,(GeneralPaperReferenceCopy.scalar S D encode x).2] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl
      all_goals dsimp only [scalarPrice] at *; omega)
  change fields S _ ≤ 3 * (natBits (scalarPrice S D P) + S) + 32 * S at hf
  dsimp only [scalarWindow,scalarProfile,GeneralPaperReferenceCopy.scalar] at *
  omega

def window {α : Type*} {n : ℕ} (S D : ℕ) (encode : α → ℕ) (source : FixedArrayTable n α)
    (k : ℕ) (hk : k ≤ n) : ℕ :=
  GeneralPaperReferenceArrayCopyLifetime.window S D encode encode
    (GeneralPaperReferenceCopy.scalar S D encode) source (fun j => scalarWindow S D encode (source.read j)) k hk

def profile (S D n B P : ℕ) : ℕ :=
  GeneralPaperReferenceArrayCopyLifetime.profile S D (B + n * S + 64 * S) B P n
    (scalarPrice S D P) (scalarProfile S D P)

theorem source_owner {α : Type*} {n : ℕ} (S B : ℕ) (encode : α → ℕ) (source : FixedArrayTable n α)
    (hB : (∑ j : Fin n,encode (source.read j)) ≤ B) :
    arrayFootprint S encode source ≤ B + n * S + 64 * S := by
  dsimp only [arrayFootprint]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

theorem all_cursors {α : Type*} {n : ℕ} (S D B P : ℕ) (encode : α → ℕ) (source : FixedArrayTable n α)
    (hB : (∑ j : Fin n,encode (source.read j)) ≤ B) (hP : ∀ j,encode (source.read j) ≤ P)
    (hD : 1 ≤ D) (hIndex : binaryWordWidth (n + 1) ≤ D) (k : ℕ) (hk : k ≤ n) :
    window S D encode source k hk ≤ profile S D n B P := by
  exact GeneralPaperReferenceArrayCopyLifetime.all_cursors S D _ B P (scalarPrice S D P)
    (scalarProfile S D P) encode encode (GeneralPaperReferenceCopy.scalar S D encode) source
    (fun j => scalarWindow S D encode (source.read j)) (source_owner S B encode source hB) hB hP
    (fun j => Nat.add_le_add_right (hP j) _) (fun j => scalar_bound S D P encode _ (hP j)) hD hIndex k hk

theorem source_data {α : Type*} {n : ℕ} (S D : ℕ) (encode : α → ℕ) (source : FixedArrayTable n α) :
    (PaperIndexedArrayConstruction.run id D
      (GeneralPaperReferenceArrayCopyLifetime.callback S (GeneralPaperReferenceCopy.scalar S D encode) source)).1 =
      (GeneralPaperScalarTableCopy.run S D encode source).1 := rfl

theorem source_work {α : Type*} {n : ℕ} (S D : ℕ) (encode : α → ℕ) (source : FixedArrayTable n α) :
    (GeneralPaperScalarTableCopy.run S D encode source).2 =
      (PaperIndexedArrayConstruction.run id D
        (GeneralPaperReferenceArrayCopyLifetime.callback S (GeneralPaperReferenceCopy.scalar S D encode) source)).2 +
        64 * (S + D + 1) := rfl

end Blotto.GeneralPaperScalarTableCopyLifetime
