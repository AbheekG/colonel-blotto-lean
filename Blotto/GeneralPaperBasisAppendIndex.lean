import Blotto.GeneralPaperBasisIntegerUpdate

/-! Executable last-coordinate indexing for a growing basis. Old entries
keep their first-j positions; the new row/column occupies position j.
-/
namespace Blotto.GeneralPaperBasisAppendIndex
set_option autoImplicit false

def decode (n : ℕ) (j : Fin (n+1)) : Option (Fin n) :=
  if h : j.val<n then some ⟨j.val,h⟩ else none

def encode (n : ℕ) : Option (Fin n) → Fin (n+1)
  | none => ⟨n,by omega⟩
  | some j => j.castSucc

theorem decode_encode (n : ℕ) (j : Option (Fin n)) : decode n (encode n j)=j := by
  cases j with
  | none => simp [decode,encode]
  | some j =>
    change (if h : j.val<n then some ⟨j.val,h⟩ else none)=some j
    rw [dite_eq_left j.isLt]

theorem encode_decode (n : ℕ) (j : Fin (n+1)) : encode n (decode n j)=j := by
  unfold decode
  split
  · apply Fin.ext
    rfl
  · apply Fin.ext
    change n=j.val
    have hj := j.isLt
    omega

def equivalence (n : ℕ) : Fin (n+1) ≃ Option (Fin n) :=
  ⟨decode n,encode n,encode_decode n,decode_encode n⟩

theorem old (n : ℕ) (j : Fin n) : decode n j.castSucc=some j := decode_encode n (some j)

theorem last (n : ℕ) : decode n ⟨n,by omega⟩=none := decode_encode n none

theorem determinant_reindex (n : ℕ) (M : Matrix (Option (Fin n)) (Option (Fin n)) ℤ) :
    (M.submatrix (decode n) (decode n)).det=M.det := Matrix.det_submatrix_equiv_self (equivalence n) M

theorem adjugate_reindex (n : ℕ) (M : Matrix (Option (Fin n)) (Option (Fin n)) ℤ) :
    (M.submatrix (decode n) (decode n)).adjugate=M.adjugate.submatrix (decode n) (decode n) :=
  Matrix.adjugate_submatrix_equiv_self (equivalence n) M

end Blotto.GeneralPaperBasisAppendIndex
