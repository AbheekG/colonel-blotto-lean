import Blotto.FixedArrayTable

/-! A scalar source stores only its Boolean tape. Its length proof is erased;
readers are derived for specifications and legacy adapters, not retained as
executable closure fields. Every finite reader still has its exact adapter. -/
namespace Blotto

structure BinaryScalarTape (K : ℕ) where
  bits : List Bool
  size : bits.length = K

namespace BinaryScalarTape

def read {K : ℕ} (tape : BinaryScalarTape K) (j : Fin K) : Bool :=
  tape.bits[j.val]'(by rw [tape.size]; exact j.isLt)

def ofFn {K : ℕ} (read : Fin K → Bool) : BinaryScalarTape K :=
  ⟨List.ofFn read,List.length_ofFn⟩

instance {K : ℕ} : Coe (Fin K → Bool) (BinaryScalarTape K) := ⟨ofFn⟩
instance {K : ℕ} : CoeFun (BinaryScalarTape K) (fun _ => Fin K → Bool) := ⟨BinaryScalarTape.read⟩

@[simp] theorem ofFn_read {K : ℕ} (reader : Fin K → Bool) : (ofFn reader).read = reader := by
  funext j
  simp only [read,ofFn,List.getElem_ofFn]

@[simp] theorem ofFn_bits {K : ℕ} (reader : Fin K → Bool) : (ofFn reader).bits = List.ofFn reader := rfl

@[simp] theorem length {K : ℕ} (tape : BinaryScalarTape K) : tape.bits.length = K := tape.size

theorem listOfFn_read {K : ℕ} (tape : BinaryScalarTape K) : List.ofFn tape.read = tape.bits := by
  cases tape with
  | mk bits hs =>
    subst K
    exact List.ofFn_getElem

theorem correct {K : ℕ} (tape : BinaryScalarTape K) : tape.bits = List.ofFn tape.read :=
  tape.listOfFn_read.symm

@[ext] theorem ext {K : ℕ} {first second : BinaryScalarTape K} (h : first.read = second.read) :
    first = second := by
  have hb : first.bits = second.bits := by rw [first.correct,second.correct,h]
  cases first
  cases second
  cases hb
  rfl

theorem ofFn_read_eq {K : ℕ} (tape : BinaryScalarTape K) : ofFn tape.read = tape :=
  ext (ofFn_read tape.read)

theorem reader_coverage {K : ℕ} (reader : Fin K → Bool) :
    ∃ tape : BinaryScalarTape K,tape.read = reader := ⟨ofFn reader,ofFn_read reader⟩

theorem read_eq_array {K : ℕ} (tape : BinaryScalarTape K) (table : FixedArrayTable K Bool)
    (h : tape.bits = table.data.toList) : tape.read = table.read := by
  funext j
  simp only [read,FixedArrayTable.read,h,Array.getElem_toList]

end BinaryScalarTape
end Blotto
