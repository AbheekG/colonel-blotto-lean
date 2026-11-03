import Blotto.BinaryTerminalPacking
import Blotto.BinaryGroupInputs

/-! Computed terminal cached totals and pivot resource words form the original
uniform/mixed group input. Source group-count casts occur only in proofs;
probability is actual Boolean division, with no supplied group-input factory. -/

namespace Blotto.BinaryTerminalGroupInputs
open BinaryRationalNormalization BinaryRationalEncoding BinaryTerminalGrouping

def uniform {n : ℕ} (input : Input n) : BinaryGroupInputs.UniformInput (groups input).length :=
  ⟨input.budget,FixedArrayTable.ofFn (fun g => ((BinaryTerminalPacking.prepare input).read g).2)⟩

theorem uniform_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) : (uniform input).Canonical :=
  ⟨hC.1,fun g => by rw [uniform,FixedArrayTable.read_ofFn]; exact BinaryTerminalPacking.prepare_canonical input hC g⟩

def mixed {n : ℕ} (input : Input n) (pivot : Fin n) : BinaryGroupInputs.MixedInput (groups input).length :=
  ⟨input.budget,(uniform input).total,input.length.read pivot,
    BinaryRationalOpcode.apply .div (input.resource.read pivot) (input.length.read pivot)⟩

theorem mixed_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) (pivot : Fin n) : (mixed input pivot).Canonical :=
  ⟨hC.1,(uniform_canonical input hC).2,hC.2.1 pivot,
    BinaryReflectedFourSetup.opcode_canonical .div _ _ (hC.2.2 pivot) (hC.2.1 pivot)⟩

def castUniform {m k : ℕ} (he : m=k) (input : BinaryGroupInputs.UniformInput m) : BinaryGroupInputs.UniformInput k :=
  he ▸ input

def castMixed {m k : ℕ} (he : m=k) (input : BinaryGroupInputs.MixedInput m) : BinaryGroupInputs.MixedInput k :=
  he ▸ input

theorem castUniform_refines {m k : ℕ} (he : m=k) (input : BinaryGroupInputs.UniformInput m)
    (source : RationalUniformGroupSpec k) (hb : value input.budget=source.B)
    (ht : ∀ g : Fin m, value (input.total.read g)=source.length (g.cast he)) :
    (castUniform he input).Refines source := by
  cases he
  exact ⟨hb,ht⟩

theorem castMixed_refines {m k : ℕ} (he : m=k) (input : BinaryGroupInputs.MixedInput m)
    (source : RationalMixedGroupSpec k) (hb : value input.budget=source.B)
    (ht : ∀ g : Fin m, value (input.total.read g)=source.length (g.cast he))
    (hEll : value input.ell=source.ell) (hp : value input.probability=source.p) :
    (castMixed he input).Refines source := by
  cases he
  exact ⟨hb,ht,hEll,hp⟩

theorem uniform_refines {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) (hNone : source.pivot=none) :
    (castUniform (congrArg List.length (groups_refines input source hC hr)) (uniform input)).Refines
      (source.uniformSpec (source.pivot_none hNone)) := by
  apply castUniform_refines _ _ _ hr.1
  intro g
  rw [uniform,FixedArrayTable.read_ofFn]
  exact BinaryTerminalPacking.prepare_total input source hC hr g

theorem mixed_refines {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) (pivot : Fin n)
    (hPivot : source.pivot=some pivot) :
    (castMixed (congrArg List.length (groups_refines input source hC hr)) (mixed input pivot)).Refines
      (source.mixedSpec pivot (source.pivot_some hPivot)) := by
  apply castMixed_refines _ _ _ hr.1
  · intro g
    rw [mixed,uniform,FixedArrayTable.read_ofFn]
    exact BinaryTerminalPacking.prepare_total input source hC hr g
  · exact hr.2.1 pivot
  · change value (BinaryRationalOpcode.apply .div (input.resource.read pivot) (input.length.read pivot)) = source.resource pivot / source.length pivot
    rw [BinaryRationalOpcode.apply_value .div _ _ (hC.2.2 pivot).1 (hC.2.1 pivot).1,hr.2.2 pivot,hr.2.1 pivot]
    rfl

end Blotto.BinaryTerminalGroupInputs
