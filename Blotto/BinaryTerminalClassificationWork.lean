import Blotto.BinaryPRGTerminalWork

/-! One original-order scan computes uniform members and the first fractional
field from three cached Boolean comparisons per coordinate. It has exactly the
retained two-filter classification, including zero resources. Its arithmetic
price is derived from the actual reached resource lattice. Logical reads,
control/list/address and physical storage costs remain separate. -/

namespace Blotto.BinaryTerminalClassificationWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryPRGResourceWork BinaryPRGTerminalWork

structure Classified (n : ℕ) where
  uniforms : List (Fin n)
  pivot : Option (Fin n)
  booleanWork : ℕ

def classifyAux {n : ℕ} (input : BinaryTerminalGrouping.Input n) : List (Fin n) → Classified n
  | [] => ⟨[], none, 0⟩
  | j :: rest =>
      let resource := input.resource.read j
      let length := input.length.read j
      let upward := BinaryRationalArithmetic.lessEqual resource length
      let downward := BinaryRationalArithmetic.lessEqual length resource
      let nonpositive := BinaryRationalArithmetic.lessEqual resource zero
      let later := classifyAux input rest
      ⟨if upward && downward then j :: later.uniforms else later.uniforms,
        if (!nonpositive) && (!downward) then some j else later.pivot,
        BinaryRationalArithmetic.lessEqualWork resource length +
          BinaryRationalArithmetic.lessEqualWork length resource +
          BinaryRationalArithmetic.lessEqualWork resource zero + later.booleanWork⟩

def classify {n : ℕ} (input : BinaryTerminalGrouping.Input n) : Classified n :=
  classifyAux input (List.finRange n)

theorem classifyAux_uniforms {n : ℕ} (input : BinaryTerminalGrouping.Input n) (items : List (Fin n)) :
    (classifyAux input items).uniforms = items.filter (BinaryTerminalGrouping.uniform input) := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
      simp only [classifyAux, BinaryTerminalGrouping.uniform, List.filter_cons, ih]
      rfl

theorem classifyAux_pivot {n : ℕ} (input : BinaryTerminalGrouping.Input n) (items : List (Fin n)) :
    (classifyAux input items).pivot = (items.filter (BinaryResourceState.fractional input.length input.resource)).head? := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
      simp only [classifyAux, BinaryResourceState.fractional, List.filter_cons]
      by_cases h : ((!BinaryRationalArithmetic.lessEqual (input.resource.read j) zero) &&
          (!BinaryRationalArithmetic.lessEqual (input.length.read j) (input.resource.read j))) = true
      · simp [h]
      · simp [h, ih]

theorem classify_state {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (classify input).uniforms = BinaryTerminalGrouping.uniformItems input ∧
      (classify input).pivot = BinaryTerminalGrouping.pivot input :=
  ⟨classifyAux_uniforms input _, classifyAux_pivot input _⟩

theorem comparison_uniform_bound (first second : SignedWord) (W : ℕ)
    (hA : width first ≤ W) (hB : width second ≤ W) :
    BinaryRationalArithmetic.lessEqualWork first second ≤ 500 * (W + 1) ^ 2 :=
  (BinaryRationalArithmetic.lessEqualWork_bound first second).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hA hB) 1) 2))

theorem classifyAux_boolean_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) (W : ℕ) (hW : 1 ≤ W)
    (hL : ∀ j, width (input.length.read j) ≤ W) (hR : ∀ j, width (input.resource.read j) ≤ W)
    (items : List (Fin n)) :
    (classifyAux input items).booleanWork ≤ items.length * (1500 * (W + 1) ^ 2) := by
  induction items with
  | nil => simp [classifyAux]
  | cons j rest ih =>
      have ha := comparison_uniform_bound _ _ W (hR j) (hL j)
      have hb := comparison_uniform_bound _ _ W (hL j) (hR j)
      have hz : width zero ≤ W := by change 1 ≤ W; exact hW
      have hc := comparison_uniform_bound _ _ W (hR j) hz
      unfold classifyAux
      dsimp only
      simp only [List.length_cons]
      nlinarith

theorem reached_classification_boolean_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) :
    (classify (terminalInput request rich state)).booleanWork ≤
      6000 * n * (request.source.originalInputWordWidth + 2) ^ 2 := by
  have hw : 1 ≤ 1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator := by omega
  have hp := classifyAux_boolean_bound (terminalInput request rich state)
    (1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator) hw
    (terminal_length_width request rich state) (terminal_resource_width request rich N bits state h) (List.finRange n)
  simp only [List.length_finRange] at hp
  have hd := request.source.normalized_lattice_wordWidth_original
  have hb : 1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator + 1 ≤
      2 * (request.source.originalInputWordWidth + 2) := by omega
  have hBound := hp.trans (Nat.mul_le_mul_left n
    (Nat.mul_le_mul_left 1500 (Nat.pow_le_pow_left hb 2)))
  exact hBound.trans_eq (by ring)

def classifyAndPack {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    Classified n × (List (List (Fin n) × SignedWord) × ℕ) :=
  let scanned := classify input
  (scanned, BinaryGreedyPackingWork.pack input.length.read input.budget scanned.uniforms)

theorem classifyAndPack_state {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (classifyAndPack input).1.pivot = BinaryTerminalGrouping.pivot input ∧
      (classifyAndPack input).2.1 = BinaryTerminalGrouping.packed input := by
  unfold classifyAndPack
  dsimp only
  refine ⟨(classify_state input).2, ?_⟩
  rw [(classify_state input).1, BinaryGreedyPackingWork.pack_state]
  rfl

theorem reached_classifyAndPack_boolean_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) :
    (classifyAndPack (terminalInput request rich state)).1.booleanWork +
      (classifyAndPack (terminalInput request rich state)).2.2 ≤
        166000 * n * (request.source.originalInputWordWidth + 2) ^ 3 := by
  have hClass := reached_classification_boolean_bound request rich N bits state h
  have hPack := packing_boolean_bound request rich state
  unfold classifyAndPack
  dsimp only
  rw [(classify_state (terminalInput request rich state)).1]
  change (classify (terminalInput request rich state)).booleanWork + (packingWork request rich state).2 ≤ _
  have hPower : (request.source.originalInputWordWidth + 2) ^ 2 ≤
      (request.source.originalInputWordWidth + 2) ^ 3 := by
    have hn : 1 ≤ request.source.originalInputWordWidth + 2 := by omega
    exact Nat.pow_le_pow_right hn (by omega : 2 ≤ 3)
  have hc := hClass.trans (Nat.mul_le_mul_left (6000 * n) hPower)
  have hp := hPack.trans (Nat.mul_le_mul_right ((request.source.originalInputWordWidth + 2) ^ 3)
    (Nat.mul_le_mul_left 160000 (Nat.sub_le n 1)))
  nlinarith

end Blotto.BinaryTerminalClassificationWork
