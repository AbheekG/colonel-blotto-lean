import Blotto.BinaryCachedTerminalPreparation

/-! Cached group totals are actual input-lattice sums in the original budget
box. Route divisions and optional pivot division therefore have derived Boolean
arithmetic prices. The bound charges cached-member traversal conservatively;
index/control/table-copy, descriptors, sampling/emission/scaling and complete
physical storage/backend costs remain separate. -/

namespace Blotto.BinaryCachedTerminalWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryCachedTerminalPreparation BinaryPRGResourceWork BinaryPRGTerminalWork
open scoped BigOperators

theorem Prepared.packing_read {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (g : Fin prepared.count) :
    prepared.packing.read g = (BinaryTerminalPacking.prepare input).read (g.cast prepared.count_eq) := by
  rw [← prepared.packing_cast, castTable_read]

theorem Prepared.members_eq {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (g : Fin prepared.count) :
    (prepared.packing.read g).1 = (BinaryTerminalGrouping.groups input).get (g.cast prepared.count_eq) := by
  rw [Prepared.packing_read]
  exact BinaryTerminalPacking.prepare_members input _

theorem Prepared.total_canonical {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (g : Fin prepared.count) : CanonicalWord (prepared.packing.read g).2 := by
  rw [Prepared.packing_read]
  exact BinaryTerminalPacking.prepare_canonical input hC _

theorem Prepared.total_lattice {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (D : ℕ) (hL : ∀ j, OnRationalLattice D (value (input.length.read j)))
    (g : Fin prepared.count) : OnRationalLattice D (value (prepared.packing.read g).2) := by
  let old := (BinaryTerminalPacking.prepare input).read (g.cast prepared.count_eq)
  have hMem : old ∈ BinaryTerminalGrouping.packed input :=
    List.getElem_mem (by have hg := (g.cast prepared.count_eq).isLt; simpa [BinaryTerminalGrouping.groups] using hg)
  have hTotal := BinaryGreedyPacking.packedGroups_totals input.length.read input.budget hC.2.1 hC.1
    (BinaryTerminalGrouping.uniformItems input) old hMem
  rw [Prepared.packing_read]
  change OnRationalLattice D (value old.2)
  rw [hTotal]
  exact OnRationalLattice.list_sum _ _ (fun j _ => hL j)

theorem Prepared.total_box {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input) (g : Fin prepared.count) :
    0 < value (prepared.packing.read g).2 ∧ value (prepared.packing.read g).2 ≤ value input.budget := by
  obtain ⟨source, hr⟩ := hAd
  rw [Prepared.packing_read]
  have he := BinaryTerminalPacking.prepare_total input source hC hr (g.cast prepared.count_eq)
  rw [he, hr.1]
  exact ⟨source.partition.total_pos _, source.partition_total_le _⟩

theorem Prepared.members_length {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input) (g : Fin prepared.count) :
    (prepared.packing.read g).1.length ≤ n := by
  obtain ⟨source, hr⟩ := hAd
  have hNodup : (BinaryTerminalGrouping.groups input).flatten.Nodup := by
    rw [BinaryTerminalGrouping.groups_refines input source hC hr]
    exact source.groups_nodup
  have hMem : (prepared.packing.read g).1 ∈ BinaryTerminalGrouping.groups input := by
    rw [Prepared.members_eq]
    exact List.get_mem _ _
  have hn := (List.nodup_flatten.mp hNodup).1 _ hMem
  have hBound : (prepared.packing.read g).1.toFinset.card ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [List.toFinset_card_of_nodup hn] at hBound
  simpa using hBound

def routeArithmeticWork {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input) : ℕ :=
  ∑ g, (((prepared.packing.read g).1).map (fun j =>
    (applyWithWork .div (input.length.read j) (prepared.packing.read g).2).2)).sum

theorem routeArithmeticWork_uniform_bound {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input) (W : ℕ)
    (hL : ∀ j, width (input.length.read j) ≤ W) (hT : ∀ g, width (prepared.packing.read g).2 ≤ W) :
    routeArithmeticWork prepared ≤ 3 * n * (12000 * (W + 1) ^ 3) := by
  have hPoint : ∀ g,
      (((prepared.packing.read g).1).map (fun j =>
        (applyWithWork .div (input.length.read j) (prepared.packing.read g).2).2)).sum ≤
          n * (12000 * (W + 1) ^ 3) := by
    intro g
    have hPrice : ∀ j, (applyWithWork .div (input.length.read j) (prepared.packing.read g).2).2 ≤
        12000 * (W + 1) ^ 3 := fun j => BinaryPRGPreparationWork.operation_uniform_bound .div _ _ W (hL j) (hT g)
    have hSum : ∀ items : List (Fin n),
        (items.map (fun j => (applyWithWork .div (input.length.read j) (prepared.packing.read g).2).2)).sum ≤
          items.length * (12000 * (W + 1) ^ 3) := by
      intro items
      induction items with
      | nil => simp
      | cons j rest ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          exact (Nat.add_le_add (hPrice j) ih).trans_eq (by ring)
    exact (hSum _).trans (Nat.mul_le_mul_right _ (Prepared.members_length prepared hC hAd g))
  have hCount : prepared.count ≤ 3 := by rcases prepared.count_bound hC hAd with h | h <;> omega
  unfold routeArithmeticWork
  calc
    _ ≤ ∑ _g : Fin prepared.count, n * (12000 * (W + 1) ^ 3) := Finset.sum_le_sum (fun g _ => hPoint g)
    _ = prepared.count * (n * (12000 * (W + 1) ^ 3)) := by simp
    _ ≤ 3 * (n * (12000 * (W + 1) ^ 3)) := Nat.mul_le_mul_right _ hCount
    _ = _ := by ring

theorem reached_routeArithmeticWork_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) :
    routeArithmeticWork (prepare (terminalInput request rich state)) ≤
      288000 * n * (request.source.originalInputWordWidth + 2) ^ 3 := by
  let input := terminalInput request rich state
  let cached := prepare input
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  have hTotalWidth : ∀ g, width (cached.packing.read g).2 ≤
      1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator := by
    intro g
    have ht := Prepared.total_box cached hC hAd g
    have hLat := Prepared.total_lattice cached hC _ (fun j => (resource_lattice_boxes request rich).1 j) g
    exact (Prepared.total_canonical cached hC g).2.trans
      (rationalWordWidth_lattice_bound request.source.normalizedInput.latticeDenominator_pos hLat
        ⟨ht.1.le, ht.2.trans (budget_box request rich).2⟩)
  have hp := routeArithmeticWork_uniform_bound cached hC hAd _ (terminal_length_width request rich state) hTotalWidth
  have hd := request.source.normalized_lattice_wordWidth_original
  have hw : 1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator + 1 ≤
      2 * (request.source.originalInputWordWidth + 2) := by omega
  have hBound := hp.trans (Nat.mul_le_mul_left (3 * n)
    (Nat.mul_le_mul_left 12000 (Nat.pow_le_pow_left hw 3)))
  exact hBound.trans_eq (by ring)

def pivotArithmeticWork {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input) : ℕ :=
  match prepared.pivot with
  | none => 0
  | some j => (applyWithWork .div (input.resource.read j) (input.length.read j)).2

theorem reached_pivotArithmeticWork_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) :
    pivotArithmeticWork (prepare (terminalInput request rich state)) ≤
      96000 * (request.source.originalInputWordWidth + 2) ^ 3 := by
  unfold pivotArithmeticWork
  split
  · exact Nat.zero_le _
  · rename_i j hPivot
    have hp := BinaryPRGPreparationWork.operation_uniform_bound .div
      ((terminalInput request rich state).resource.read j) ((terminalInput request rich state).length.read j)
      (1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator)
      (terminal_resource_width request rich N bits state h j) (terminal_length_width request rich state j)
    have hd := request.source.normalized_lattice_wordWidth_original
    have hw : 1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator + 1 ≤
        2 * (request.source.originalInputWordWidth + 2) := by omega
    exact (hp.trans (Nat.mul_le_mul_left 12000 (Nat.pow_le_pow_left hw 3))).trans_eq (by ring)

def arithmeticWork {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input) : ℕ :=
  prepared.prefixWork + routeArithmeticWork prepared + pivotArithmeticWork prepared

theorem reached_arithmeticWork_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) :
    arithmeticWork (prepare (terminalInput request rich state)) ≤
      (454000 * n + 96000) * (request.source.originalInputWordWidth + 2) ^ 3 := by
  have hClass := BinaryTerminalClassificationWork.reached_classifyAndPack_boolean_bound request rich N bits state h
  have hRoute := reached_routeArithmeticWork_bound request rich N bits state h
  have hPivot := reached_pivotArithmeticWork_bound request rich N bits state h
  unfold arithmeticWork
  change (BinaryTerminalClassificationWork.classifyAndPack (terminalInput request rich state)).1.booleanWork +
    (BinaryTerminalClassificationWork.classifyAndPack (terminalInput request rich state)).2.2 +
      routeArithmeticWork (prepare (terminalInput request rich state)) + pivotArithmeticWork (prepare (terminalInput request rich state)) ≤ _
  exact (Nat.add_le_add (Nat.add_le_add hClass hRoute) hPivot).trans_eq (by ring)

end Blotto.BinaryCachedTerminalWork
