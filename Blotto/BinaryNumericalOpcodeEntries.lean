import Blotto.BinaryNormalizationPlan
import Blotto.BinaryPRGNumericalEntriesMeasured

/-! A reusable actual map forwards extra producer work while preserving the
whole old value/source record. Planned opcodes now produce the numerical ratio
and both arithmetic entry passes once, retaining every old entry and source
charge and forwarding actual division work plus reached planned emission. -/
namespace Blotto.BinaryNumericalOpcodeEntries
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition BinaryPRGPreparation
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 4000000

def map {α β E : Type*} [Zero E] [Add E] (produce : α → (β × ℕ) × E) : List α → (List β × ℕ) × E
  | [] => (([],2),0)
  | item::rest =>
      let first := produce item
      let later := map produce rest
      ((first.1.1::later.1.1,first.1.2+later.1.2+4),first.2+later.2)

theorem map_compat {α β E : Type*} [Zero E] [Add E] (produce : α → (β × ℕ) × E) (items : List α) :
    (map produce items).1 = BinaryLifetimeMapMeasured.map (fun item => (produce item).1) items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [map,BinaryLifetimeMapMeasured.map,ih]

theorem map_refines {α β E : Type*} [Zero E] [Add E] (produce : α → (β × ℕ) × E)
    (previous : α → β × ℕ) (h : ∀ item,(produce item).1 = previous item) (items : List α) :
    (map produce items).1 = BinaryLifetimeMapMeasured.map previous items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [map,BinaryLifetimeMapMeasured.map,h,ih]

theorem map_length {α β E : Type*} [Zero E] [Add E] (produce : α → (β × ℕ) × E) (items : List α) :
    (map produce items).1.1.length = items.length := by
  rw [map_compat,BinaryLifetimeMapMeasured.map_length]

def entryPayload {α : Type*} (entries : List (α × Trace)) : ℕ :=
  (BinaryLifetimeArray.mapDirect Prod.snd entries).flatten.length

theorem entryPayload_nil {α : Type*} : entryPayload ([] : List (α × Trace)) = 0 := rfl

theorem entryPayload_cons {α : Type*} (entry : α × Trace) (rest : List (α × Trace)) :
    entryPayload (entry::rest) = entry.2.length+entryPayload rest := by
  simp only [entryPayload,BinaryLifetimeArray.mapDirect,List.flatten_cons,List.length_append]

theorem map_price {α β : Type*} (produce : α → ((β × Trace) × ℕ) × ℕ) (items : List α)
    (h : ∀ item ∈ items,(produce item).2 ≤ 4*(produce item).1.2+25*(produce item).1.1.2.length+5) :
    (map produce items).2 ≤ 4*(map produce items).1.2+25*entryPayload (map produce items).1.1 := by
  induction items with
  | nil => simp [map,entryPayload]
  | cons item rest ih =>
      have ht := ih (fun next hn => h next (by simp [hn]))
      have hh := h item (by simp)
      simp only [map,entryPayload_cons]
      omega

def opcode (op : RealArithmeticOp) (first second : SignedWord) : ((SignedWord × Trace) × ℕ) × ℕ :=
  let produced := BinaryNormalizationPlan.apply op first second
  (produced.1.1,produced.1.2+produced.2)

theorem opcode_compat (op : RealArithmeticOp) (first second : SignedWord) :
    (opcode op first second).1 = BinaryQuadraticMeasured.apply op first second := by
  simp only [opcode,BinaryNormalizationPlan.apply_compat,BinaryQuadraticMeasured.apply]

theorem opcode_price (op : RealArithmeticOp) (first second : SignedWord) :
    (opcode op first second).2 ≤ 4*(opcode op first second).1.2+25*(opcode op first second).1.1.2.length+5 := by
  have hd := BinaryNormalizationPlan.apply_division op first second
  have he := BinaryNormalizationPlan.apply_price op first second
  simp only [opcode]
  omega

def prepare {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) : (BinaryPRGNumericalEntriesMeasured.Entries n × ℕ) × ℕ :=
  let ratioProduced := opcode .div input.b input.a
  let ratio := ratioProduced.1
  let lengthsProduced := map (opcode .mul two) rows
  let lengths := lengthsProduced.1
  let poorProduced := map (fun item => opcode .mul ratio.1.1 item.1) lengths.1
  let poor := poorProduced.1
  ((⟨ratio.1,lengths.1,poor.1,
      (by rw [map_length,hRows,List.length_ofFn]),
      (by rw [map_length,map_length,hRows,List.length_ofFn])⟩,
      ratio.2+lengths.2+poor.2+8),ratioProduced.2+lengthsProduced.2+poorProduced.2)

theorem prepare_compat {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    (prepare input rows hRows).1 = BinaryPRGNumericalEntriesMeasured.prepare input rows hRows := by
  have hRatio := opcode_compat .div input.b input.a
  have hLengths := map_refines (opcode .mul two) (BinaryQuadraticMeasured.apply .mul two)
    (fun word => opcode_compat .mul two word) rows
  have hPoor := map_refines
    (fun item : SignedWord × Trace => opcode .mul (BinaryQuadraticMeasured.apply .div input.b input.a).1.1 item.1)
    (fun item : SignedWord × Trace => BinaryQuadraticMeasured.apply .mul (BinaryQuadraticMeasured.apply .div input.b input.a).1.1 item.1)
    (fun item => opcode_compat .mul (BinaryQuadraticMeasured.apply .div input.b input.a).1.1 item.1)
    (BinaryLifetimeMapMeasured.map (BinaryQuadraticMeasured.apply .mul two) rows).1
  simp only [prepare,BinaryPRGNumericalEntriesMeasured.prepare,hRatio,hLengths,hPoor]

attribute [local irreducible] opcode map

theorem prepare_price {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    (prepare input rows hRows).2 ≤ 4*(prepare input rows hRows).1.2+
      25*((prepare input rows hRows).1.1.ratio.2.length+
        entryPayload (prepare input rows hRows).1.1.lengths+entryPayload (prepare input rows hRows).1.1.poor)+5 := by
  let ratio := opcode .div input.b input.a
  let lengths := map (opcode .mul two) rows
  have hr := opcode_price .div input.b input.a
  have hl := map_price (opcode .mul two) rows (fun word _ => opcode_price .mul two word)
  have hp := map_price (fun item => opcode .mul ratio.1.1.1 item.1) lengths.1.1
    (fun item _ => opcode_price .mul ratio.1.1.1 item.1)
  change ratio.2 ≤ 4*ratio.1.2+25*ratio.1.1.2.length+5 at hr
  change lengths.2 ≤ 4*lengths.1.2+25*entryPayload lengths.1.1 at hl
  simp only [prepare]
  change ratio.2+lengths.2+(map (fun item => opcode .mul ratio.1.1.1 item.1) lengths.1.1).2 ≤
    4*(ratio.1.2+lengths.1.2+(map (fun item => opcode .mul ratio.1.1.1 item.1) lengths.1.1).1.2+8)+
      25*(ratio.1.1.2.length+entryPayload lengths.1.1+
        entryPayload (map (fun item => opcode .mul ratio.1.1.1 item.1) lengths.1.1).1.1)+5
  omega

end Blotto.BinaryNumericalOpcodeEntries
