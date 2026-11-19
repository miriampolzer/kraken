module

import Kraken.ForLean
public import Lean.ToExpr

@[expose] public section

/-
Common Kraken executable layout.
-/

namespace Kraken

abbrev Label := String
instance : Repr ByteArray where reprPrec _ _ := "<opaque byte array>"

deriving instance Lean.ToExpr for ByteArray

inductive Directive (Instr Const : Type) where
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (arr : ByteArray)
  /-- A data word of `bytes` bytes whose value is a symbolic constant, e.g. a label or a
  difference of labels (a relocation). It is never executed. Jump tables (`.long .Lcase - .Ltable`)
  and pointer tables (`.quad fn`) are the typical uses. -/
  | word (bytes : Nat) (e : Const)
  deriving DecidableEq, Repr, Hashable, BEq, Lean.ToExpr

structure Sized Directive where
  directive : Directive
  size : Nat

/-- `ds₁` is `ds₂` preceded by zero-size directives. -/
def ZeroSizePrefix {D : Type} (ds₁ ds₂ : List (Sized D)) : Prop :=
  ∃ pre, ds₁ = pre ++ ds₂ ∧ ∀ c ∈ pre, c.size = 0

@[simp] theorem ZeroSizePrefix.refl {D : Type} (ds : List (Sized D)) : ZeroSizePrefix ds ds :=
  ⟨[], rfl, by simp⟩

abbrev Program Instr Const := List (Directive Instr Const)

structure Executable (Instr Const : Type) where
  startAddr : Int64
  program : List (Sized (Directive Instr Const))

/-- A placement of a program in memory. `instrSize` is `Nat → Nat` because on X64 the same
instruction AST may be encoded with different byte lengths at different positions. -/
structure Layout where
  start : Int64
  instrSize : Nat → Nat
  instrSize_pos : ∀ i, 0 < instrSize i

variable {Instr Const : Type}

@[simp]
def Layout.size (l : Layout) (d : Directive Instr Const) (i : Nat) : Nat :=
  match d with
  | .instr _ => l.instrSize i
  | .label _ => 0
  | .byteArray arr => arr.size
  | .word bytes _ => bytes

def Executable.size (e : Executable Instr Const) : Nat :=
  (e.program.map (·.size)).sum

def Layout.apply (l : Layout) (prog : Program Instr Const) : Executable Instr Const :=
  { startAddr := l.start
    program := prog.mapIdx fun i directive => { directive, size := l.size directive i } }

def Program.labels (p : Program Instr Const) : List Label := p.filterMap fun
  | .label l => l
  | _ => none

class Layout.WellFormed (l : Layout) (p : Program Instr Const) : Prop where
  no_overflow : (l.apply p).size < 2 ^ 64
  unique_labels : p.labels.Nodup

instance (l : Layout) (p : Program Instr Const) : Decidable (l.WellFormed p) :=
  decidable_of_iff ((l.apply p).size < 2 ^ 64 ∧ p.labels.Nodup)
    ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

def Layout.drop (l : Layout) (p₁ : Program Instr Const) : Layout where
  start := l.start + .ofNat (l.apply p₁).size
  instrSize i := l.instrSize (i + p₁.length)
  instrSize_pos i := l.instrSize_pos (i + p₁.length)

@[simp]
theorem Layout.drop_nil (l : Layout) : l.drop ([] : Program Instr Const) = l := by
  rcases l with ⟨start, instrSize, instrSize_pos⟩
  simp [Layout.drop, Layout.apply, Executable.size, Int64.add_zero]

@[simp]
theorem Layout.size_drop (l : Layout) (p₁ : Program Instr Const)
    (d : Directive Instr Const) (i : Nat) :
    (l.drop p₁).size d i = l.size d (i + p₁.length) :=
  rfl

theorem Layout.apply_append_program (l : Layout) (p₁ p₂ : Program Instr Const) :
    (l.apply (p₁ ++ p₂)).program =
      (l.apply p₁).program ++ ((l.drop p₁).apply p₂).program := by
  simp [Layout.apply, Layout.drop, List.mapIdx_append]

theorem Layout.size_apply_append (l : Layout) (p₁ p₂ : Program Instr Const) :
    (l.apply (p₁ ++ p₂)).size = (l.apply p₁).size + ((l.drop p₁).apply p₂).size := by
  simp [Executable.size, Layout.apply_append_program]

theorem Layout.WellFormed.of_append_left {l : Layout} {p₁ p₂ : Program Instr Const}
    (hwf : l.WellFormed (p₁ ++ p₂)) : l.WellFormed p₁ where
  no_overflow := by
    have := hwf.no_overflow
    rw [Layout.size_apply_append] at this
    omega
  unique_labels := by
    have hnd : (p₁.labels ++ p₂.labels).Nodup := by
      simpa [Program.labels, List.filterMap_append] using hwf.unique_labels
    exact (List.nodup_append.mp hnd).1

instance Layout.WellFormed.drop {l : Layout} {p₁ p₂ : Program Instr Const}
    [hwf : l.WellFormed (p₁ ++ p₂)] : (l.drop p₁).WellFormed p₂ where
  no_overflow := by
    have := hwf.no_overflow
    rw [Layout.size_apply_append] at this
    omega
  unique_labels := by
    have hnd : (p₁.labels ++ p₂.labels).Nodup := by
      simpa [Program.labels, List.filterMap_append] using hwf.unique_labels
    exact (List.nodup_append.mp hnd).2.1

structure Addressable (Directive : Type) extends Sized Directive where (addr : Int64)

variable (e : Executable Instr Const) (program : List (Sized (Directive Instr Const)))
  {c : Sized (Directive Instr Const)}

-- Returns each directive paired with its start address and size.
-- TODO: tail-recursive version for efficiency?
def Executable.withAddresses (e : Executable Instr Const) :
    List (Addressable (Directive Instr Const)) :=
  let {startAddr, program} := e
  match program with
  | [] => []
  | instr :: program =>
    {instr with addr := startAddr} ::
      Executable.withAddresses {startAddr := startAddr + .ofNat instr.size, program}
termination_by e.2

def Executable.directivesAtAddress (a : Int64) : List (Sized (Directive Instr Const)) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  (starts_at_a.takeWhile (·.addr = a)).map (·.toSized)

theorem Executable.withAddresses_map_snd (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).map (·.toSized) = program := by
  induction program generalizing startAddr <;> grind [Executable.withAddresses]

@[grind hom] theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

/-- The sum of sizes of the first `n` directives of `e`. -/
def Executable.sizeBefore (n : Nat) : Nat :=
  ((e.program.take n).map (·.size)).sum

/--
The address of the `n`-th directive of `e`: the start address of `e` plus the sum of sizes of the
first `n` directives.
-/
def Executable.addrOf (n : Nat) : Int64 :=
  e.startAddr + .ofNat (e.sizeBefore n)

@[simp] theorem Executable.addrOf_zero : e.addrOf 0 = e.startAddr := by
  grind [sizeBefore, addrOf]

@[grind →] theorem Executable.sizeBefore_succ {n : Nat}
    (hc : e.program[n]? = some c) : e.sizeBefore (n + 1) = e.sizeBefore n + c.size := by
  simp [sizeBefore, List.take_add_one, hc]

theorem Executable.sizeBefore_add (j i : Nat) :
    e.sizeBefore (j + i) = e.sizeBefore j + (((e.program.drop j).take i).map (·.size)).sum := by
  simp [sizeBefore, List.take_add]

theorem Executable.sizeBefore_mono {j k : Nat}
    (h : j ≤ k) : e.sizeBefore j ≤ e.sizeBefore k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [sizeBefore_add]

theorem Executable.addrOf_succ {n : Nat}
    (hc : e.program[n]? = some c) : e.addrOf (n + 1) = e.addrOf n + .ofNat c.size := by
  grind [addrOf]

private theorem add_ofNat_add (a : Int64) (b c : Nat) :
    a + .ofNat b + .ofNat c = a + .ofNat (b + c) := by grind

theorem Layout.addrOf_append_left (l : Layout) (p₁ p₂ : Program Instr Const) {i : Nat}
    (hi : i ≤ p₁.length) :
    (l.apply (p₁ ++ p₂)).addrOf i = (l.apply p₁).addrOf i := by
  have hlen : (l.apply p₁).program.length = p₁.length := by simp [Layout.apply]
  change l.start + .ofNat (((l.apply (p₁ ++ p₂)).program.take i).map (·.size)).sum =
    l.start + .ofNat (((l.apply p₁).program.take i).map (·.size)).sum
  rw [Layout.apply_append_program, List.take_append_of_le_length (by omega)]

theorem Layout.addrOf_append_right (l : Layout) (p₁ p₂ : Program Instr Const) (i : Nat) :
    (l.apply (p₁ ++ p₂)).addrOf (i + p₁.length) = ((l.drop p₁).apply p₂).addrOf i := by
  have hlen : (l.apply p₁).program.length = p₁.length := by simp [Layout.apply]
  rw [Nat.add_comm, Executable.addrOf, Executable.sizeBefore_add, Executable.sizeBefore,
    Executable.addrOf, Executable.sizeBefore, Layout.apply_append_program,
    List.take_left' hlen, List.drop_left' hlen]
  change l.start + .ofNat ((l.apply p₁).size + _) = l.start + .ofNat (l.apply p₁).size + .ofNat _
  exact (add_ofNat_add _ _ _).symm

theorem Executable.getElem?_withAddresses_mk :
    ∀ (program : List (Sized (Directive Instr Const))) (startAddr : Int64) (k : Nat),
      (Executable.withAddresses {startAddr, program})[k]? =
        program[k]?.map (fun c => {c with addr := Executable.addrOf {startAddr, program} k})
  | [], a, k => by rw [Executable.withAddresses]; simp
  | c :: program, a, 0 => by
    rw [Executable.withAddresses]
    simp
  | c :: program, a, k + 1 => by
    rw [Executable.withAddresses]
    simp only [List.getElem?_cons_succ, getElem?_withAddresses_mk program _ k]
    congr 2
    funext c'
    simp only [addrOf, sizeBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
    grind

theorem Executable.getElem?_withAddresses_eq (k : Nat) :
    e.withAddresses[k]? = e.program[k]?.map (fun c => {c with addr := e.addrOf k}) :=
  getElem?_withAddresses_mk e.program e.startAddr k

private theorem dropWhile_eq_drop_of {α : Type _} {p : α → Bool} {l : List α} {j : Nat}
    (hprior : ∀ k, k < j → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[j]? = some c → p c = false) :
    l.dropWhile p = l.drop j := by
  rw [List.dropWhile_eq_drop_findIdx_not]
  by_cases hj : j < l.length
  · rw [(List.findIdx_eq hj).mpr ⟨by simp [hhead _ (List.getElem?_eq_getElem hj)],
      fun k hk => by simp [hprior k hk _ (List.getElem?_eq_getElem (by omega))]⟩]
  · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hj), List.drop_eq_nil_iff]
    refine Nat.le_of_eq (List.findIdx_eq_length.mpr fun x hx => ?_).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [hprior i (by omega) _ (List.getElem?_eq_getElem hi)]

theorem Executable.withAddresses_dropWhile_addrOf (j n : Nat)
    (hj : e.addrOf j = e.addrOf n)
    (hfresh : ∀ k, k < j → e.addrOf k ≠ e.addrOf n) :
    e.withAddresses.dropWhile (·.addr ≠ e.addrOf n) = e.withAddresses.drop j := by
  apply dropWhile_eq_drop_of
  · intro k hk c hc
    rw [Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using hfresh k hk
  · intro c hc
    rw [Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using hj

theorem Layout.apply_getElem? (l : Layout) (prog : Program Instr Const) (i : Nat) :
    (l.apply prog).program[i]? = prog[i]?.map fun d => {directive := d, size := l.size d i} := by
  simp [Layout.apply, List.getElem?_mapIdx]

private theorem takeWhile_eq_take_of {α : Type _} {p : α → Bool} {l : List α} {n : Nat}
    (hprior : ∀ k, k < n → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[n]? = some c → p c = false) :
    l.takeWhile p = l.take n := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => simp [hhead a rfl]
    | succ n =>
      simp [hprior 0 (Nat.zero_lt_succ n) a rfl,
        ih (fun k hk => hprior (k + 1) (Nat.succ_lt_succ hk)) hhead]

private theorem exists_least_le {P : Nat → Prop} {n : Nat} (h : P n) :
    ∃ j, j ≤ n ∧ P j ∧ ∀ k, k < j → ¬P k := by
  induction n using Nat.strongRecOn
  grind

theorem Executable.sizeBefore_le (n : Nat) :
    e.sizeBefore n ≤ e.size := by
  simpa [Executable.size, sizeBefore,
    List.take_of_length_le (Nat.le_max_right n e.program.length)] using
    e.sizeBefore_mono (Nat.le_max_left n e.program.length)

theorem Layout.sizeBefore_lt (l : Layout) (prog : Program Instr Const) [hwf : l.WellFormed prog]
    (n : Nat) : (l.apply prog).sizeBefore n < 2 ^ 64 :=
  Nat.lt_of_le_of_lt ((l.apply prog).sizeBefore_le n) hwf.no_overflow

theorem Layout.sizeBefore_eq_of_addrOf_eq (l : Layout) (prog : Program Instr Const)
    [l.WellFormed prog] {j k : Nat}
    (h : (l.apply prog).addrOf j = (l.apply prog).addrOf k) :
    (l.apply prog).sizeBefore j = (l.apply prog).sizeBefore k := by
  have hj := l.sizeBefore_lt prog j
  have hk := l.sizeBefore_lt prog k
  grind [Executable.addrOf]

/-- If the `k`-th directive `d` of `prog` has positive size (`0 < l.size d k`), then
`(l.apply prog).directivesAtAddress ((l.apply prog).addrOf k)` consists of a prefix of
zero-size directives at `(l.apply prog).addrOf k` followed by
`[{directive := d, size := l.size d k}]`. -/
theorem Layout.directivesAtAddress_addrOf (l : Layout) (prog : Program Instr Const)
    [l.WellFormed prog] {k : Nat} {d : Directive Instr Const}
    (hd : prog[k]? = some d) (hz : 0 < l.size d k) :
    ZeroSizePrefix ((l.apply prog).directivesAtAddress ((l.apply prog).addrOf k))
      [{directive := d, size := l.size d k}] := by
  let e := l.apply prog
  have hc : e.program[k]? = some {directive := d, size := l.size d k} := by
    simp [e, Layout.apply_getElem?, hd]
  obtain ⟨j, hjk, hj, hmin⟩ := exists_least_le (P := fun i => e.addrOf i = e.addrOf k) rfl
  have hsize : e.sizeBefore j = e.sizeBefore k := l.sizeBefore_eq_of_addrOf_eq prog hj
  have hpre (c') (hc' : c' ∈ (e.program.drop j).take (k - j)) : c'.size = 0 := by
    have := e.sizeBefore_add j (k - j)
    rw [Nat.add_sub_cancel' hjk] at this
    have hsum : (((e.program.drop j).take (k - j)).map (·.size)).sum = 0 := by omega
    exact List.sum_eq_zero_iff_forall_eq_nat.mp hsum _ (List.mem_map_of_mem hc')
  have haddr (m : Nat) (hjm : j ≤ m) (hmk : m ≤ k) : e.addrOf m = e.addrOf k := by
    grind [Executable.addrOf, e.sizeBefore_mono hjm, e.sizeBefore_mono hmk]
  have hnext : e.addrOf (k + 1) ≠ e.addrOf k := fun h => by
    have : e.sizeBefore (k + 1) = e.sizeBefore k := l.sizeBefore_eq_of_addrOf_eq prog h
    grind
  refine ⟨(e.program.drop j).take (k - j), ?_, hpre⟩
  rw [Executable.directivesAtAddress, Executable.withAddresses_dropWhile_addrOf _ j k hj hmin,
    takeWhile_eq_take_of (n := k - j + 1)]
  · rw [List.map_take, List.map_drop, Executable.withAddresses_map_snd, List.take_add_one,
      List.getElem?_drop, Nat.add_sub_cancel' hjk, hc, Option.toList]
  · grind [Executable.getElem?_withAddresses_eq, Executable.sizeBefore_mono]
  · grind [Executable.getElem?_withAddresses_eq]

def Directive.isLabel (lbl : Label) : Directive Instr Const → Bool
  | .label l => l == lbl
  | _ => false

@[simp] theorem Directive.isLabel_iff {lbl : Label} {d : Directive Instr Const} :
    d.isLabel lbl = true ↔ d = .label lbl := by
  cases d <;> simp [Directive.isLabel]

theorem Executable.withAddresses_findSome?_label_mk [DecidableEq Instr] [DecidableEq Const] :
    ∀ (program : List (Sized (Directive Instr Const))) (startAddr : Int64) (lbl : Label) (k : Nat),
      program.findIdx? (·.directive.isLabel lbl) = some k →
      (Executable.withAddresses {startAddr, program}).findSome?
        (fun {directive, addr, ..} => if directive = .label lbl then .some addr else .none) =
        some (Executable.addrOf {startAddr, program} k)
  | [], _, _, _, hk => by simp at hk
  | c :: program, startAddr, lbl, k, hk => by
    rw [Executable.withAddresses, List.findSome?_cons]
    rw [List.findIdx?_cons] at hk
    by_cases h : c.directive = .label lbl
    · have his : c.directive.isLabel lbl = true := Directive.isLabel_iff.mpr h
      simp [his] at hk
      subst hk
      simp [h]
    · have his : c.directive.isLabel lbl = false :=
        Bool.eq_false_iff.mpr (mt Directive.isLabel_iff.mp h)
      simp [his] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      simp only [h, ↓reduceIte, withAddresses_findSome?_label_mk program _ lbl k' hk']
      simp only [addrOf, sizeBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
      grind

@[simp] theorem Layout.map_directive_apply (l : Layout) (prog : Program Instr Const) :
    (l.apply prog).program.map (·.directive) = prog :=
  List.ext_getElem? fun _ => by simp [Layout.apply, List.getElem?_mapIdx, Function.comp_def]

/-- If `k` is the index of the first `.label lbl` directive in `prog`, looking up `lbl` in
`(l.apply prog).withAddresses` yields `some ((l.apply prog).addrOf k)`. -/
theorem Layout.withAddresses_findSome?_label [DecidableEq Instr] [DecidableEq Const]
    (l : Layout) (prog : Program Instr Const) (lbl : Label) {k : Nat}
    (hk : prog.findIdx? (·.isLabel lbl) = some k) :
    ((l.apply prog).withAddresses.findSome?
      (fun {directive, addr, ..} => if directive = .label lbl then .some addr else .none)) =
      some ((l.apply prog).addrOf k) := by
  apply Executable.withAddresses_findSome?_label_mk
  rw [← l.map_directive_apply prog, List.findIdx?_map] at hk
  exact hk

theorem Executable.withAddresses_eq_mapIdx (e : Executable Instr Const) :
    e.withAddresses = e.program.mapIdx fun idx c => {c with addr := e.addrOf idx} :=
  List.ext_getElem? fun k => by
    simpa [List.getElem?_mapIdx] using e.getElem?_withAddresses_eq k

theorem Layout.withAddresses_apply (l : Layout) (p : Program Instr Const) :
    (l.apply p).withAddresses =
      p.mapIdx fun idx directive =>
        {directive, size := l.size directive idx, addr := (l.apply p).addrOf idx} :=
  List.ext_getElem? fun k => by
    simp [Executable.withAddresses_eq_mapIdx, Layout.apply, List.getElem?_mapIdx, Function.comp_def]

@[simp] theorem Layout.map_directive_withAddresses (l : Layout) (p : Program Instr Const) :
    (l.apply p).withAddresses.map (·.directive) = p :=
  List.ext_getElem? fun _ => by
    simp [Layout.withAddresses_apply, List.getElem?_mapIdx, Function.comp_def]

private theorem mem_withAddresses_apply (l : Layout) (p : Program Instr Const)
    {x : Addressable (Directive Instr Const)} (hx : x ∈ (l.apply p).withAddresses) :
    ∃ i : Fin p.length,
      x = {directive := p[i], size := l.size p[i] i, addr := (l.apply p).addrOf i} ∧
      (l.apply p).sizeBefore i + x.size ≤ (l.apply p).size := by
  rw [Layout.withAddresses_apply] at hx
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hx
  simp only [List.length_mapIdx, List.getElem_mapIdx] at hi heq
  have hc : (l.apply p).program[i]? = some {directive := p[i], size := l.size p[i] i} := by
    simp [Layout.apply, List.getElem?_mapIdx, List.getElem?_eq_getElem hi]
  refine ⟨⟨i, hi⟩, heq.symm, ?_⟩
  have hle := (l.apply p).sizeBefore_succ hc ▸ (l.apply p).sizeBefore_le (i + 1)
  simpa [← heq] using hle

theorem Layout.mem_directivesAtAddress (l : Layout) (p : Program Instr Const)
    {a : Int64} {c : Sized (Directive Instr Const)}
    (h : c ∈ (l.apply p).directivesAtAddress a) :
    ∃ i : Fin p.length,
      c = {directive := p[i], size := l.size p[i] i} ∧ (l.apply p).addrOf i = a := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  have haddr : x.addr = a := by simpa using List.mem_takeWhile hx
  obtain ⟨i, rfl, -⟩ := mem_withAddresses_apply l p
    ((List.dropWhile_sublist _).subset ((List.takeWhile_sublist _).subset hx))
  exact ⟨i, rfl, haddr⟩

theorem Layout.mem_of_zeroSizePrefix {l : Layout} {p : Program Instr Const}
    {pc : Int64} {pre rest : List (Sized (Directive Instr Const))}
    (hpre : (l.apply p).directivesAtAddress pc = pre ++ rest) (hz : ∀ c ∈ pre, c.size = 0)
    {c : Sized (Directive Instr Const)} (hc : c ∈ pre) :
    ∃ m d, c = {directive := d, size := 0} ∧ l.size d m = 0 := by
  obtain ⟨i, rfl, -⟩ := l.mem_directivesAtAddress p (hpre ▸ List.mem_append_left _ hc)
  have hcz : l.size p[i] i = 0 := hz _ hc
  exact ⟨i, p[i], by congr, hcz⟩

theorem Layout.apply_append_withAddresses (l : Layout) (p₁ p₂ : Program Instr Const) :
    (l.apply (p₁ ++ p₂)).withAddresses =
      (l.apply p₁).withAddresses ++ ((l.drop p₁).apply p₂).withAddresses := by
  rw [Layout.withAddresses_apply l (p₁ ++ p₂), Layout.withAddresses_apply l p₁,
    Layout.withAddresses_apply (l.drop p₁) p₂, List.mapIdx_append]
  congr 1
  · refine List.ext_getElem? fun i => ?_
    by_cases hi : i < p₁.length
    · simp [List.getElem?_mapIdx, List.getElem?_eq_getElem hi,
        Layout.addrOf_append_left l p₁ p₂ (Nat.le_of_lt hi)]
    · simp [List.getElem?_mapIdx, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
  · refine List.ext_getElem? fun i => ?_
    simp only [List.getElem?_mapIdx]
    exact congrArg (Option.map · p₂[i]?) (funext fun d => by
      simp [Layout.drop, Layout.addrOf_append_right l p₁ p₂ i])

theorem Layout.directivesAtAddress_infix_eq (l : Layout) (p₁ p p₂ : Program Instr Const)
    [hwf : l.WellFormed (p₁ ++ (p ++ p₂))] (pc : Int64)
    (hpos : ∃ c ∈ ((l.drop p₁).apply p).directivesAtAddress pc, 0 < c.size) :
    ZeroSizePrefix ((l.apply (p₁ ++ (p ++ p₂))).directivesAtAddress pc)
      (((l.drop p₁).apply p).directivesAtAddress pc) := by
  obtain ⟨_, hc₀, hcsz⟩ := hpos
  obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hc₀
  have hx₀_drop : x₀ ∈ ((l.drop p₁).apply p).withAddresses.dropWhile (·.addr ≠ pc) :=
    (List.takeWhile_sublist _).subset hx₀
  have hx₀_addr : x₀.addr = pc := by simpa using List.mem_takeWhile hx₀
  obtain ⟨i, hi_eq, hi_le⟩ :=
    mem_withAddresses_apply (l.drop p₁) p ((List.dropWhile_sublist _).subset hx₀_drop)
  have haddr : x₀.addr = ((l.drop p₁).apply p).addrOf i := congrArg Addressable.addr hi_eq
  have hsz_lt : ((l.drop p₁).apply p).sizeBefore i < ((l.drop p₁).apply p).size := by
    have : 0 < x₀.size := hcsz
    omega
  have hsum_lt : (l.apply p₁).size + ((l.drop p₁).apply p).size +
      (((l.drop p₁).drop p).apply p₂).size < UInt64.size := by
    have := hwf.no_overflow
    rw [Layout.size_apply_append l p₁ (p ++ p₂),
      Layout.size_apply_append (l.drop p₁) p p₂] at this
    have : UInt64.size = 2 ^ 64 := rfl
    omega
  have he_mid : ((l.drop p₁).apply p).startAddr =
      (l.apply p₁).startAddr + .ofNat (l.apply p₁).size := rfl
  have he₂ : (((l.drop p₁).drop p).apply p₂).startAddr =
      l.start + .ofNat ((l.apply p₁).size + ((l.drop p₁).apply p).size) := by
    change l.start + .ofNat (l.apply p₁).size + .ofNat ((l.drop p₁).apply p).size = _
    exact add_ofNat_add _ _ _
  have htw₂ : (((l.drop p₁).drop p).apply p₂).withAddresses.takeWhile (·.addr = pc) = [] := by
    cases h : (((l.drop p₁).drop p).apply p₂).withAddresses.takeWhile (·.addr = pc) with
    | nil => rfl
    | cons y _ =>
      have hy_mem : y ∈ (((l.drop p₁).drop p).apply p₂).withAddresses :=
        (List.takeWhile_sublist _).subset (h ▸ List.mem_cons_self)
      have hy_addr : y.addr = pc := by
        have := List.mem_takeWhile (h ▸ List.mem_cons_self)
        simpa using this
      obtain ⟨i₂, hy₂, hi₂⟩ := mem_withAddresses_apply ((l.drop p₁).drop p) p₂ hy_mem
      have haddr₂ : y.addr = (((l.drop p₁).drop p).apply p₂).addrOf i₂ :=
        congrArg Addressable.addr hy₂
      have hpc : ((l.drop p₁).apply p).addrOf i = (((l.drop p₁).drop p).apply p₂).addrOf i₂ :=
        (hx₀_addr ▸ haddr).symm.trans (hy_addr ▸ haddr₂)
      simp only [Executable.addrOf, he_mid, he₂, add_ofNat_add] at hpc
      change l.start + .ofNat ((l.apply p₁).size + ((l.drop p₁).apply p).sizeBefore i) =
        l.start + .ofNat ((l.apply p₁).size + ((l.drop p₁).apply p).size +
          (((l.drop p₁).drop p).apply p₂).sizeBefore i₂) at hpc
      have := Int64.add_ofNat_inj (by omega) (by omega) hpc
      omega
  have happ : (l.apply (p₁ ++ (p ++ p₂))).withAddresses =
      (l.apply p₁).withAddresses ++
        (((l.drop p₁).apply p).withAddresses ++ (((l.drop p₁).drop p).apply p₂).withAddresses) := by
    rw [Layout.apply_append_withAddresses l p₁ (p ++ p₂),
      Layout.apply_append_withAddresses (l.drop p₁) p p₂]
  have takeWhile_append_two (xs : List (Addressable (Directive Instr Const))) :
      ((xs ++ (((l.drop p₁).drop p).apply p₂).withAddresses).takeWhile (·.addr = pc)) =
        xs.takeWhile (·.addr = pc) := by
    rw [List.takeWhile_append]
    split
    · rename_i hlen; rw [htw₂, List.append_nil, (List.takeWhile_sublist _).eq_of_length hlen]
    · rfl
  let w₁' := (l.apply p₁).withAddresses.dropWhile (·.addr ≠ pc)
  have hne_mid : (((l.drop p₁).apply p).withAddresses.dropWhile (·.addr ≠ pc)).isEmpty = false :=
    Bool.eq_false_iff.mpr (mt List.isEmpty_iff.mp (List.ne_nil_of_mem hx₀_drop))
  cases h_emp : w₁'.isEmpty with
  | true =>
    refine ⟨[], ?_, by simp⟩
    dsimp only [Executable.directivesAtAddress, w₁'] at h_emp ⊢
    rw [happ, List.dropWhile_append, h_emp, List.nil_append, List.dropWhile_append, hne_mid]
    simp only [Bool.false_eq_true, ↓reduceIte, takeWhile_append_two]
  | false =>
    have hne : w₁' ≠ [] := fun h => by simp [h] at h_emp
    let j := (l.apply p₁).withAddresses.findIdx (fun a => !decide (a.addr ≠ pc))
    have hw₁' : w₁' = (l.apply p₁).withAddresses.drop j := List.dropWhile_eq_drop_findIdx_not
    have hj_lt : j < (l.apply p₁).withAddresses.length :=
      Classical.byContradiction fun hge =>
        hne (hw₁'.trans (List.drop_eq_nil_of_le (Nat.le_of_not_lt hge)))
    have hj_addr : (l.apply p₁).addrOf j = pc := by
      have hhead : !decide ((l.apply p₁).withAddresses[j].addr ≠ pc) = true :=
        List.findIdx_getElem (w := hj_lt)
      have hget := Executable.getElem?_withAddresses_eq (l.apply p₁) j
      rw [List.getElem?_eq_getElem hj_lt] at hget
      obtain ⟨_, -, heq⟩ := Option.map_eq_some_iff.mp hget.symm
      have : (l.apply p₁).withAddresses[j].addr = (l.apply p₁).addrOf j :=
        congrArg Addressable.addr heq.symm
      grind
    have haddr₁₂ : (l.apply p₁).addrOf j = ((l.drop p₁).apply p).addrOf i :=
      hj_addr.trans (hx₀_addr ▸ haddr)
    simp only [Executable.addrOf, he_mid, add_ofNat_add] at haddr₁₂
    change l.start + .ofNat ((l.apply p₁).sizeBefore j) =
      l.start + .ofNat ((l.apply p₁).size + ((l.drop p₁).apply p).sizeBefore i) at haddr₁₂
    have hj_le : (l.apply p₁).sizeBefore j ≤ (l.apply p₁).size := (l.apply p₁).sizeBefore_le j
    have hoff_eq : (l.apply p₁).sizeBefore j =
        (l.apply p₁).size + ((l.drop p₁).apply p).sizeBefore i :=
      Int64.add_ofNat_inj (by omega) (by omega) haddr₁₂
    have hpc_mid : ((l.drop p₁).apply p).startAddr = pc := by
      rw [← hj_addr, he_mid]
      change l.start + .ofNat _ = l.start + .ofNat _
      congr 2
      omega
    have hw₁'_prop : ∀ x ∈ w₁', x.addr = pc ∧ x.size = 0 := by
      intro x hx
      rw [hw₁'] at hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      simp only [List.getElem_drop]
      have hget := Executable.getElem?_withAddresses_eq (l.apply p₁) (j + k)
      rw [List.getElem?_eq_getElem (by rw [List.length_drop] at hk; omega)] at hget
      obtain ⟨c, hc, heq⟩ := Option.map_eq_some_iff.mp hget.symm
      have hmono := (l.apply p₁).sizeBefore_mono (Nat.le_add_right j k)
      have hsucc : (l.apply p₁).sizeBefore (j + k) + c.size ≤ (l.apply p₁).size :=
        (l.apply p₁).sizeBefore_succ hc ▸ (l.apply p₁).sizeBefore_le (j + k + 1)
      rw [← heq]
      refine ⟨?_, by dsimp; omega⟩
      dsimp [Executable.addrOf]
      rw [← hj_addr]
      congr 2
      omega
    have hdrop_mid :
        ((l.drop p₁).apply p).withAddresses.dropWhile (·.addr ≠ pc) =
          ((l.drop p₁).apply p).withAddresses := by
      simpa only [← hpc_mid, Executable.addrOf_zero, List.drop_zero] using
        ((l.drop p₁).apply p).withAddresses_dropWhile_addrOf 0 0 rfl (by omega)
    refine ⟨w₁'.map (·.toSized), ?_, fun c hc => ?_⟩
    · dsimp only [Executable.directivesAtAddress, w₁'] at h_emp ⊢
      rw [happ, List.dropWhile_append]
      simp only [h_emp, Bool.false_eq_true, ↓reduceIte, hdrop_mid]
      rw [List.takeWhile_append_of_pos (fun x hx => decide_eq_true (hw₁'_prop x hx).1),
          takeWhile_append_two, List.map_append]
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      exact (hw₁'_prop x hx).2

end Kraken
