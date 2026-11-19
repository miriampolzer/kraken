module

/-
Omnisemantics for x64.
-/

import Kraken.Attribute
public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

@[expose] public section

open Kraken (Layout)

@[kstep] def Effects.All [Labels] (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .resolve_label lbl k =>
    match label? lbl with
    | .some a => (k a).All post
    | .none => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ cont => (cont ()).All post
  | .require_write_access _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

@[ksimp] theorem Effects.All_resolve_label [Labels] (lbl : Label) (k : Int64 → Effects)
    (post : MachineState → Prop) :
    (Effects.resolve_label lbl k).All post =
      (match label? lbl with | .some a => (k a).All post | .none => False) := by
  rw [Effects.All]

@[ksimp] theorem Effects.All_require_read_access [Labels] (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_read_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.All_require_write_access [Labels] (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_write_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

def step1 (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  letI := e.labels
  (Executable.step e s .done).All post

private theorem Directives.interp_directivesAtAddress_of_zeroSizePrefix
    {l : Layout} {p : Program} {pc : Int64} {rest : List (Kraken.Sized Directive)}
    (h : Kraken.ZeroSizePrefix ((l.apply p).directivesAtAddress pc) rest)
    (s : MachineData) (ret : Int64 → MachineData → Effects) :
    Directives.interp ((l.apply p).directivesAtAddress pc) s pc ret =
      Directives.interp rest s pc ret := by
  obtain ⟨pre, hpre, hz⟩ := h
  rw [hpre]
  have hmem := fun c (hc : c ∈ pre) => Kraken.Layout.mem_of_zeroSizePrefix hpre hz hc
  clear hpre hz
  induction pre generalizing s with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨m, d', rfl, hz0⟩ := hmem c List.mem_cons_self
    simp only [List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
      inert_of_size_zero l hz0]
    exact ih s (fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc'))

theorem eventually_of_interp {l : Layout} {p : Program} [l.WellFormed p]
    {k : Nat} {d : Directive} (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels (l.apply p)
      (d.interp s
        ⟨(l.apply p).addrOf k, (l.apply p).addrOf (k + 1)⟩
        (fun s' => .done ⟨s', (l.apply p).addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 (l.apply p)) post ⟨s, (l.apply p).addrOf k⟩ := by
  have hc : (l.apply p).program[k]? = some {directive := d, size := l.size d k} := by
    simp only [Kraken.Layout.apply_getElem?, hd, Option.map_some]
  have hsucc := (l.apply p).addrOf_succ hc
  letI : Labels := Executable.labels (l.apply p)
  match hsize : l.size d k with
  | 0 =>
    apply Eventually.done
    simpa [-Kraken.Layout.size, hsucc, hsize, inert_of_size_zero l hsize, Effects.All] using h
  | _ + 1 =>
    refine .step _ post ?_ fun _ => .done _
    unfold step1 Executable.step
    dsimp only
    rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix
      (l.directivesAtAddress_addrOf p hd (by grind only))]
    simpa [-Kraken.Layout.size, Directives.interp, hsucc, hsize] using h

@[ksimp] theorem Int64.add_sub_cancel_left (a b : Int64) : a + (b - a) = b := by grind
@[ksimp] theorem Int64.ofBitVec_toBitVec_ksimp (a : Int64) : Int64.ofBitVec a.toBitVec = a :=
  Int64.ofBitVec_toBitVec a

theorem step_at {l : Layout} {p : Program} [l.WellFormed p] {k : Nat} {d : Directive}
    (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels (l.apply p)
      (d.interp s
        ⟨(l.apply p).addrOf k, (l.apply p).addrOf (k + 1)⟩
        (fun s' => .done ⟨s', (l.apply p).addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All (Eventually (step1 (l.apply p)) post)) :
    Eventually (step1 (l.apply p)) post ⟨s, (l.apply p).addrOf k⟩ :=
  eventually_trans _ _ _ _ (eventually_of_interp hd h) fun _ => id

theorem label?_eq_some_addrOf {l : Layout} {p : Program} {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) :
    @Labels.label? (Executable.labels (l.apply p)) lbl = some ((l.apply p).addrOf k) :=
  l.withAddresses_findSome?_label p lbl hk

/-- `L₁ ⊆ L₂` means every label resolved by `L₁` resolves to the same address in `L₂`. -/
instance : HasSubset Labels where
  Subset L₁ L₂ := ∀ l a, L₁.label? l = some a → L₂.label? l = some a

private theorem Effects.All_mono_labels {L₁ L₂ : Labels} (hL : L₁ ⊆ L₂)
    {post : MachineState → Prop} (e : Effects)
    (h : @Effects.All L₁ post e) : @Effects.All L₂ post e := by
  match e with
  | .done _ | .unimplemented _ | .gp_unaligned .. | .nonmem_load .. | .nonmem_store .. => exact h
  | .resolve_label lbl k =>
    simp only [Effects.All_resolve_label] at h ⊢
    cases hlbl : L₁.label? lbl <;> rw [hlbl] at h
    · exact False.elim h
    · rw [hL lbl _ hlbl]; exact All_mono_labels hL (k _) h
  | @Effects.undefined _ _ cont => exact fun v => All_mono_labels hL (cont v) (h v)
  | .require_read_access _ cont | .require_write_access _ cont | .require_exec_access _ cont =>
    exact All_mono_labels hL (cont ()) h

private theorem label?_eq_some_mem {layout : Layout} {p : Program} {l : Label} {a : Int64}
    (h : (Executable.labels (layout.apply p)).label? l = some a) :
    l ∈ Kraken.Program.labels p := by
  obtain ⟨x, hx, hfx⟩ := List.exists_of_findSome?_eq_some h
  have hd : x.directive = .label l := by
    rcases x with ⟨d, _, _⟩; dsimp only at hfx; split at hfx <;> simp_all
  have hmem : Kraken.Directive.label l ∈ p :=
    layout.map_directive_withAddresses p ▸ hd ▸ List.mem_map_of_mem (f := (·.directive)) hx
  exact List.mem_filterMap.mpr ⟨.label l, hmem, rfl⟩

theorem labels_infix_subset (layout : Layout) (p₁ p p₂ : Program)
    [hwf : layout.WellFormed (p₁ ++ (p ++ p₂))] :
    Executable.labels ((layout.drop p₁).apply p) ⊆
      Executable.labels (layout.apply (p₁ ++ (p ++ p₂))) := by
  intro lbl a ha
  have hmem : lbl ∈ Kraken.Program.labels p := label?_eq_some_mem ha
  have happ : (layout.apply (p₁ ++ (p ++ p₂))).withAddresses =
      (layout.apply p₁).withAddresses ++
        (((layout.drop p₁).apply p).withAddresses ++
          (((layout.drop p₁).drop p).apply p₂).withAddresses) := by
    rw [layout.apply_append_withAddresses p₁ (p ++ p₂),
      (layout.drop p₁).apply_append_withAddresses p p₂]
  change List.findSome? _ _ = some a at ha ⊢
  rw [happ, List.findSome?_append]
  cases h₁ : List.findSome? _ (layout.apply p₁).withAddresses with
  | none => simp [List.findSome?_append, ha]
  | some _ =>
    have hmem₁ : lbl ∈ Kraken.Program.labels p₁ := label?_eq_some_mem h₁
    have hmem₂₃ : lbl ∈ Kraken.Program.labels (p ++ p₂) := by
      simpa [Kraken.Program.labels, List.filterMap_append] using Or.inl hmem
    have hnodup : (Kraken.Program.labels p₁ ++ Kraken.Program.labels (p ++ p₂)).Nodup := by
      simpa [Kraken.Program.labels, List.filterMap_append] using hwf.unique_labels
    exact absurd rfl ((List.nodup_append.mp hnodup).2.2 lbl hmem₁ lbl hmem₂₃)

theorem Eventually.infix {layout : Layout} (p₁ p p₂ : Program)
    [hwf : layout.WellFormed (p₁ ++ (p ++ p₂))]
    (post : MachineState → Prop) (init : MachineState)
    (h : Eventually (step1 ((layout.drop p₁).apply p)) post init) :
    Eventually (step1 (layout.apply (p₁ ++ (p ++ p₂)))) post init := by
  haveI : (layout.drop p₁).WellFormed p :=
    (inferInstance : (layout.drop p₁).WellFormed (p ++ p₂)).of_append_left
  induction h with
  | done s hp => exact .done s hp
  | step s mid_p hstep _ ih =>
    by_cases hpos : ∃ c ∈ ((layout.drop p₁).apply p).directivesAtAddress s.pc, 0 < c.size
    · refine .step s mid_p ?_ ih
      dsimp only [step1, Executable.step] at hstep ⊢
      rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix
        (layout.directivesAtAddress_infix_eq p₁ p p₂ s.pc hpos)]
      exact Effects.All_mono_labels (labels_infix_subset layout p₁ p p₂) _ hstep
    · have hall0 :
          Kraken.ZeroSizePrefix (((layout.drop p₁).apply p).directivesAtAddress s.pc) [] :=
        ⟨((layout.drop p₁).apply p).directivesAtAddress s.pc, by simp,
          fun c hc => Classical.byContradiction fun hz => hpos ⟨c, hc, Nat.pos_of_ne_zero hz⟩⟩
      dsimp only [step1, Executable.step] at hstep
      letI := Executable.labels ((layout.drop p₁).apply p)
      rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix hall0,
          Directives.interp, Effects.All] at hstep
      exact ih ⟨s.data, s.pc⟩ hstep

theorem Eventually.prepend {layout : Layout} (p₁ p₂ : Program)
    [hwf : layout.WellFormed (p₁ ++ p₂)]
    (post : MachineState → Prop) (init : MachineState)
    (h : Eventually (step1 ((layout.drop p₁).apply p₂)) post init) :
    Eventually (step1 (layout.apply (p₁ ++ p₂))) post init := by
  haveI : layout.WellFormed (p₁ ++ (p₂ ++ [])) := by simpa only [List.append_nil] using hwf
  simpa only [List.append_nil] using Eventually.infix p₁ p₂ [] post init h

theorem Eventually.append {layout : Layout} (p₁ p₂ : Program)
    [hwf : layout.WellFormed (p₁ ++ p₂)]
    (post : MachineState → Prop) (init : MachineState)
    (h : Eventually (step1 (layout.apply p₁)) post init) :
    Eventually (step1 (layout.apply (p₁ ++ p₂))) post init := by
  haveI : layout.WellFormed ([] ++ (p₁ ++ p₂)) := hwf
  apply Eventually.infix [] p₁ p₂
  rwa [Layout.drop_nil]
