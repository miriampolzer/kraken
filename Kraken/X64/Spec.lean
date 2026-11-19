module

public import Kraken.X64.OmniSemantics

public section

open Kraken (Layout)

section Infix
variable {l : Layout} {prog : Program} [hwf : l.WellFormed prog]

theorem lift_infix (p₁ f p₂ : Program) (hP : p₁ ++ f ++ p₂ = prog)
    {post : MachineState → Prop} {init : MachineState}
    (h : [(l.drop p₁).WellFormed f] → Eventually (step1 ((l.drop p₁).apply f)) post init) :
    Eventually (step1 (l.apply prog)) post init := by
  subst hP
  haveI : l.WellFormed (p₁ ++ (f ++ p₂)) := by simpa only [List.append_assoc] using hwf
  haveI : (l.drop p₁).WellFormed f := hwf.of_append_left.drop
  simpa only [List.append_assoc] using Eventually.infix p₁ f p₂ post init h

theorem label?_infix (p₁ f p₂ : Program) (hP : p₁ ++ f ++ p₂ = prog)
    {lbl : Label} {k : Nat} (hk : f.findIdx? (·.isLabel lbl) = some k) :
    (Executable.labels (l.apply prog)).label? lbl = some (((l.drop p₁).apply f).addrOf k) := by
  subst hP
  haveI : l.WellFormed (p₁ ++ (f ++ p₂)) := by simpa only [List.append_assoc] using hwf
  rw [List.append_assoc]
  exact labels_infix_subset l p₁ f p₂ lbl _ (label?_eq_some_addrOf hk)

theorem step_at_infix (p₁ f p₂ : Program) (hP : p₁ ++ f ++ p₂ = prog)
    {k : Nat} {d : Directive} (hd : f[k]? = some d)
    {s : MachineData} {post : @Post MachineState}
    (h : letI := Executable.labels (l.apply prog)
      let ef := (l.drop p₁).apply f
      (d.interp s ⟨ef.addrOf k, ef.addrOf (k + 1)⟩
        (fun s' => .done ⟨s', ef.addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All (Eventually (step1 (l.apply prog)) post)) :
    Eventually (step1 (l.apply prog)) post ⟨s, ((l.drop p₁).apply f).addrOf k⟩ := by
  subst hP
  have hk_lt : k < f.length := (List.getElem?_eq_some_iff.mp hd).1
  have hd' : (p₁ ++ f ++ p₂)[k + p₁.length]? = some d := by
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
      List.getElem?_append_left hk_lt, hd]
  have hadr {j : Nat} (hj : j ≤ f.length) :
      (l.apply (p₁ ++ f ++ p₂)).addrOf (j + p₁.length) = ((l.drop p₁).apply f).addrOf j := by
    rw [List.append_assoc]
    exact (l.addrOf_append_right p₁ (f ++ p₂) j).trans ((l.drop p₁).addrOf_append_left f p₂ hj)
  rw [← hadr (Nat.le_of_lt hk_lt)]
  refine step_at (l := l) (p := p₁ ++ f ++ p₂) hd' ?_
  rwa [hadr (Nat.le_of_lt hk_lt),
    show k + p₁.length + 1 = (k + 1) + p₁.length by omega, hadr hk_lt]

end Infix

@[expose] def Stalls (e : Executable) (pc : Int64) : Prop :=
  ∀ s U, step1 e ⟨s, pc⟩ U → U ⟨s, pc⟩

theorem stalls_sub_one {l : Layout} {prog : Program} (hsz : (l.apply prog).size < 2 ^ 64 - 1) :
    Stalls (l.apply prog) (l.start - 1) := by
  have hnil : (l.apply prog).directivesAtAddress (l.start - 1) = [] := by
    refine List.eq_nil_iff_forall_not_mem.mpr fun c hc => ?_
    obtain ⟨⟨i, _⟩, _, haddr⟩ := l.mem_directivesAtAddress prog hc
    have hlt : (l.apply prog).sizeBefore i < 2 ^ 64 - 1 :=
      Nat.lt_of_le_of_lt ((l.apply prog).sizeBefore_le i) hsz
    change l.start + Int64.ofNat ((l.apply prog).sizeBefore i) = l.start - 1 at haddr
    grind [show (-1 : Int64).toBitVec = -1#64 from rfl]
  intro s U hs
  simpa [step1, Executable.step, hnil, Directives.interp, Effects.All] using hs

@[expose] def Spec (l : Layout) (prog : Program) (lbl : Label)
    (Pre : MachineData → Prop) (Post : MachineData → MachineState → Prop) : Prop :=
  ∃ entry, (Executable.labels (l.apply prog)).label? lbl = some entry ∧
    ∀ s, Pre s → Eventually (step1 (l.apply prog)) (Post s) ⟨s, entry⟩

theorem Spec.and {l : Layout} {prog : Program} {lbl : Label}
    {Pre : MachineData → Prop} {Post₁ Post₂ : MachineData → MachineState → Prop}
    (h₁ : Spec l prog lbl Pre Post₁) (h₂ : Spec l prog lbl Pre Post₂)
    (hstall : ∀ s u, Pre s → (Post₁ s u ∨ Post₂ s u) → Stalls (l.apply prog) u.pc) :
    Spec l prog lbl Pre (fun s u => Post₁ s u ∧ Post₂ s u) := by
  obtain ⟨e₁, hl₁, hr₁⟩ := h₁
  obtain ⟨e₂, hl₂, hr₂⟩ := h₂
  cases hl₁.symm.trans hl₂
  refine ⟨e₁, hl₁, fun s hs => ?_⟩
  letI := Executable.labels (l.apply prog)
  exact Eventually.and_of_stall (trans := step1 (l.apply prog))
    (S := fun u => Stalls (l.apply prog) u.pc)
    (fun u U hst hstep => hst u.data U hstep)
    (fun _ _ _ ha hb => Effects.All.and ha hb)
    (fun u hp => hstall s u hs (Or.inl hp))
    (fun u hq => hstall s u hs (Or.inr hq))
    (hr₁ s hs) (hr₂ s hs)

end
