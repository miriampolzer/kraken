module

public import Kraken.X64.OmniSemantics

@[expose] public section

/--
`d` is inert if it falls through with the same machine state and no observable effect.

Presently, labels, empty `.byteArray`s, and no-op instructions like `nop` and `mov %rax, %rax` are
inert.
-/
def Directive.Inert (d : Directive) : Prop :=
  ∀ [Labels] s p (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) post,
    (d.interp s p next jmp).All post ↔ (next s).All post

theorem Directive.inert_of_size_eq_zero [l : Layout] {i : Nat} {d : Directive}
    (hz : l.size d i = 0) : d.Inert := by
  cases d with
  | instr _ => exact absurd hz (Nat.ne_of_gt (l.instrSize_pos i))
  | label _ => exact fun _ _ _ _ _ => Iff.rfl
  | byteArray bs =>
    intro _ s p next jmp post
    simp [Directive.interp, ByteArray.isEmpty, show bs.size = 0 from hz]

theorem Directives.interp_inert_append [Labels] {pre rest : List (Kraken.Sized Directive)}
    (hpre : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert) (s : MachineData) (pc : Int64)
    (ret : Int64 → MachineData → Effects) (post : @Post MachineState) :
    (Directives.interp (pre ++ rest) s pc ret).All post ↔ (Directives.interp rest s pc ret).All post := by
  induction pre generalizing s with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨hz, hinert⟩ := hpre c List.mem_cons_self
    obtain ⟨d, z⟩ := c
    dsimp only at hz hinert
    subst hz
    have h0 : pc + Int64.ofNat 0 = pc := by simp
    simp only [List.cons_append, Directives.interp, h0]
    rw [hinert]
    exact ih (fun c hc => hpre c (List.mem_cons_of_mem _ hc)) s
