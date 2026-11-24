import checkpoints.shen_extension.ExceptionalFirstBill

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- Price a retained short primary claim on its actual booked cycle. The
factor four consists of at most two successors and one omitted exterior label. -/
theorem booked_short_price {D V q r target C Y} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (ym : Y∈claims t C) (first : C⊆outN D V (t.rep Y)) (width : (exterior D V C).card=r)
    (size : C.card+1=r) (short : (ball D V (t.rep Y) 3).card<3*r) (two : Y.card=r-1) :
    (3*C.card+6:ℕ)≤rowStock t (booked t) C*4 := by
  classical
  obtain ⟨key,id⟩ := mem_filter.mp ym
  have y := rep_key t key
  have sec := (congrArg card y).trans two
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have fit := ready.close
  have uv := rep_native t key
  have shape := short_shapes free reg ready uv short
  have third : (N3 D V (t.rep Y)).card=r-1 := by rcases shape with a|a <;> omega
  have roots := t.rooted _ (t.assigned _ key)
  have length := t.length _ (t.assigned _ key)
  rw [id] at roots length
  have kept : Y∉shortSwitches t := by
    intro moved
    have eq := (policy.secondary _ moved).symm.trans id
    obtain ⟨a,am⟩ := card_pos.mp (show 0<C.card by omega)
    exact (mem_N2.mp (y.symm ▸ (eq.symm ▸ am))).2 (X_B1 (first am))
  have four : r≤(ball D V (t.rep Y) 4\ball D V (t.rep Y) 3).card := by
    by_contra! narrow
    exact kept (mem_filter.mpr ⟨key,two,third,narrow⟩)
  obtain ⟨base,w,wx,wc,a,am,edge,many,sub,peak⟩ :=
    short_first_scores free (by omega) reg uv hr fit first length roots sec third four (by omega)
  let B := ball (fun x y=>D y x) C a 2
  have n := RetainedShellScores.increments (W:=C) (A:=B) (B:=∅) (C:=∅)
    (f:=fun a=>surplus (3*r) (ball D V a 3).card) (n:=3) (i:=2) (j:=0) (k:=0)
    sub (empty_subset _) (empty_subset _)
    (fun v vm=>by have h:=base v vm; simp [surplus,show 3*r<(ball D V v 3).card by omega]; omega)
    (fun v vm=>by have h:=peak v vm; simp [surplus,show 3*r<(ball D V v 3).card by omega]; omega)
    (fun _ h=>False.elim (notMem_empty _ h)) (fun _ h=>False.elim (notMem_empty _ h))
  change 3≤B.card at many
  simp only [card_empty,Nat.zero_mul,Nat.add_zero] at n
  have bill : 3*C.card+6≤∑a∈C,surplus (3*r) (ball D V a 3).card := by omega
  obtain ⟨_,_,_,_,_,_,_,bank,_⟩ := narrow_cycle free (by omega) reg uv fit hr sec third
  have cap K (km : K∈booked t) : omissions D V K r≤2 := by
    obtain ⟨Z,zm,rfl⟩ := mem_image.mp km; have := t.loss _ (t.assigned _ zm); omega
  have root K (km : K∈booked t) : ∀v∈K,Rooted D V v K := by
    rcases mem_image.mp km with ⟨Z,zm,rfl⟩
    exact t.rooted _ (t.assigned _ zm)
  have bookedHere : C∈booked t := id ▸ mem_image_of_mem t.pay key
  have loss : omissions D V C r=1 := by unfold omissions; rw [width]; omega
  have bound := stock_times_capacity (f:=2) t bookedHere (fun v vm=>primary_two_turns (d:=1) free (by omega) reg uv fit
    (by omega) bookedHere vm first (by omega) sec (fun z zm=>((bank z zm).1.one z zm).le) root cap (by omega))
  rw [loss] at bound
  norm_num at bound
  exact (show ((3*C.card+6:ℕ):ℚ)≤∑v∈C,(surplus (3*r) (ball D V v 3).card:ℚ) by exact_mod_cast bill).trans bound

#print axioms booked_short_price
end LeanCH.BR.LowShellCycleSelection
