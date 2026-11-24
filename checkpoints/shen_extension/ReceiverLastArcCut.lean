import checkpoints.shen_extension.ReceiverParentDebt

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 BRsub AvoidedHeadQuota

/-- Preserve a last arc into g precisely when its tail sees some member
of Z. All columns other than g retain their native arcs. -/
def lastCut (D : CH.Digraph) (g : ℕ) (Z : Finset ℕ) : CH.Digraph := fun a b=>
  if b=g ∧ (∀z∈Z,D a z≠true) then false else D a b

theorem lastCut_sub {D g Z} (a b) (arc : lastCut D g Z a b=true) : D a b=true := by
  unfold lastCut at arc
  split at arc <;> simp_all

/-- A bank whose rows all reach b leaves no short b-to-g return once
the unprotected last arcs at g are withdrawn. -/
theorem lastCut_clear {D V H q g b Z} (free : QFree D V q) (hv : H⊆V)
    (bv : b∈H) (ne : b≠g) (zv : Z⊆V) (toB : ∀z∈Z,D z b=true) :
    g∉ball (lastCut D g Z) H b (q-1) := by
  classical
  intro ret
  obtain ⟨_,k,le,w⟩ := mem_ball.mp ret
  cases k with
  | zero => cases w; exact ne rfl
  | succ k =>
    obtain ⟨a,path,_,enter⟩ := w.unsnoc
    have charged : ∃z∈Z,D a z=true := by
      by_contra no
      have blocked : g=g ∧ ∀z∈Z,D a z≠true := ⟨rfl,fun z zm az=>no ⟨z,zm,az⟩⟩
      rw [lastCut,ite_eq_left blocked] at enter
      contradiction
    obtain ⟨z,zm,az⟩ := charged
    have old := Walk.mono hv (walk_sub (lastCut_sub (D:=D) (g:=g) (Z:=Z)) path)
    exact free a (k+1+1) (by omega) (by omega)
      (.step (zv zm) az (.step (hv bv) (toB z zm) old))

theorem lastCut_row {D H Z g a} :
    outN (lastCut D g Z) H a=
      if (∀z∈Z,D a z≠true) then (outN D H a).erase g else outN D H a := by
  classical
  split
  next off =>
    ext u
    by_cases eq : u=g
    · subst u
      have blocked : g=g ∧ ∀z∈Z,D a z≠true := ⟨rfl,off⟩
      have zero : lastCut D g Z a g=false := ite_eq_left blocked
      simp [mem_outN,zero]
    · have allowed : ¬ (u=g ∧ ∀z∈Z,D a z≠true) := fun h=>eq h.1
      have keep : lastCut D g Z a u=D a u := ite_eq_right allowed
      simp [mem_outN,mem_erase,keep,eq]
  next hit =>
    ext u
    have allowed : ¬ (u=g ∧ ∀z∈Z,D a z≠true) := fun h=>hit h.2
    have keep : lastCut D g Z a u=D a u := ite_eq_right allowed
    simp only [mem_outN,keep]

/-- Install an actual missing shortcut after paying all the last-arc
cuts. With a surplus row left over the boundary order is impossible. -/
theorem blocked_lastCut {D V H q t g b Z} (free : QFree D V q) (hv : H⊆V)
    (cut : 1≤q) (size : H.card=q*t+1) (br : Compose.Boundary.BoundaryRegular q t)
    (gm : g∈H) (bm : b∈H) (ne : b≠g) (miss : D g b≠true)
    (zv : Z⊆V) (toB : ∀z∈Z,D z b=true) (hit : ∃z∈Z,D g z=true)
    (short : t≤(outN D H g).card+1)
    (others : ∀a∈H,a≠g → t≤(outN D H a).card)
    (excess : ∃a∈H,t<(outN D H a).card ∧
      (D a g≠true ∨ (∃z∈Z,D a z=true) ∨ t+2≤(outN D H a).card))
    (paid : ∀a∈H,(∀z∈Z,D a z≠true) → D a g=true → t+1≤(outN D H a).card) : False := by
  classical
  let K:=lastCut D g Z
  have never : ¬∀z∈Z,D g z≠true := by obtain ⟨z,zm,gz⟩ := hit; exact fun deny=>deny z zm gz
  have keep : outN K H g=outN D H g := by rw [lastCut_row,ite_eq_right never]
  have budgets (a) (am : a∈H) (quota : t≤(outN D H a).card) :
      t≤(outN K H a).card ∧ (t<(outN D H a).card →
        (D a g≠true ∨ (∃z∈Z,D a z=true) ∨ t+2≤(outN D H a).card) →
        t<(outN K H a).card) := by
    change _≤(outN (lastCut D g Z) H a).card ∧ (_ → _ → _<(outN (lastCut D g Z) H a).card)
    rw [lastCut_row]
    split
    next off =>
      by_cases edge : g∈outN D H a
      · have debit := paid a am off (mem_outN.mp edge).2
        have := card_erase_add_one edge
        refine ⟨by omega,?_⟩
        intro _ protectedRow
        rcases protectedRow with avoids|⟨z,zm,az⟩|extra
        · exact (avoids (mem_outN.mp edge).2).elim
        · exact (off z zm az).elim
        · omega
      · rw [erase_eq_of_notMem edge]; exact ⟨quota,fun high _=>high⟩
    next => exact ⟨quota,fun high _=>high⟩
  obtain ⟨x,xm,hi,uncharged⟩ := excess
  have forced := short_return (D:=K) (V:=H) (H:=H)
    (qfree_sub lastCut_sub (free.mono_set hv)) (Subset.rfl) cut size br gm bm
    (fun edge=>miss (lastCut_sub _ _ edge)) (keep ▸ short)
    (fun a am ne=>(budgets a am (others a am ne)).1)
    ⟨x,xm,(budgets x xm hi.le).2 hi uncharged⟩
  exact lastCut_clear free hv bm ne zv toB forced

#print axioms lastCut_clear
#print axioms blocked_lastCut
end LeanCH.BR.LabelledCompromiseRecipe
