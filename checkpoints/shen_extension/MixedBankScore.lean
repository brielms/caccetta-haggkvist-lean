import checkpoints.shen_extension.MixedBankPayments
import checkpoints.shen_extension.CycleLayerTransport
import checkpoints.shen_extension.ShellProfileCapacity

namespace LeanCH.BR.MixedBankScore
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock ShellCycleSupply
open RetainedLayerCapacity GuardedLayerGrowth

/-- Capacity of the punctured third ball with two retained heads per row. -/
def fourthRoom (r a b : ℕ) : Prop :=
  let m := b-1
  let h := a-1
  m*(m+1)<(m-h)*16+(h-r)*(2*r+10)+r*(4*r)

/-- Capacity of the punctured fourth ball. The marked first-bank rows
keep all of their third balls, including the actual subsequent layers. -/
def fifthRoom (r a b e : ℕ) : Prop :=
  let d := 3
  let m := e-1
  let h := b-1
  let k := a-1
  m*(m+1)<(m-h)*(2*(3*d+1))+(h-k)*(2*(r+2*d))+(k-r)*(4*r)+r*(2*(e+3-r))

def Capacity (r : ℕ) : Prop :=
  (∀a∈Icc (2*r+2) (3*r+1),fourthRoom r a (3*r+1)) ∧
  ∀a∈Icc (2*r) (2*r+1),∀b∈Icc (3*r) (3*r+1),∀e∈Icc (4*r-1) (4*r),
    (a=2*r+1 → b=3*r) → fifthRoom r a b e
instance (r a b : ℕ) : Decidable (fourthRoom r a b) := by unfold fourthRoom; infer_instance
instance (r a b e : ℕ) : Decidable (fifthRoom r a b e) := by unfold fifthRoom; infer_instance
instance (r : ℕ) : Decidable (Capacity r) := by unfold Capacity; infer_instance

private theorem fifth {D V q r v a b e} (free : QFree D V q) (reg : OutEq r D V)
    (hq : 7≤q) (hr : 7≤r) (fit : r≤q+1) (uv : v∈V)
    (two : (ball D V v 2).card=a) (three : (ball D V v 3).card=b) (four : (ball D V v 4).card=e)
    (useFifth : fifthRoom r a b e)
    (narrow : 4*r-1≤e) (near : ∀u∈V,2*r≤(ball D V u 2).card)
    (stock : ∀x∈outN D V v,e+3-r≤(ball D V x 3).card) : 5*r-3≤(ball D V v 5).card := by
  let d := 3
  have rank : d=2 ∨ d=3 := Or.inr rfl
  have slack : 5*r-3+d≤(ball D V v 4).card+r+1 := by rw [four]; dsimp [d]; omega
  apply CycleLayerTransport.fifth (d:=d) free (by omega) reg uv rank (by omega) (by omega) slack near stock
  dsimp only
  rw [two,three,four]
  exact useFifth

/-- A complete first-layer bank with a small third ball of its root has
a strict two-unit score gain on every physical row of the bank. -/
theorem complete {D V q r s} (free : QFree D V q) (reg : OutEq r D V)
    (hq : 7≤q) (hr : 7≤r) (fit : r≤q+1) (sv : s∈V) (cap : Capacity r)
    (near : ∀u∈V,2*r≤(ball D V u 2).card)
    (low : ∀u∈V,4*r-1≤(ball D V u 4).card)
    (thin : (N2 D V s).card+1=r)
    (sb : 3*r≤(ball D V s 3).card) (st : (ball D V s 3).card≤3*r+1) :
    ∀v∈outN D V s,Rooted D V v (outN D V s) ∧
      7*r+3≤(ball D V v 3).card+(ball D V v 4).card := by
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) sv
  rw [reg s sv] at one
  have two := @card_B2 D V s
  have narrow : (ball D V s 2).card=2*r := by omega
  have pay := narrow_supply free (by omega) reg sv fit thin
  have base (v) (vm : v∈outN D V s) : (ball D V s 4).card+3-r≤(ball D V v 3).card := by
    have h := (pay v vm).2 2 (by omega)
    simp only [Nat.reduceAdd] at h
    omega
  intro v vm
  refine ⟨(pay v vm).1,?_⟩
  have a := base v vm
  have b := low v (outN_subset vm)
  have c := low s sv
  by_cases hi : 4*r+1≤(ball D V s 4).card
  · omega
  have guard := cap.2 (2*r) (mem_Icc.mpr ⟨le_rfl,by omega⟩) _ (mem_Icc.mpr ⟨sb,st⟩) _ (mem_Icc.mpr ⟨c,by omega⟩) (by omega)
  have large := fifth free reg hq hr fit sv narrow rfl rfl guard c near base
  have next := (pay v vm).2 3 (by omega)
  simp only [Nat.reduceAdd] at next
  omega

theorem low_score_floor {D V q r} (free : QFree D V q) (reg : OutEq r D V)
    (hq : 7≤q) (hr : 7≤r) (fit : r≤q+1) (bounds : FourthRoom r) (cap : Capacity r)
    (host : V.card≤7*r) : ∀u∈V,7*r+1≤(ball D V u 3).card+(ball D V u 4).card := by
  let score := fun u=>(ball D V u 3).card+(ball D V u 4).card
  have near u (uv : u∈V) := second_floor free (by omega : 4≤q) reg (by omega : 0<r) (by omega) uv
  have floor3 u (uv : u∈V) := diagonal_third (k:=q-2) free uv reg hq (by omega) fit (by omega) (by omega) bounds.1
  have floor4 u (uv : u∈V) := diagonal_fourth free hq (by omega) fit bounds reg uv
  apply MixedBankPayments.no_low (i:=3) (j:=4) (c:=1) (gain:=2) free (by omega) (by omega) (by omega) reg
    (by omega) score (fun _ _=>rfl) (fun flag=>if flag then 2 else 1) (fun flag=>if flag then 2 else 1)
    (by intro flag; cases flag <;> decide) (by simpa only [ite_true,ite_false,Bool.false_eq_true,Nat.reduceAdd,Nat.reducePow,Nat.reduceMul] using (show 12<r*2 by omega))
  intro u uv unpaid
  change (ball D V u 3).card+(ball D V u 4).card<7*r+1 at unpaid
  have lb2 := near u uv
  have lb3 := floor3 u uv
  have lb4 := floor4 u uv
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg u uv] at one
  have two := @card_B2 D V u
  have three := @card_B3 D V u
  have thin : (ball D V u 2).card≤2*r+1 := by
    by_cases short : (ball D V u 3).card≤3*r
    · exact ShellProfileCapacity.short_second free hq (by omega) fit reg uv short
    have middle : (ball D V u 3).card=3*r+1 := by omega
    by_contra! wide
    have within := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    have block := cap.1 (ball D V u 2).card (mem_Icc.mpr ⟨by omega,by omega⟩)
    have next := CycleLayerTransport.fourth (d:=2) (target:=4*r) free hq reg uv (.inl rfl)
      (by omega) (by omega) (by omega) near (by dsimp only; rw [middle]; exact block)
    omega
  have ext_eq := head_exterior free (by omega : 2≤q) uv
  by_cases narrow : (ball D V u 2).card=2*r
  · refine ⟨true,outN_subset,reg u uv,?_,complete free reg hq hr fit uv cap near floor4 (by omega) lb3 (by omega),?_⟩
    · change omissions D V (outN D V u) r≤1
      unfold omissions; rw [ext_eq]; omega
    · dsimp [score]; omega
  have wide : (ball D V u 2).card=2*r+1 := by omega
  have b3 : (ball D V u 3).card=3*r := by
    by_contra! no
    exact ShellProfileCapacity.triple_excess free (by omega) fit reg uv wide (by omega) (by omega)
  have ys : (N2 D V u).card=r := by omega
  have zs : (N3 D V u).card+1=r := by omega
  rcases SecondaryCycleCohort.cohort free (by omega) (by omega) fit reg uv ys zs with ⟨s,sm,row,next,child,_⟩|primary
  · have sv := outN_subset sm
    have small := floor3 s sv
    have origin := head_exterior free (by omega : 2≤q) sv
    have smallBank : (N2 D V s).card+1=r := by rw [next]; exact zs
    have paid := complete free reg hq hr fit sv cap near floor4 smallBank small (by omega)
    refine ⟨false,?_,ys,?_,?_,?_⟩
    · exact fun _ hm=>N2_subV hm
    · change omissions D V (N2 D V u) r≤1
      unfold omissions; rw [←row,origin]; omega
    · rw [row] at paid
      exact paid
    · dsimp [score]; omega
  · have first (v) (vm : v∈outN D V u) : (ball D V u 4).card+3-r≤(ball D V v 3).card := by
      have := (primary v vm).2
      omega
    have guard := cap.2 (2*r+1) (mem_Icc.mpr ⟨by omega,le_rfl⟩) (3*r)
      (mem_Icc.mpr ⟨le_rfl,by omega⟩) _ (mem_Icc.mpr ⟨lb4,by omega⟩) (fun _=>rfl)
    have five := fifth free reg hq hr fit uv wide b3 rfl guard lb4 near first
    refine ⟨true,outN_subset,reg u uv,?_,?_,?_⟩
    · change omissions D V (outN D V u) r≤1
      unfold omissions; rw [ext_eq]; omega
    · intro v vm
      have cr := (primary v vm).1
      have hit := CycleLayerTransport.transfer (k:=2) free (by omega) (by omega) fit reg uv ys zs cr (by omega)
      simp only [Nat.reduceAdd] at hit
      have high := first v vm
      exact ⟨cr,by dsimp [score]; omega⟩
    · dsimp [score]; omega

#print axioms complete
#print axioms low_score_floor
end LeanCH.BR.MixedBankScore
