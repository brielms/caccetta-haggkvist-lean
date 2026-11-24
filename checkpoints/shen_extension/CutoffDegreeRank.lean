import checkpoints.shen_extension.BankDescentFrontier
import checkpoints.shen_extension.ReturnArcRecurrence

namespace LeanCH.BR.Closure.CutoffDegreeRank
open Finset BRq2 BRq3 BR45 DeficitLevels BankDescentFrontier

/-- Actual counterexample parameters, with graph and carrier as witnesses. -/
def Realized (q s n : ℕ) : Prop :=
  ∃ (D : CH.Digraph) (V : Finset ℕ), V.Nonempty ∧ V.card=n ∧ QFree D V q ∧
    n≤q*s ∧ ∀x∈V,s≤(outN D V x).card

/-- Compare degree first, order second, and at fixed degree and order
prefer the larger cutoff. Every realized positive-degree cutoff is < n. -/
def Ranked (base q s n : ℕ) : Prop :=
  base≤q ∧ ∀ r j m, base≤r → Realized r j m →
    s≤j ∧ (j=s → n≤m ∧ (m=n → r≤q))

private theorem cutoff_lt {q s n} (hq : 1≤q) (ex : Realized q s n) : q<n := by
  obtain ⟨D,V,live,sz,safe,ord,deg⟩ := ex
  have pos := card_pos.mpr live
  have sp : s≠0 := by intro eq; rw [eq,Nat.mul_zero] at ord; omega
  have one (x) (xv : x∈V) : 1≤(outN D V x).card := by have := deg x xv; omega
  have lower := dt_size hq (ball_q_one q hq) safe one live
  simp only [Nat.mul_one] at lower
  omega

private theorem choose_rank {base s n} (hb : 2≤base) (start : Realized base s n) :
    ∃q j m, j≤s ∧ Realized q j m ∧ Ranked base q j m := by
  classical
  let P (j : ℕ) := ∃r m,base≤r ∧ Realized r j m
  have any : ∃j,P j := ⟨s,base,n,le_rfl,start⟩
  let j := Nat.find any
  have jm : ∀i,P i → j ≤ i := fun _ => Nat.find_min' any
  obtain ⟨r₀,m₀,br₀,ex₀⟩ := Nat.find_spec any
  let N (m : ℕ) := ∃r,base≤r ∧ Realized r j m
  have someN : ∃m,N m := ⟨m₀,r₀,br₀,ex₀⟩
  let m := Nat.find someN
  have mm : ∀i,N i → m ≤ i := fun _ => Nat.find_min' someN
  obtain ⟨r₁,br₁,ex₁⟩ := Nat.find_spec someN
  let K (k : ℕ) := ∃r,base≤r ∧ Realized r j m ∧ m-r=k
  have someK : ∃k,K k := ⟨m-r₁,r₁,br₁,ex₁,rfl⟩
  obtain ⟨q,bq,exq,gap⟩ := Nat.find_spec someK
  have mx := cutoff_lt (by omega : 1≤q) exq
  refine ⟨q,j,m,jm s ⟨base,n,le_rfl,start⟩,exq,bq,?_⟩
  intro r i u br realized
  refine ⟨jm i ⟨r,u,br,realized⟩,?_⟩
  rintro rfl
  refine ⟨mm u ⟨r,br,realized⟩,?_⟩
  rintro rfl
  have rx := cutoff_lt (by omega : 1≤r) realized
  have cmp := Nat.find_min' someK (show K (m-r) from ⟨r,br,realized,rfl⟩)
  omega

/-- A bad graph supplies a single source with all native transition rules
and the full rank against edits that also change cutoff. -/
theorem from_input {D V base s} (hb : 2≤base) (free : QFree D V base) (live : V.Nonempty)
    (ord : V.card≤base*s) (deg : ∀x∈V,s≤(outN D V x).card) :
    ∃ q d, d+1≤s ∧ ∃ (O : Origin q (d+1)) (st : State), Ranked base q (d+1) O.V.card ∧
      PackingFrontier.Frontier O st ∧ UnitLoopCapstone.AlternativesWithLoops O st ∧ BankRules O ∧
      ((h : q=3) → DenseArc.FanReturns O.G O.V d ∧ DenseArc.FourEscape (h ▸ O) ∧
                     PackedEscape (h ▸ O) ∧ TriangleRules (h ▸ O)) := by
  obtain ⟨q,j,m,js,ex,rank⟩ := choose_rank hb (show Realized base s V.card from ⟨D,V,live,rfl,free,ord,deg⟩)
  obtain ⟨G,W,wl,sz,safe,bound,degree⟩ := ex
  obtain ⟨d,le,O,st,fr,alt,bank,three⟩ := recursive_banks (hb.trans rank.1) safe wl (sz ▸ bound) degree
  have exO : Realized q (d+1) O.V.card := ⟨O.G,O.V,O.ne,rfl,O.free,O.order,O.deg⟩
  have first := rank.2 q (d+1) O.V.card rank.1 exO
  have eq : d+1=j := le.antisymm first.1
  have os := O.least G W safe (eq ▸ degree) wl
  have eqn : O.V.card=m := by have lo := (first.2 eq).1; omega
  exact ⟨q,d,le.trans js,O,st,by simpa only [eq,eqn] using rank,fr,alt,bank,three⟩

/-- Deleting T or editing rows may raise the cutoff to q+1 on the next
induction step. At least one original (q+1)-cycle survives on W whenever
the real retained degrees and order pay for the step. -/
theorem surviving_edit {base q s} (O : Origin q s) (hb : 2≤base)
    (rank : Ranked base q s O.V.card) {E : CH.Digraph} {W : Finset ℕ} {d} (size : W.card≤O.V.card) (safe : QFree E W q) (live : W.Nonempty)
    (below : d≤s) (budget : W.card≤(q+1)*d) (paid : ∀x∈W,d≤(outN E W x).card) :
    ∃M⊆W, M.card=q+1 ∧ OutEq 1 E M := by
  have fail : ¬QFree E W (q+1) := by
    intro f
    have compare := rank.2 (q+1) d W.card (by have := rank.1; omega)
      ⟨E,W,live,rfl,f,budget,paid⟩
    have eq := below.antisymm compare.1
    have sz := size.antisymm (compare.2 eq).1
    have impossible := (compare.2 eq).2 sz
    omega
  unfold QFree at fail
  push Not at fail
  obtain ⟨x,k,pos,upper,walk⟩ := fail
  have kq : k=q+1 := by
    have no : ¬k≤q := fun le => safe x k pos le walk
    omega
  subst k
  obtain ⟨M,sub,sz,mdeg⟩ := boundary_closed_walk_support safe walk
  have hq := hb.trans rank.1
  have reg := dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (safe.mono_set sub) mdeg (by simpa using sz)
  exact ⟨M,sub,sz,reg.1⟩

theorem surviving_cycle {base q s} (O : Origin q s) (hb : 2≤base)
    (rank : Ranked base q s O.V.card) {W : Finset ℕ} {d} (wv : W⊆O.V) (live : W.Nonempty)
    (below : d≤s) (budget : W.card≤(q+1)*d) (paid : ∀x∈W,d≤(outN O.G W x).card) :
    ∃M⊆W, M.card=q+1 ∧ OutEq 1 O.G M :=
  surviving_edit O hb rank (card_le_card wv) (O.free.mono_set wv) live below budget paid

/-- On every proper carrier use the *actual* certified girth, even when
its cutoff is larger than the original one. -/
theorem light_at_cutoff {base q s r} (O : Origin q s) (rank : Ranked base q s O.V.card)
    {W : Finset ℕ} (wv : W⊆O.V) (proper : W.card<O.V.card) (live : W.Nonempty)
    (br : base≤r) (safe : QFree O.G W r) :
    ∃x∈W, r*(outN O.G W x).card+1≤W.card := by
  obtain ⟨x,xw,minimum⟩ := W.exists_min_image (fun x => (outN O.G W x).card) live
  have small : (outN O.G W x).card<s := by
    by_contra! ge
    exact proper.not_ge (O.least O.G W (O.free.mono_set wv) (fun v hv => ge.trans (minimum v hv)) live)
  refine ⟨x,xw,?_⟩
  by_contra! short
  have input : Realized r (outN O.G W x).card W.card :=
    ⟨O.G,W,live,rfl,safe,by omega,minimum⟩
  have le := (rank.2 _ _ _ br input).1
  omega

/-- A vertex set within the exact numerical budget cannot hit all original
shortest cycles. The unused labels support an actual induced cycle. -/
theorem avoid_set {base q s} (O : Origin q s) (hb : 2≤base) (rank : Ranked base q s O.V.card)
    {T : Finset ℕ} (tv : T⊆O.V) (cost : q*T.card+O.V.card≤(q+1)*s) :
    ∃M⊆O.V\T, M.card=q+1 ∧ OutEq 1 O.G M := by
  have total := card_sdiff_add_card_eq_card tv
  have ge : s<O.V.card := by
    obtain ⟨a,av⟩ := O.ne
    have inc : insert a (outN O.G O.V a)⊆O.V := insert_subset av outN_subset
    have ne : a∉outN O.G O.V a := fun ha => loopfree O.free (by have := rank.1; omega) av (mem_outN.mp ha).2
    have cmp := card_le_card inc
    rw [card_insert_of_notMem ne] at cmp
    have dg := O.deg a av
    omega
  have width : T.card≤s := by
    by_contra! big
    have mul := Nat.mul_le_mul_left q big.le
    rw [Nat.add_mul,Nat.one_mul] at cost
    omega
  have pay (x) (hx : x∈O.V\T) : s-T.card≤(outN O.G (O.V\T) x).card := by
    have sub : outN O.G O.V x⊆outN O.G (O.V\T) x∪T := by
      intro z hz
      by_cases zt : z∈T
      · exact mem_union_right _ zt
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨(mem_outN.mp hz).1,zt⟩,(mem_outN.mp hz).2⟩)
    have cap := (card_le_card sub).trans (card_union_le _ _)
    have deg := O.deg x (mem_sdiff.mp hx).1
    omega
  apply surviving_cycle O hb rank sdiff_subset (card_pos.mp (by omega)) (Nat.sub_le _ _) _ pay
  rw [Nat.mul_sub,Nat.add_mul q 1 T.card,Nat.one_mul]
  omega

#print axioms light_at_cutoff
#print axioms avoid_set
#print axioms from_input
#print axioms surviving_edit
#print axioms surviving_cycle
end LeanCH.BR.Closure.CutoffDegreeRank
