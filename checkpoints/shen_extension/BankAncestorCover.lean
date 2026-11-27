import checkpoints.shen_extension.BypassBankReplay
import LeanCH.BR.BRFiniteWalk

/-! Cover a labelled set by ancestors in a graph where every sufficiently
large set contains two heads of one row. -/

namespace LeanCH.BR.BankAncestorCover
open Finset BRq2 BRq3 BR45 BypassRepair

/-- Above the threshold two labels in the set have an actual common parent. -/
def PairAbove (D : CH.Digraph) (V : Finset ℕ) (a : ℕ) : Prop :=
  ∀ T ⊆ V, a < T.card →
    ∃ p ∈ V, ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ D p u = true ∧ D p v = true

/-- Select a parent for two heads at a time; once at most `a` heads remain,
use any predecessor for each of them. -/
theorem one_round {D V a} (pair : PairAbove D V a)
    (pred : ∀ v ∈ V, ∃ p ∈ V, D p v = true) (T : Finset ℕ) (sub : T ⊆ V) :
    ∃ P ⊆ V, 2*P.card ≤ T.card+a ∧ ∀ v ∈ T, ∃ p ∈ P, D p v = true := by
  classical
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    by_cases small : T.card ≤ a
    · let pick (i : ℕ) := if h : i ∈ V then (pred i h).choose else i
      have spec (i) (hi : i ∈ T) : pick i ∈ V ∧ D (pick i) i = true := by
        simpa [pick, sub hi] using (pred i (sub hi)).choose_spec
      refine ⟨T.image pick, ?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨v,hv,rfl⟩ := mem_image.mp hp
        exact (spec v hv).1
      · have := card_image_le (s := T) (f := pick)
        omega
      · intro v hv
        exact ⟨pick v, mem_image_of_mem _ hv,(spec v hv).2⟩
    · obtain ⟨p,pv,u,ut,v,vt,ne,pu,pv'⟩ := pair T sub (by omega)
      let B : Finset ℕ := {u,v}
      have bt : B ⊆ T := insert_subset ut (singleton_subset_iff.mpr vt)
      have btwo : B.card = 2 := card_pair ne
      have rem := card_sdiff_add_card_eq_card bt
      rw [btwo] at rem
      have lt : T \ B ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, fun eq => by
        rw [eq] at rem; omega⟩
      obtain ⟨P,Pv,bound,all⟩ := ih (T \ B) lt (sdiff_subset.trans sub)
      refine ⟨insert p P,insert_subset pv Pv,?_,?_⟩
      · have := card_insert_le p P
        omega
      · intro z zt
        by_cases zb : z ∈ B
        · rcases (show z = u ∨ z = v by simpa [B] using zb) with eq | eq
          · exact ⟨p,mem_insert_self ..,eq ▸ pu⟩
          · exact ⟨p,mem_insert_self ..,eq ▸ pv'⟩
        · obtain ⟨w,wp,wz⟩ := all z (mem_sdiff.mpr ⟨zt,zb⟩)
          exact ⟨w,mem_insert_of_mem wp,wz⟩

/-- After `l` rounds at most `a` ancestors cover the designated targets
by walks of exactly `l` steps. -/
theorem ancestor_cover {D V a} (pair : PairAbove D V a)
    (pred : ∀ v ∈ V, ∃ p ∈ V, D p v = true) (l : ℕ) (T : Finset ℕ)
    (sub : T ⊆ V) (budget : T.card < a+2^l) :
    ∃ P ⊆ V, P.card ≤ a ∧ ∀ v ∈ T, ∃ p ∈ P, Walk D V p v l := by
  induction l generalizing T with
  | zero =>
    refine ⟨T,sub,by simpa using budget,fun v hv => ⟨v,hv,.refl v⟩⟩
  | succ l ih =>
    obtain ⟨B,bs,size,covered⟩ := one_round pair pred T sub
    rw [pow_succ] at budget
    obtain ⟨P,ps,small,paths⟩ := ih B bs (by omega)
    refine ⟨P,ps,small,?_⟩
    intro v hv
    obtain ⟨b,hb,bv⟩ := covered v hv
    obtain ⟨p,hp,walk⟩ := paths b hb
    exact ⟨p,hp,walk.snoc (sub hv) bv⟩

/-- A nonempty carrier covered by `a` exact-length ancestors contains a
positive return in at most `a*l` steps. -/
theorem cover_return {D : CH.Digraph} {V P : Finset ℕ} {q a l : ℕ} (free : QFree D V q)
    (live : V.Nonempty) (sub : P ⊆ V) (few : P.card ≤ a) (pos : 0 < l)
    (paths : ∀ v ∈ V, ∃ p ∈ P, Walk D V p v l) : q < a*l := by
  classical
  by_contra! short
  let R : CH.Digraph := fun u v => decide (Walk D V v u l)
  have liftPath {u v d} (p : Walk R P u v d) : Walk D V v u (d*l) := by
    induction p with
    | refl u => simpa using (Walk.refl (D := D) (W := V) u)
    | @step u v w d vp uv follow ih =>
      have seg : Walk D V v u l := of_decide_eq_true uv
      simpa [Nat.succ_mul] using ih.append seg
  have smallFree : QFree R P P.card := by
    intro u d dp ds w
    exact free u (d*l) (Nat.mul_pos dp pos)
      ((Nat.mul_le_mul_right l (ds.trans few)).trans short) (liftPath w)
  obtain ⟨v,vv⟩ := live
  obtain ⟨p,pp,_⟩ := paths v vv
  obtain ⟨z,zp,sink,_,_,_⟩ := reach_sink_of_card smallFree (le_refl _) pp
  obtain ⟨w,wp,back⟩ := paths z (sub zp)
  exact sink w wp (decide_eq_true back)

/-- A lower-degree obstruction provides the required common parents at
every bank size. -/
theorem source_pair {q s : ℕ} (X : ShenMinimumOrder.Source q s) (none : NoHost q (s-1))
    (hq : 1 ≤ q) (hs : 2 ≤ s) {a : ℕ} (order : X.V.card = q*(s-1)+(a+1)) :
    PairAbove X.D X.V a := by
  classical
  intro T tv big
  obtain ⟨B,bt,bc⟩ := exists_subset_card_eq (show a+1 ≤ T.card by omega)
  have bv := bt.trans tv
  have size : (X.V \ B).card = q*(s-1) := by rw [card_sdiff_of_subset bv, bc, order]; omega
  have pos : 0 < q*(s-1) := Nat.mul_pos (by omega) (by omega)
  have fail := none X.D (X.V \ B) (card_pos.mp (by omega)) size.le (X.free.mono_set sdiff_subset)
  push Not at fail
  obtain ⟨p,pl,low⟩ := fail
  have pv := (mem_sdiff.mp pl).1
  have split := card_outN_union (D := X.D) (show Disjoint B (X.V \ B) from disjoint_sdiff) p
  rw [union_sdiff_of_subset bv] at split
  have deg := X.degree p pv
  obtain ⟨u,hu,v,hv,ne⟩ := one_lt_card.mp (show 1 < (outN X.D B p).card by omega)
  exact ⟨p,pv,u,bt (outN_subset hu),v,bt (outN_subset hv),ne,(mem_outN.mp hu).2,(mem_outN.mp hv).2⟩

/-- At every bank size `a+1`, a source of order less than `a+2^l` has
cutoff strictly less than `a*l`. -/
theorem bank_return_bound {q s : ℕ} (X : ShenMinimumOrder.Source q s) (none : NoHost q (s-1))
    (hq : 2 ≤ q) (hs : 2 ≤ s) {a l : ℕ} (order : X.V.card = q*(s-1)+(a+1))
    (pos : 0 < l) (budget : X.V.card < a+2^l) : q < a*l := by
  have pair := source_pair X none (by omega) hs order
  have pred (v) (hv : v ∈ X.V) : ∃ p ∈ X.V, X.D p v = true := by
    obtain ⟨p,pv,pw,_,_⟩ := ShenCycleSuccessor.fixed_parent X hq (by omega) hv
    exact ⟨p,pv,pw⟩
  obtain ⟨P,sub,small,paths⟩ := ancestor_cover pair pred l X.V (Subset.rfl) budget
  exact cover_return X.free X.nonempty sub small pos paths

#print axioms bank_return_bound

/-- With `a+1` deleted labels, the lower-degree interval must contain
at least `2^(q/a)-1` labels. The quotient is natural-number division. -/
theorem bank_size_bound {q s : ℕ} (X : ShenMinimumOrder.Source q s) (none : NoHost q (s-1))
    (hq : 2 ≤ q) (hs : 2 ≤ s) {a : ℕ} (order : X.V.card = q*(s-1)+(a+1))
    (positive : 0 < a) (fit : a ≤ q) : 2^(q/a) ≤ q*(s-1)+1 := by
  by_contra! small
  have radius : 0 < q/a := Nat.div_pos fit positive
  have cost := bank_return_bound X none hq hs order radius (by omega)
  exact (Nat.not_lt_of_ge (Nat.mul_div_le q a)) (by simpa [Nat.mul_comm] using cost)

#print axioms bank_size_bound

/-- Read the exponent from the selected bank on the same minimum-order
source that supplies the lower-degree induction hypothesis. -/
theorem marked_bank_bound {q s : ℕ} {X : ShenMinimumOrder.Source q s}
    {m : BypassBankReplay.Cell} (cell : BypassBankReplay.Marked X m) (none : NoHost q (s-1))
    (hq : 2 ≤ q) (hs : 2 ≤ s) (room : X.V.card ≤ q*s) :
    2^(q/(m.bank.card-1)) ≤ q*(s-1)+1 := by
  have lo := BypassBankReplay.order_floor none hs X.free X.nonempty X.degree
  have size := cell.size
  have expand : q*s = q*(s-1)+q := by
    calc q*s = q*((s-1)+1) := congrArg (q*·) (by omega)
         _ = _ := by rw [Nat.mul_add,Nat.mul_one]
  exact bank_size_bound X none hq hs (by omega) (by omega) (by omega)

#print axioms marked_bank_bound
end LeanCH.BR.BankAncestorCover

