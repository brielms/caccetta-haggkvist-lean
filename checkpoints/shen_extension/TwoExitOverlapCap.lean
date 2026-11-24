import checkpoints.pair_tilt_20261119.TwoExitBlockers
import checkpoints.shen_extension.PortParentInvariant

namespace LeanCH.BR.Closure.TwoExitOverlapCap
open Finset BRq2 BRq3 BR45 WeightedSD TwoExit

variable {q : ℕ} {E : CH.Digraph} {V R H : Finset ℕ} {w : ℕ→ℚ} {c : ℚ} {a u v : ℕ}

/-- One missing reverse arc places the entire closed intersection inside the first open row. -/
private theorem one_side (pos : ∀i∈V,0<w i) (flat : ∀i∈V,WeightedSD.row q E V w i=c)
    (uv : u∈V) (ne : u≠v) (missing : ¬E v u=true) :
    (q:ℚ)*mass (insert u (outN E V u) ∩ insert v (outN E V v)) w+w u≤c := by
  have sub : insert u (outN E V u) ∩ insert v (outN E V v) ⊆ outN E V u := by
    intro k hk
    obtain ⟨left,right⟩ := mem_inter.mp hk
    rcases mem_insert.mp left with rfl|h
    · exact False.elim (missing (mem_outN.mp ((mem_insert.mp right).resolve_left ne)).2)
    · exact h
  have m : mass _ w≤mass _ w := sum_le_sum_of_subset_of_nonneg sub
    (fun i hi _=>(pos i (mem_outN.mp hi).1).le)
  have row := flat u uv
  rw [WeightedSD.row,outW_eq_mass] at row
  linarith [mul_le_mul_of_nonneg_left m (Nat.cast_nonneg q : (0:ℚ)≤q)]

/-- Distinct vertices cannot both lie in the closed intersection. At least one
exit weight is therefore deducted from the flat-row overlap budget. -/
theorem overlap_cap (hq : 2≤q) (free : QFree E V q)
    (X : TwoExits q E V R H w c a u v) :
    (q:ℚ)*mass (insert u (outN E V u) ∩ insert v (outN E V v)) w+min (w u) (w v)≤c := by
  by_cases vu : E v u=true
  · have uv : ¬E u v=true := fun e=>free u 2 (by decide) hq
      (.step X.z₂v e (.step X.z₁v vu (.refl _)))
    have bd := one_side X.pos X.flat X.z₂v X.ne.symm uv
    rw [inter_comm] at bd
    linarith [min_le_right (w u) (w v)]
  · have bd := one_side X.pos X.flat X.z₁v X.ne vu
    linarith [min_le_left (w u) (w v)]

local notation "σ" => c-mass V w
local notation "Q" => (q:ℚ)*(c-mass V w+mass (V\R) w)-c
local notation "G" => (q:ℚ)*mass H w-mass R w
local notation "k" => ((q:ℚ)-1)

theorem shared_row_positive (hq : 2≤q) (free : QFree E V q)
    (X : TwoExits q E V R H w c a u v) {r : ℕ}
    (bu : E r u=false → Q≤(q:ℚ)*k*leak E V R w r)
    (au : E r u=true → k^2*G≤(q:ℚ)*k*leak E V R w r-Q)
    (bv : E r v=false → Q≤(q:ℚ)*k*leak E V R w r)
    (av : E r v=true → k^2*G≤(q:ℚ)*k*leak E V R w r-Q) :
    0<residual E V R w u v r := by
  apply lt_of_le_of_ne (residual_nonneg X.pos r)
  intro eq
  obtain ⟨_,_,ov,_,_⟩ := zero_residual_row hq X eq.symm bu au bv av
  have bound := overlap_cap hq free X
  have sm := lt_min (X.pos u X.z₁v) (X.pos v X.z₂v)
  have nn : (0:ℚ)≤q+k^2 := by positivity
  linarith [mul_nonneg nn (sub_nonneg.mpr X.high.le)]

theorem same_pair_bill (hq : 2≤q) (free : QFree E V q)
    (X : TwoExits q E V R H w c a u v) {x y : ℕ}
    (xu : E x u=true) (xv : E x v=true) (yu : E y u=false) (yv : E y v=false)
    (block : Q≤k*(leak E V R w x+k*leak E V R w y)) :
    (q:ℚ)*σ+min (w u) (w v)≤k*(residual E V R w u v x+k*residual E V R w u v y) := by
  have p := (pair_same X xu xv yu yv block).1
  linarith [overlap_cap hq free X]

/-- When the two sets of internal path vertices together fit within the girth
cutoff, some actual inner row enters both exits. -/
theorem shared_entry {A B : Finset ℕ} (free : QFree E V q) (inside : R⊆V)
    (ar : A⊆R) (br : B⊆R) (live : (A∪B).Nonempty) (size : (A∪B).card≤q)
    (left : ∀i∈R,∃j∈insert u A,E i j=true)
    (right : ∀i∈R,∃j∈insert v B,E i j=true) :
    ∃i∈A∪B,E i u=true ∧ E i v=true := by
  obtain ⟨p,hp⟩ := live
  have ir := union_subset ar br
  obtain ⟨i,ii,dead,_⟩ := reach_sink_of_card (free.mono_set (ir.trans inside)) size hp
  obtain ⟨j,jh,ij⟩ := left i (ir ii)
  obtain ⟨l,lh,il⟩ := right i (ir ii)
  have eq := (mem_insert.mp jh).resolve_right (fun ja=>dead j (mem_union_left _ ja) ij)
  have el := (mem_insert.mp lh).resolve_right (fun lb=>dead l (mem_union_right _ lb) il)
  exact ⟨i,ii,eq ▸ ij,el ▸ il⟩

#print axioms overlap_cap
#print axioms shared_row_positive
#print axioms same_pair_bill
#print axioms shared_entry

/-- Two actual covers of size q−1 automatically meet the size test when
q is three or four. The resulting row sees both exits on the original graph. -/
theorem cover_entry (lo : 3≤q) (hi : q≤4) (free : QFree E V q)
    (rs : R⊆V) {T S : Finset ℕ} (tc : T.card+1=q) (sc : S.card+1=q)
    (left : ∀i∈R,∃j∈T,E i j=true) (right : ∀i∈R,∃j∈S,E i j=true)
    (ut : T\R={u}) (vs : S\R={v}) : ∃i∈R,E i u=true ∧ E i v=true := by
  classical
  have decomp {K : Finset ℕ} {z : ℕ} (one : K\R={z}) :
      z∈K ∧ K.erase z⊆R ∧ insert z (K.erase z)=K := by
    have zk := (mem_sdiff.mp (one ▸ mem_singleton_self z)).1
    refine ⟨zk,?_,insert_erase zk⟩
    intro i hi'
    by_contra off
    exact (mem_erase.mp hi').1 (mem_singleton.mp (one ▸ mem_sdiff.mpr ⟨(mem_erase.mp hi').2,off⟩))
  obtain ⟨uT,ar,reT⟩ := decomp ut
  obtain ⟨vS,br,reS⟩ := decomp vs
  have ct := card_erase_add_one uT
  have cs := card_erase_add_one vS
  have size := card_union_le (T.erase u) (S.erase v)
  have live : (T.erase u).Nonempty := card_pos.mp (by omega)
  obtain ⟨i,ii,iu,iv⟩ := shared_entry free rs ar br (live.mono subset_union_left)
    (by omega) (reT.symm ▸ left) (reS.symm ▸ right)
  exact ⟨i,union_subset ar br ii,iu,iv⟩

/-- If a pair swaps its role between two exits and sends no mass beyond them,
a joint entering row quantifies the overlap required even when it is nonempty. -/
theorem swapped_joint_bound (hq : 3≤q) (X : TwoExits q E V R H w c a u v)
    {x y i : ℕ} (ir : i∈R) (iu : E i u=true) (iv : E i v=true)
    (xu : E x u=true) (xv : E x v=false) (yu : E y u=false) (yv : E y v=true)
    (zx : residual E V R w u v x=0) (zy : residual E V R w u v y=0)
    (first : Q≤k*(leak E V R w x+k*leak E V R w y))
    (second : Q≤k*(leak E V R w y+k*leak E V R w x)) :
    2*(q:ℚ)*((q:ℚ)*σ+c-(q:ℚ)*mass (insert u (outN E V u)∩insert v (outN E V v)) w)
      ≤k*((q:ℚ)-2)*(c-w i) := by
  obtain ⟨p₁,p₂⟩ := pair_swapped X xu xv yu yv first second
  rw [zx,zy] at p₁ p₂
  have sub : ({u,v}:Finset ℕ)⊆outN E V i := by
    apply insert_subset (mem_outN.mpr ⟨X.z₁v,iu⟩)
    exact singleton_subset_iff.mpr (mem_outN.mpr ⟨X.z₂v,iv⟩)
  have cap := sum_le_sum_of_subset_of_nonneg (f:=w) sub (fun j hj _=>(X.pos j (mem_outN.mp hj).1).le)
  rw [sum_pair X.ne] at cap
  change w u+w v≤mass (outN E V i) w at cap
  have row := X.flat i (X.rs ir)
  rw [WeightedSD.row,outW_eq_mass] at row
  have q0 : (0:ℚ)≤q := Nat.cast_nonneg q
  have degree : (3:ℚ)≤q := by exact_mod_cast hq
  have A : 0≤k*((q:ℚ)-2) := mul_nonneg (by linarith) (by linarith)
  have One : (q:ℚ)*(w u+w v)≤c-w i := by linarith [mul_le_mul_of_nonneg_left cap q0]
  have both := mul_le_mul_of_nonneg_left (add_le_add p₁ p₂) q0
  nlinarith only [both,mul_le_mul_of_nonneg_left One A]

#print axioms cover_entry
#print axioms swapped_joint_bound

/-- For any number of exits, a common closed successor cannot return to a parent
of any exit. This holds even if the successor is itself an exit. -/
theorem no_return_rectangle {T : Finset ℕ} (hq : 3≤q) (free : QFree E V q)
    (ts : T⊆V) {s p : ℕ} (sv : s∈V) (pv : p∈V)
    (cover : ∀z∈T,s∈insert z (outN E V z)) (par : ∃z∈T,E p z=true) :
    s≠p ∧ E s p=false := by
  obtain ⟨z,zt,pz⟩ := par
  have zv := ts zt
  have path : ∃d,0<d ∧ d≤2 ∧ Walk E V p s d := by
    rcases mem_insert.mp (cover z zt) with eq|hit
    · subst s; exact ⟨1,by decide,by decide,.step zv pz (.refl _)⟩
    · exact ⟨2,by decide,by decide,.step zv pz (.step sv (mem_outN.mp hit).2 (.refl _))⟩
  obtain ⟨d,positive,short,walk⟩ := path
  exact ⟨fun eq=>free p d positive (by omega) (eq ▸ walk),
    Bool.eq_false_iff.mpr (fun arc=>free p (d+1) (by omega) (by omega) (walk.snoc pv arc))⟩

/-- Both native equalizers price the same forbidden rectangle. Forward and
reverse prices may differ. -/
theorem rectangle_budgets {S P : Finset ℕ} {p : ℕ→ℚ} {d : ℚ}
    (free : QFree E V q) (small : SmallerSmallRow q V.card)
    (sv : S⊆V) (pv : P⊆V) (sl : S.Nonempty) (pl : P.Nonempty)
    (dis : Disjoint S P) (absent : ∀i∈S,∀j∈P,E i j=false)
    (wp : ∀i∈V,0≤w i) (pp : ∀i∈V,0≤p i)
    (rows : ∀i∈V,WeightedSD.row q E V w i=c)
    (cols : ∀i∈V,WeightedSD.row q (fun i j=>E j i) V p i=d) :
    (q:ℚ)*mass P w+k*mass S w≤(q:ℚ)*mass V w-c ∧
    (q:ℚ)*mass S p+k*mass P p≤(q:ℚ)*mass V p-d := by
  have half {F : CH.Digraph} {B C : Finset ℕ} {v : ℕ→ℚ} {e : ℚ} (nf : QFree F V q)
      (bs : B⊆V) (cs : C⊆V) (bl : B.Nonempty) (cl : C.Nonempty) (dj : Disjoint B C)
      (off : ∀i∈B,∀j∈C,F i j=false) (nn : ∀i∈V,0≤v i)
      (flat : ∀i∈V,WeightedSD.row q F V v i=e) :
      (q:ℚ)*mass C v+k*mass B v≤(q:ℚ)*mass V v-e := by
    obtain ⟨j,jc⟩ := cl
    have sub : B⊆V\C := fun i hi=>mem_sdiff.mpr ⟨bs hi,disjoint_left.mp dj hi⟩
    have ne : B≠V := fun all => disjoint_left.mp dj (all.symm ▸ cs jc) jc
    have bd := PortParentInvariant.collective_slack nf small bl sub ne off v nn flat
    have m : mass (V\C) v+mass C v=mass V v := sum_sdiff cs
    nlinarith only [bd,congrArg (fun x : ℚ=>(q:ℚ)*x) m]
  exact ⟨half free sv pv sl pl dis absent wp rows,
    half free.reverse pv sv pl sl dis.symm (fun i ip j js=>absent j js i ip) pp cols⟩

#print axioms no_return_rectangle
#print axioms rectangle_budgets
end LeanCH.BR.Closure.TwoExitOverlapCap
