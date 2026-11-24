import checkpoints.shen_extension.SharedArcCleanRecurrence

namespace LeanCH.BR.Closure.StrictReturnLayers
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights

/-- Add a row exactly when removing all its arcs into the previous layer
would bring its weighted score down to the total mass or below. -/
noncomputable def layers (q : ℕ) (D : CH.Digraph) (V : Finset ℕ)
    (w : ℕ → ℚ) (T : Finset ℕ) : ℕ → Finset ℕ
  | 0 => T
  | k+1 =>
    let S := layers q D V w T k
    S ∪ V.filter (fun v => w v + q*outW D (V \ S) w v ≤ mass V w)

private theorem grows {q D V w T} (i : ℕ) :
    layers q D V w T i ⊆ layers q D V w T (i+1) := subset_union_left

private theorem nested {q D V w T i j} (le : i≤j) :
    layers q D V w T i ⊆ layers q D V w T j := (monotone_nat_of_le_succ (grows (q:=q) (D:=D)
      (V:=V) (w:=w) (T:=T))) le

theorem bounded {q D V w T} (ts : T⊆V) (k) : layers q D V w T k⊆V := by
  induction k with
  | zero => exact ts
  | succ k ih => exact union_subset ih (filter_subset _ _)

def Returns (E : CH.Digraph) (V T : Finset ℕ) (k v : ℕ) : Prop :=
  ∃ t ∈ T, ∃ l ≤ k, Walk E V v t l

def Keeps {q : ℕ} (D E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) : Prop :=
  (∀i j,E i j=true → D i j=true) ∧ ∀i∈V,mass V w < WeightedSD.row q E V w i

/-- Every subgraph keeping the original strict row scores above total mass
has a return of length at most k from each member of the kth layer. -/
theorem forced {q D E V w T} (keep : Keeps (q:=q) D E V w) (ts : T⊆V)
    (nn : ∀i∈V,0≤w i) (k : ℕ) {v} (hit : v∈layers q D V w T k) : Returns E V T k v := by
  classical
  induction k generalizing v with
  | zero => exact ⟨v,hit,0,by omega,.refl _⟩
  | succ k ih =>
    let S := layers q D V w T k
    rcases mem_union.mp hit with old|admitRow
    · obtain ⟨t,tm,l,bound,path⟩ := ih old
      exact ⟨t,tm,l,by omega,path⟩
    obtain ⟨vv,low⟩ := mem_filter.mp admitRow
    have someEdge : ∃j∈S,E v j=true := by
      by_contra none
      have zero : outW E S w v=0 := sum_eq_zero fun j jm => by
        simp [show E v j=false from Bool.eq_false_iff.mpr (fun e => none ⟨j,jm,e⟩)]
      have bound : outW E (V \ S) w v ≤ outW D (V \ S) w v := by
        apply sum_le_sum
        intro j hj
        cases ed : E v j
        · simp; split <;> simp_all [nn j (mem_sdiff.mp hj).1]
        · simp [keep.1 v j ed]
      have high := keep.2 v vv
      rw [WeightedSD.row,outW_split (bounded ts k),zero,zero_add] at high
      exact (not_lt_of_ge low) (high.trans_le (add_le_add_right (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg q)) _))
    obtain ⟨j,jm,ed⟩ := someEdge
    obtain ⟨t,tm,l,le,path⟩ := ih jm
    exact ⟨t,tm,l+1,by omega,.step (bounded ts k jm) ed path⟩

/-- One simultaneous deletion attains the forced layers for all starting
vertices and all horizons up to k. All target rows are retained. -/
theorem realize {q D V w T} (ts : T⊆V)
    (strict : ∀i∈V,mass V w < WeightedSD.row q D V w i) (k : ℕ) :
    ∃ E, Keeps (q:=q) D E V w ∧
      (∀i∈T,∀j,E i j=D i j) ∧
      (∀i j,j∉layers q D V w T k → E i j=D i j) ∧
      ∀ l≤k,∀v∈V,Returns E V T l v → v∈layers q D V w T l := by
  classical
  induction k with
  | zero =>
    refine ⟨D,⟨fun _ _ e => e,strict⟩,by simp,by simp,?_⟩
    rintro l bound v _ ⟨t,tm,j,jl,p⟩
    obtain rfl : l=0 := by omega
    obtain rfl : j=0 := by omega
    cases p
    exact tm
  | succ k ih =>
    obtain ⟨E,keep,targets,outside,detect⟩ := ih
    let S := layers q D V w T k
    let N := layers q D V w T (k+1)
    let J : CH.Digraph := fun i j => if i∉N ∧ j∈S then false else E i j
    have sub {i j} (ed : J i j=true) : E i j=true := by
      unfold J at ed; split at ed <;> simp_all
    have inside (i) (hi : i∈N) (j) : J i j=E i j := by simp [J,hi]
    have score (i) (iv : i∈V) : mass V w < WeightedSD.row q J V w i := by
      by_cases hi : i∈N
      · simpa only [WeightedSD.row,outW,inside i hi] using keep.2 i iv
      · have off : outW J S w i=0 := sum_eq_zero fun j jm => by simp [J,hi,jm]
        have same : outW J (V \ S) w i=outW D (V \ S) w i := by
          apply sum_congr rfl
          intro j jm
          simp [J,(mem_sdiff.mp jm).2,outside i j (mem_sdiff.mp jm).2]
        rw [WeightedSD.row,outW_split (bounded ts k),off,zero_add,same]
        exact lt_of_not_ge fun low => hi (mem_union_right _ (mem_filter.mpr ⟨iv,low⟩))
    refine ⟨J,⟨fun i j ed => keep.1 i j (sub ed),score⟩,?_,?_,?_⟩
    · intro i it j
      exact (inside i (nested (Nat.zero_le (k+1)) it) j).trans (targets i it j)
    · intro i j out
      have old : j∉S := fun hj => out (grows k hj)
      simp [J,old,outside i j old]
    · rintro l bound v vv ⟨t,tm,d,dl,path⟩
      by_cases earlier : l≤k
      · exact detect l earlier v vv ⟨t,tm,d,dl,walk_sub (fun _ _ e => sub e) path⟩
      obtain rfl : l=k+1 := by omega
      by_contra absent
      cases path with
      | refl => exact absent (nested (Nat.zero_le (k+1)) tm)
      | @step _ j _ m jv ed tail =>
        have jm : j∈S := detect k le_rfl j jv ⟨t,tm,m,by omega,walk_sub (fun _ _ e => sub e) tail⟩
        have out : v∉N := absent
        simp [J,out,jm] at ed

/-- The smaller-host hypothesis forces robust reach in at most q steps,
with the adversary allowed to discard a different set of arcs in every row. -/
theorem covers {q D V w T} (hq : 2≤q) (small : SmallerSmallRow q V.card) (free : QFree D V q)
    (ts : T⊆V) (live : T.Nonempty) (pos : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w < WeightedSD.row q D V w i) : layers q D V w T q=V := by
  obtain ⟨E,keep,_,_,detect⟩ := realize ts strict q
  apply Subset.antisymm (bounded ts q)
  intro v vv
  obtain ⟨t,tm⟩ := live
  obtain ⟨_,l,le,path⟩ := mem_ball.mp (feasible_reach_positive_within hq (qfree_sub keep.1 free)
    small w (fun i hi => (pos i hi).le) (fun i hi => (keep.2 i hi).le) vv (ts tm) (pos t (ts tm)))
  exact detect q le_rfl v vv ⟨t,tm,l,le,path⟩

#print axioms forced
#print axioms realize
#print axioms covers

/-- The fold onto a receiver charges only heads that return robustly.
The charge includes both the entire transferred mass and the receiver's
own strict surplus. The target may be an arbitrary nonempty bank. -/
theorem bank_bound {q D V w T} (hq : 2≤q) (small : SmallerSmallRow q V.card) (free : QFree D V q)
    (ts : T⊆V) (live : T.Nonempty) (nn : ∀i∈V,0≤w i)
    (strict : ∀i∈V,mass V w < WeightedSD.row q D V w i) {a} (retained : a∈V \ T)
    (no : ∀t∈T,¬D a t=true) :
    mass T w + (WeightedSD.row q D V w a - mass V w) ≤
      q * mass (outN D V a ∩ layers q D V w T (q-1)) w := by
  classical
  obtain ⟨E,keep,_,_,detect⟩ := realize ts strict (q-1)
  let J : CH.Digraph := fun i j => if i=a then D i j else E i j
  have sub (i j) (e : J i j=true) : D i j=true := by
    dsimp only [J] at e
    split at e
    · exact e
    · exact keep.1 i j e
  have rowA : WeightedSD.row q J V w a = WeightedSD.row q D V w a := by
    simp [WeightedSD.row,outW,J]
  have high (i) (iv : i∈V) : mass V w < WeightedSD.row q J V w i := by
    by_cases eq : i=a
    · exact eq ▸ (rowA ▸ strict a (mem_sdiff.mp retained).1)
    · simpa only [WeightedSD.row,outW,J,eq,ite_false] using keep.2 i iv
  have safe := qfree_sub sub free
  have miss (t) (tm : t∈T) : ¬J a t=true := fun e => no t tm (sub a t e)
  let B := foldBank q J V T a
  have cover : B ⊆ outN D V a ∩ layers q D V w T (q-1) := by
    intro h hh
    obtain ⟨head,t,tm,hit⟩ := mem_filter.mp hh
    obtain ⟨hv,ah⟩ := mem_outN.mp head
    obtain ⟨_,l,le,path⟩ := mem_ball.mp hit
    have away : h≠a := fun eq => loopfree safe (by omega) (mem_sdiff.mp retained).1 (eq ▸ ah)
    have cut : Walk J (V.erase a) h t l := by
      rcases path.lastVisit a with clear|⟨d,j,_,len,back,_⟩
      · exact clear
      · exact (safe a (d+1) (by omega) (by omega) (.step hv ah back)).elim
    have old := walk_mono_graph_on (E:=E) (fun x hx _ _ e => by
      simpa only [J,(mem_erase.mp hx).1,ite_false] using e) cut (mem_erase.mpr ⟨away,hv⟩)
    exact mem_inter.mpr ⟨mem_outN.mpr ⟨hv,sub a h ah⟩,detect (q-1) le_rfl h hv
      ⟨t,tm,l,le,old.mono (erase_subset _ _)⟩⟩
  let v := addWeightAt w a (mass T w)
  have child := small _ _ (parentTransfer_card_lt ts live) (reachFold_qfree safe ts miss)
  obtain ⟨i,iv,low⟩ := child v
    (fun i im => addWeightAt_nonneg nn (mass_nonneg fun x hx => nn x (ts hx)) a i (mem_sdiff.mp im).1)
    ⟨a,retained⟩
  change WeightedSD.row q (foldGraph J V T B a) (V \ T) v i ≤ mass (V \ T) v at low
  change WeightedSD.row q (foldGraph J V T B a) (V \ T) (addWeightAt w a (mass T w)) i ≤ _ at low
  rw [show mass (V \ T) v=mass V w from fold_weight_mass ts retained w] at low
  have eq : i=a := by
    by_contra diff
    exact (high i (mem_sdiff.mp iv).1).not_ge ((fold_other_row ts retained w nn iv diff).trans low)
  subst i
  rw [fold_receiver_row retained miss (loopfree safe (by omega) (mem_sdiff.mp retained).1)
    foldBank_subset_out w,rowA] at low
  have monotone := mass_mono cover (fun z hz => nn z (outN_subset (mem_inter.mp hz).1))
  exact (by linarith only [low] : mass T w + (WeightedSD.row q D V w a - mass V w) ≤ q*mass B w).trans
    (mul_le_mul_of_nonneg_left monotone (Nat.cast_nonneg q))

#print axioms bank_bound

/-- Cut the specified first arcs of a return and its remaining last arcs. -/
def endCut (D : CH.Digraph) (h t : ℕ) (L R : Finset ℕ) : CH.Digraph := fun i j =>
  if (i=h ∧ j∈L) ∨ (j=t ∧ i∈R) then false else D i j

open Classical in
noncomputable def lastParents (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (h t : ℕ) (L : Finset ℕ) :=
  (inN D V t).filter (fun y => ∃z∈outN D V h \ L,y∈ball D V z (q-3))

theorem cut_sub {D h t L R i j} (e : endCut D h t L R i j=true) : D i j=true := by
  unfold endCut at e; split at e <;> simp_all

theorem cut_blocks {q D V h t} (hq : 3≤q) (ne : h≠t) (ht : D h t=false) (L : Finset ℕ) :
    ¬Returns (endCut D h t L (lastParents q D V h t L)) V {t} (q-1) h := by
  classical
  let R := lastParents q D V h t L
  let K := endCut D h t L R
  rintro ⟨v,vm,l,le,p⟩
  rw [mem_singleton.mp vm] at p
  cases p with
  | refl => exact ne rfl
  | @step _ z _ m zv hz tail =>
    have clear : z∉L := fun hit => by simp [endCut,hit] at hz
    have head := cut_sub hz
    cases m with
    | zero => cases tail; exact Bool.noConfusion (ht.symm.trans head)
    | succ k =>
      obtain ⟨y,body,tv,yt⟩ := tail.unsnoc
      have yv : y∈V := body.end_mem_or.elim (fun eq => eq ▸ zv) id
      have yes : y∈R := mem_filter.mpr ⟨mem_inN.mpr ⟨yv,cut_sub yt⟩,z,
        mem_sdiff.mpr ⟨mem_outN.mpr ⟨zv,head⟩,clear⟩,
        mem_ball.mpr ⟨yv,k,by omega,walk_sub (fun _ _ e => cut_sub e) body⟩⟩
      change K y t=true at yt
      simp [K,endCut,yes] at yt

theorem triangle_lastParents (D : CH.Digraph) (V : Finset ℕ) (h t : ℕ) (L : Finset ℕ) :
    lastParents 3 D V h t L = (outN D V h ∩ inN D V t) \ L := by
  classical
  ext y
  simp only [lastParents,mem_filter,mem_sdiff,mem_inter]
  constructor
  · rintro ⟨yt,z,⟨hz,out⟩,hit⟩
    obtain ⟨_,k,bound,p⟩ := mem_ball.mp hit
    obtain rfl : k=0 := by omega
    cases p
    exact ⟨⟨hz,yt⟩,out⟩
  · rintro ⟨⟨hy,yt⟩,out⟩
    exact ⟨yt,y,⟨hy,out⟩,self_mem_ball (mem_inN.mp yt).1⟩

#print axioms cut_blocks
#print axioms triangle_lastParents
end LeanCH.BR.Closure.StrictReturnLayers
