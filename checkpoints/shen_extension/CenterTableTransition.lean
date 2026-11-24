import checkpoints.shen_extension.CircularPhaseTransition

namespace LeanCH.BR.ShenCenterTable
open BRq2 BRq3 BR45 ShenCircle ShenPrimeTransition

/-- One nominated head for each source. The distinct centers nominate the
next center cyclically. No nominated arc is assumed to be in the graph. -/
structure Table (q : ℕ) (V : Finset ℕ) where
  center : ℕ → ℕ
  label : ℕ → ℕ
  mem : ∀ i < q, center i ∈ V
  injective : Set.InjOn center (Finset.range q)
  bounded : ∀ x ∈ V, label x < q
  next : ∀ i < q, label (center i) = (i+1)%q

def Table.pool {q V} (P : Table q V) (i : ℕ) := V.filter (fun x => P.label x=i)

def Table.misses {q V} (P : Table q V) (D : CH.Digraph) :=
  V.filter (fun x => D x (P.center (P.label x)) = false)

private theorem follow {D V} (path : ℕ → ℕ) (a n : ℕ)
    (mem : ∀ (i : ℕ), a < i → i ≤ a+n → path i ∈ V)
    (arc : ∀ (i : ℕ), a ≤ i → i < a+n → D (path i) (path (i+1))=true) :
    Walk D V (path a) (path (a+n)) n := by
  induction n with
  | zero => exact .refl _
  | succ k ih =>
    exact (ih (fun i hi h => mem i hi (by omega)) (fun i hi h => arc i hi (by omega))).snoc
      (mem _ (by omega) le_rfl) (arc (a+k) (by omega) (by omega))

private theorem some_break {q D V} (hq : 0<q) (free : QFree D V q) (P : Table q V) :
    ∃ a < q, P.center a ∈ P.misses D := by
  by_contra! none
  let path := fun i => P.center (i%q)
  have arc (i) (hi : i<q) : D (path i) (path (i+1))=true := by
    have miss := none i hi
    simp [Table.misses,P.mem i hi,P.next i hi] at miss
    simpa [path,Nat.mod_eq_of_lt hi] using miss
  have w := follow path 0 q (fun i _ _ => P.mem _ (Nat.mod_lt _ hq))
    (fun i _ hi => arc i (by omega))
  have closed : Walk D V (P.center 0) (P.center 0) q := by simpa [path] using w
  exact free _ q hq le_rfl closed

/-- In a q-free input with at most one failed nomination, the source of
that failure lies in its own successor's pool, and its entire real
out-neighbourhood lies in that same pool. -/
theorem sole_break {q D V} (hq : 2≤q) (free : QFree D V q) (P : Table q V)
    (one : (P.misses D).card≤1) :
    ∃ a < q, P.center a ∈ P.misses D ∧
      P.center a ∈ P.pool ((a+1)%q) ∧ outN D V (P.center a) ⊆ P.pool ((a+1)%q) := by
  obtain ⟨a,ha,broken⟩ := some_break (by omega) free P
  let u := P.center a
  have intact {x} (hx : x∈V) (other : x≠u) : D x (P.center (P.label x))=true := by
    by_contra! fail
    exact other (Finset.card_le_one.mp one x
      (Finset.mem_filter.mpr ⟨hx,Bool.eq_false_iff.mpr fail⟩) u broken)
  refine ⟨a,ha,broken,Finset.mem_filter.mpr ⟨P.mem _ ha,P.next a ha⟩,?_⟩
  intro x hx
  obtain ⟨xV,ux⟩ := mem_outN.mp hx
  apply Finset.mem_filter.mpr ⟨xV,?_⟩
  by_contra bad
  let idx := fun j => (a+1+j)%q
  let path := fun j => P.center (idx j)
  let j := (q + P.label x - (a+1))%q
  have small : j<q := Nat.mod_lt _ (by omega)
  have hit : idx j=P.label x := by
    dsimp [idx,j]
    rw [Nat.add_mod_mod,show a+1+(q+P.label x-(a+1))=q+P.label x by omega,
      Nat.add_mod_left,Nat.mod_eq_of_lt (P.bounded _ xV)]
  have nonzero : j≠0 := by
    rintro z
    apply bad
    simpa [idx,z] using hit.symm
  have endIdx : idx (q-1)=a := by
    dsimp [idx]
    rw [show a+1+(q-1)=a+q by omega,Nat.add_mod_right,Nat.mod_eq_of_lt ha]
  have proper (k) (hk : k<q-1) : idx k ≠ a := by
    dsimp [idx]
    by_cases under : a+1+k<q
    · rw [Nat.mod_eq_of_lt under]; omega
    · have eq : a+1+k=(a+1+k-q)+q := by omega
      rw [eq,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]; omega
  have link (k) (hk : k<q-1) : D (path k) (path (k+1))=true := by
    have v := Nat.mod_lt (a+1+k) (by omega : 0<q)
    have ne : path k≠u := fun eq => proper k hk (P.injective (Finset.mem_range.mpr v)
      (Finset.mem_range.mpr ha) eq)
    have arc := intact (P.mem (idx k) v) ne
    rw [P.next _ v] at arc
    simpa [path,idx,Nat.mod_add_mod,Nat.add_assoc] using arc
  have back := follow path j (q-1-j) (fun k _ _ => P.mem _ (Nat.mod_lt _ (by omega)))
    (fun k _ hk => link k (by omega))
  rw [show j+(q-1-j)=q-1 by omega] at back
  change Walk D V (P.center (idx j)) (P.center (idx (q-1))) _ at back
  rw [hit,endIdx] at back
  have xu : x≠u := by rintro rfl; exact loopfree free (by omega) (P.mem a ha) ux
  exact free u (q-1-j+1+1) (by omega) (by omega)
    (.step xV ux (.step (P.mem _ (P.bounded _ xV)) (intact xV xu) back))

theorem two_missing {q s D V} (hq : 2≤q) (free : QFree D V q) (P : Table q V)
    (degree : ∀ i<q, s≤(outN D V (P.center i)).card)
    (caps : ∀ i<q, (P.pool i).card≤s) : 2≤(P.misses D).card := by
  by_contra! small
  obtain ⟨a,ha,_,self,sub⟩ := sole_break hq free P (by omega)
  have missing : P.center a ∉ outN D V (P.center a) := fun h =>
    loopfree free (by omega) (P.mem a ha) (mem_outN.mp h).2
  have proper := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨sub,fun eq => missing (eq ▸ self)⟩)
  have := caps ((a+1)%q) (Nat.mod_lt _ (by omega))
  have := degree a ha
  omega

#print axioms sole_break
#print axioms two_missing

theorem two_missing_weighted {q D V w} (hq : 2≤q) (free : QFree D V q) (P : Table q V)
    (strict : Strict q D V w)
    (caps : ∀ i<q, q*total (P.pool ((i+1)%q)) w ≤ total V w + (q-1)*w (P.center i)) :
    2≤(P.misses D).card := by
  by_contra! small
  obtain ⟨a,ha,_,self,sub⟩ := sole_break hq free P (by omega)
  let u := P.center a
  have missing : u ∉ outN D V u := fun h => loopfree free (by omega) (P.mem a ha) (mem_outN.mp h).2
  have bank := Finset.sum_le_sum_of_subset_of_nonneg (f:=w) (Finset.insert_subset self sub)
    (fun _ _ _ => Nat.zero_le _)
  change (∑ x ∈ insert u (outN D V u), w x) ≤ _ at bank
  rw [Finset.sum_insert missing] at bank
  have charged := (Nat.mul_le_mul_left q bank).trans (caps a ha)
  have row := nat_strict.mp strict u (P.mem a ha)
  change total V w < w u + q * ∑ i∈V, (if D u i=true then w i else 0) at row
  change q*(w u + ∑ i∈outN D V u, w i) ≤ total V w + (q-1)*w u at charged
  simp only [outN,Finset.sum_filter,Nat.mul_add] at charged
  have split : (q-1)*w u + w u = q*w u := by rw [← Nat.succ_mul,show (q-1).succ=q by omega]
  omega

/-- Sum genuinely different missing arcs. A row may use different prescribed
centers in the different tables, but each nominated head at that row is paid once. -/
theorem family_missing {q s D V} (hq : 2≤q) (free : QFree D V q)
    (degree : ∀ x∈V, s≤(outN D V x).card)
    (I : Finset ℕ) (P : ℕ → Table q V)
    (caps : ∀ j∈I, ∀ i<q, ((P j).pool i).card ≤ s)
    (distinct : ∀ x∈V, Set.InjOn (fun j => (P j).center ((P j).label x)) I)
    (target : ℕ → Finset ℕ) (nominates : ∀ x∈V, ∀ j∈I, (P j).center ((P j).label x) ∈ target x) :
    2*I.card ≤ ∑ x∈V, ((target x).filter (fun y => D x y=false)).card := by
  classical
  have lo := Finset.sum_le_sum (fun j hj =>
    two_missing hq free (P j) (fun i hi => degree _ ((P j).mem i hi)) (caps j hj))
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at lo
  rw [Nat.mul_comm I.card 2] at lo
  apply lo.trans
  simp only [Table.misses,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x hx
  rw [← Finset.card_filter,← Finset.card_filter]
  apply Finset.card_le_card_of_injOn (fun j => (P j).center ((P j).label x))
  · intro j hj
    exact Finset.mem_filter.mpr ⟨nominates _ hx _ (Finset.mem_filter.mp hj).1,(Finset.mem_filter.mp hj).2⟩
  · exact (distinct x hx).mono (Finset.filter_subset _ _)

/-- For q cyclically ordered layers of s labels, at least 2s real arcs
from one layer to its successor must be absent. The layer labels may be
chosen anew for each application. -/
theorem layer_holes {q s D V} (hq : 2≤q) (free : QFree D V q)
    (degree : ∀ x∈V, s≤(outN D V x).card) (layer : ℕ → ℕ)
    (bound : ∀ x∈V, layer x<q)
    (sizes : ∀ j<q, (V.filter (fun x => layer x=j)).card=s) :
    2*s ≤ ∑ x∈V, ((V.filter (fun y => layer y=(layer x+1)%q)).filter
      (fun y => D x y=false)).card := by
  classical
  let block := fun j => V.filter (fun x => layer x=j)
  let cell := fun (j t : ℕ) => if h : j<q ∧ t<s then
    (block j).orderEmbOfFin (sizes j h.1) ⟨t,h.2⟩ else 0
  have atCell (j t) (hj : j<q) (ht : t<s) : cell j t∈V ∧ layer (cell j t)=j := by
    have member : cell j t ∈ block j := by
      simp [cell,hj,ht]
    exact Finset.mem_filter.mp member
  let P (t : ℕ) (ht : t<s) : Table q V := {
    center := fun j => cell j t
    label := fun x => (layer x+1)%q
    mem := fun j hj => (atCell j t hj ht).1
    injective := by
      intro i hi j hj eq
      exact (atCell i t (Finset.mem_range.mp hi) ht).2.symm.trans
        ((congrArg layer eq).trans (atCell j t (Finset.mem_range.mp hj) ht).2)
    bounded := fun _ _ => Nat.mod_lt _ (by omega)
    next := fun j hj => by rw [(atCell j t hj ht).2] }
  by_cases zero : s=0
  · simp [zero]
  let tables t := if ht : t<s then P t ht else P 0 (by omega)
  let target := fun x => block ((layer x+1)%q)
  have h := family_missing hq free degree (Finset.range s) tables (target:=target)
  rw [Finset.card_range] at h
  apply h
  · intro t ht j hj
    have tlt := Finset.mem_range.mp ht
    let prev := if j=0 then q-1 else j-1
    have pv : prev<q := by dsimp [prev]; split <;> omega
    apply (Finset.card_le_card (t:=block prev) ?_).trans (sizes prev pv).le
    intro x hx
    obtain ⟨xV,lx⟩ := Finset.mem_filter.mp hx
    change (tables t).label x = j at lx
    simp [tables,tlt,P] at lx
    apply Finset.mem_filter.mpr ⟨xV,?_⟩
    have lim := bound x xV
    by_cases last : layer x+1=q
    · rw [last,Nat.mod_self] at lx; simp [prev,←lx]; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at lx
      simp [prev,←lx]
  · intro x _ t ht u hu eq
    have ht' := Finset.mem_range.mp ht
    have hu' := Finset.mem_range.mp hu
    let j := (layer x+1)%q
    have hj : j<q := Nat.mod_lt _ (by omega)
    change (tables t).center ((tables t).label x) = (tables u).center ((tables u).label x) at eq
    simp only [tables, ht',hu',↓reduceDIte,P] at eq
    change cell j t=cell j u at eq
    simp only [cell,hj,ht',hu',and_self,↓reduceDIte] at eq
    exact congrArg Fin.val ((block j).orderEmbOfFin (sizes j hj) |>.injective eq)
  · intro x _ t ht
    have lt := Finset.mem_range.mp ht
    have b := atCell ((layer x+1)%q) t (Nat.mod_lt _ (by omega)) lt
    simpa [tables,lt,P,target,block] using b

#print axioms two_missing_weighted
#print axioms family_missing
#print axioms layer_holes
end LeanCH.BR.ShenCenterTable
