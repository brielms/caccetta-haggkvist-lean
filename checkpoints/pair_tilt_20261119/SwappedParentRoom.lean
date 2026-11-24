import checkpoints.shen_extension.TwoExitOverlapCap

/-! # Swapped pair: exit-ancestor rectangle against the inner ball

This builds on `TwoExitOverlapCap` (`overlap_cap`, `swapped_joint_bound`, `no_return_rectangle`,
`rectangle_budgets`).

* `ancestor_no_return`: closed common successors of the exits avoid every vertex reaching an exit
  in `1..q-2` steps, not only the exit parents. For `q ≥ 4` this enlarges the rectangle.
* `start_entry`, `heads_not_ancestor`: under a cover, an inner row that is not an exit ancestor
  points to the start `t₀` of the induced path. Every head is such a row. With two covers, the
  inner rows outside the ancestor set point to both path starts.
* `swapped_parent_cap`: a surviving zero-residual swapped pair with a joint entering row `i`
  caps the weight of any avoided set `P`. At `q = 3` the cap is `27·w(P) ≤ 14c − 45σ − 2w(i)`.
* `inner_parent_room`: the inner ancestors `R ∖ D` weigh at most
  `((q−2)c − qσ − (q−1)(w u + w v) − min + w a)/q`, by the two-exit bank, the overlap cap and
  the root row.
* `inner_parents_compatible_three`: at `q = 3`, inner ancestors can break the cap only if
  `9·w(a) > 5c − 18σ + 18(w u + w v) + 9·min − 2w(i)`.
* `aggregate_witness_three`: every inequality above, together with the swapped AB tests, both
  banks and the gap, has a common rational solution. The parent rectangle alone does not close
  the swapped pair. -/
namespace LeanCH.BR.Closure.SwappedParentRoom
open Finset BRq2 BRq3 BR45 WeightedSD TwoExit

/-- `r` reaches `z` in `1..q-2` steps inside `U`. -/
def Ancestor (q : ℕ) (E : CH.Digraph) (U : Finset ℕ) (z r : ℕ) : Prop :=
  ∃ℓ,1≤ℓ ∧ ℓ≤q-2 ∧ Walk E U r z ℓ

/-- A closed successor of an exit cannot equal or point to any ancestor of that exit. -/
theorem ancestor_no_return {q : ℕ} {E : CH.Digraph} {V U : Finset ℕ} (hq : 2≤q)
    (free : QFree E V q) (uv : U⊆V) {z s p : ℕ} (pv : p∈V)
    (closed : s∈insert z (outN E V z)) (anc : Ancestor q E U z p) :
    s≠p ∧ E s p=false := by
  obtain ⟨ℓ,lp,lq,walk⟩ := anc
  have wv := walk.mono uv
  obtain ⟨d,dp,dq,reach⟩ : ∃d,1≤d ∧ d≤q-1 ∧ Walk E V p s d := by
    rcases mem_insert.mp closed with e|hit
    · exact ⟨ℓ,lp,by omega,e ▸ wv⟩
    · exact ⟨ℓ+1,by omega,by omega,wv.snoc (mem_outN.mp hit).1 (mem_outN.mp hit).2⟩
  refine ⟨fun eq => free p d dp (by omega) (eq ▸ reach),?_⟩
  apply Bool.eq_false_iff.mpr
  intro arc
  exact free p (d+1) (by omega) (by omega) (reach.snoc pv arc)

theorem heads_not_ancestor {q : ℕ} {E : CH.Digraph} {U H : Finset ℕ} {z : ℕ}
    (zu : z∈U) (zr : z∉BRsub.ballSet E U H (q-2)) : ∀h∈H,¬Ancestor q E U z h := by
  rintro h hh ⟨ℓ,_,lq,walk⟩
  exact zr (BRsub.mem_ballSet.mpr ⟨h,hh,mem_ball.mpr ⟨zu,ℓ,lq,walk⟩⟩)

/-- Under a cover, inner rows that are not exit ancestors enter the path start, which every
head enters as well. -/
theorem start_entry {q : ℕ} {E : CH.Digraph} {U H T : Finset ℕ} (hq : 3≤q) (free : QFree E U q)
    (hs : H⊆U) (hl : H.Nonempty) (ts : T⊆U) (size : T.card<q)
    (cover : ∀r∈BRsub.ballSet E U H (q-2),∃k∈T,E r k=true)
    {z : ℕ} (zt : z∈T\BRsub.ballSet E U H (q-2)) :
    ∃t₀∈T,t₀∈BRsub.ballSet E U H (q-2) ∧ (∀h∈H,E h t₀=true) ∧
      ∀r∈BRsub.ballSet E U H (q-2),¬Ancestor q E U z r → E r t₀=true := by
  obtain ⟨_,_,s,st,p,len,onto,_,entry,single,_,_,_⟩ :=
    CommonParentEndpointPath.full_cover (by omega) free hs hl ts size cover
  have zp : z=p.vertex p.len := mem_singleton.mp (single ▸ zt)
  have heads : ∀h∈H,E h s=true := fun h hh => (entry h hh s st).2 rfl
  obtain ⟨h,hh⟩ := hl
  have sr : s∈BRsub.ballSet E U H (q-2) := BRsub.mem_ballSet.mpr
    ⟨h,hh,mem_ball.mpr ⟨ts st,1,by omega,.step (ts st) (heads h hh) (.refl _)⟩⟩
  refine ⟨s,st,sr,heads,fun r rr far => ?_⟩
  obtain ⟨k,kt,rk⟩ := cover r rr
  obtain ⟨j,jr,rfl⟩ := mem_image.mp (onto.symm ▸ kt)
  have jb : j≤p.len := by have := mem_range.mp jr; omega
  rcases Nat.eq_zero_or_pos j with j0|jpos
  · rw [j0,p.start] at rk; exact rk
  · exfalso
    apply far
    refine ⟨p.len-j+1,by omega,by omega,?_⟩
    rw [zp]
    exact .step (ts (p.mem j jb)) rk ((p.walk jb le_rfl).mono ts)

/-- Two covers at one inner ball: every inner row that is an ancestor of neither exit enters
both path starts. -/
theorem double_entrance {q : ℕ} {E : CH.Digraph} {U H T S : Finset ℕ} (hq : 3≤q)
    (free : QFree E U q) (hs : H⊆U) (hl : H.Nonempty)
    (ts : T⊆U) (tsize : T.card<q) (tcov : ∀r∈BRsub.ballSet E U H (q-2),∃k∈T,E r k=true)
    (ss : S⊆U) (ssize : S.card<q) (scov : ∀r∈BRsub.ballSet E U H (q-2),∃k∈S,E r k=true)
    {u v : ℕ} (ut : u∈T\BRsub.ballSet E U H (q-2)) (vs : v∈S\BRsub.ballSet E U H (q-2)) :
    ∃t₀∈T,∃s₀∈S,(∀h∈H,E h t₀=true ∧ E h s₀=true) ∧
      ∀r∈BRsub.ballSet E U H (q-2),¬Ancestor q E U u r → ¬Ancestor q E U v r →
        E r t₀=true ∧ E r s₀=true := by
  obtain ⟨t₀,tt,_,th,tr⟩ := start_entry hq free hs hl ts tsize tcov ut
  obtain ⟨s₀,sS,_,sh,sr⟩ := start_entry hq free hs hl ss ssize scov vs
  exact ⟨t₀,tt,s₀,sS,fun h hh => ⟨th h hh,sh h hh⟩,fun r rr fu fv => ⟨tr r rr fu,sr r rr fv⟩⟩

/-- A surviving zero-residual swapped pair caps the weight of every set that the closed common
successors avoid. -/
theorem swapped_parent_cap {q : ℕ} {E : CH.Digraph} {V R H P : Finset ℕ} {w : ℕ→ℚ} {c : ℚ}
    {a u v x y i : ℕ} (hq : 3≤q) (X : TwoExits q E V R H w c a u v)
    (free : QFree E V q) (small : SmallerSmallRow q V.card)
    (ir : i∈R) (iu : E i u=true) (iv : E i v=true)
    (xu : E x u=true) (xv : E x v=false) (yu : E y u=false) (yv : E y v=true)
    (zx : residual E V R w u v x=0) (zy : residual E V R w u v y=0)
    (first : (q:ℚ)*(c-mass V w+mass (V\R) w)-c≤
      ((q:ℚ)-1)*(leak E V R w x+((q:ℚ)-1)*leak E V R w y))
    (second : (q:ℚ)*(c-mass V w+mass (V\R) w)-c≤
      ((q:ℚ)-1)*(leak E V R w y+((q:ℚ)-1)*leak E V R w x))
    (pv : P⊆V) (pl : P.Nonempty)
    (sl : (insert u (outN E V u)∩insert v (outN E V v)).Nonempty)
    (dis : Disjoint (insert u (outN E V u)∩insert v (outN E V v)) P)
    (absent : ∀s∈insert u (outN E V u)∩insert v (outN E V v),∀p∈P,E s p=false) :
    2*(q:ℚ)^3*mass P w≤2*(q:ℚ)^2*((q:ℚ)-1)*c-2*(q:ℚ)^3*(c-mass V w)
      -2*(q:ℚ)*((q:ℚ)-1)*((q:ℚ)*(c-mass V w)+c)+((q:ℚ)-1)^2*((q:ℚ)-2)*(c-w i) := by
  have sw := TwoExitOverlapCap.swapped_joint_bound hq X ir iu iv xu xv yu yv zx zy first second
  have sv : insert u (outN E V u)∩insert v (outN E V v)⊆V := by
    intro s hs
    rcases mem_insert.mp (mem_inter.mp hs).1 with e|h
    · rw [e]; exact X.z₁v
    · exact (mem_outN.mp h).1
  obtain ⟨p0,p0P⟩ := pl
  have outside : insert u (outN E V u)∩insert v (outN E V v)⊆V\P :=
    fun s hs => mem_sdiff.mpr ⟨sv hs,disjoint_left.mp dis hs⟩
  have proper : insert u (outN E V u)∩insert v (outN E V v)≠V := fun all =>
    disjoint_left.mp dis (all.symm ▸ pv p0P) p0P
  have slack := PortParentInvariant.collective_slack free small sl outside proper absent w
    (fun j jv => (X.pos j jv).le) X.flat
  have split : mass (V\P) w+mass P w=mass V w := by unfold mass; exact sum_sdiff pv
  have splitq : (q:ℚ)*mass (V\P) w+(q:ℚ)*mass P w=(q:ℚ)*mass V w := by rw [← mul_add,split]
  have q3 : (3:ℚ)≤q := by exact_mod_cast hq
  have rect : (q:ℚ)*mass P w+((q:ℚ)-1)*mass (insert u (outN E V u)∩insert v (outN E V v)) w≤
      (q:ℚ)*mass V w-c := by linarith
  have h1 := mul_le_mul_of_nonneg_left rect (by positivity : (0:ℚ)≤2*(q:ℚ)^2)
  have h2 := mul_le_mul_of_nonneg_left sw (by linarith : (0:ℚ)≤(q:ℚ)-1)
  nlinarith

/-- The inner exit ancestors carry at most this much. The heads lie in `D`. -/
theorem inner_parent_room {q : ℕ} {E : CH.Digraph} {V R H D : Finset ℕ} {w : ℕ→ℚ} {c : ℚ}
    {a u v : ℕ} (hq : 2≤q) (X : TwoExits q E V R H w c a u v) (free : QFree E V q)
    (hd : H⊆D) (dr : D⊆R) :
    (q:ℚ)*mass (R\D) w≤((q:ℚ)-2)*c-(q:ℚ)*(c-mass V w)-((q:ℚ)-1)*(w u+w v)
      -min (w u) (w v)+w a := by
  have cap := TwoExitOverlapCap.overlap_cap hq free X
  have two := bank_two X.pos X.flat X.z₁v X.z₁R X.dead₁ X.z₂v X.z₂R X.dead₂
  have hv : H⊆V := X.hs.trans X.rs
  have out : outN E V a=H := by
    ext j
    rw [mem_outN]
    exact ⟨fun ⟨jv,e⟩ => (X.heads j jv).mp e,fun jh => ⟨hv jh,(X.heads j (hv jh)).mpr jh⟩⟩
  have row := X.flat a X.av
  rw [WeightedSD.row,outW_eq_mass,out] at row
  have whole : mass V w=mass R w+mass (V\R) w := by
    unfold mass; rw [add_comm]; exact (sum_sdiff X.rs).symm
  have rd : mass (R\D) w+mass D w=mass R w := by unfold mass; exact sum_sdiff dr
  have hD : mass H w≤mass D w :=
    sum_le_sum_of_subset_of_nonneg hd (fun j jd _ => (X.pos j (X.rs (dr jd))).le)
  have q0 : (0:ℚ)≤q := Nat.cast_nonneg q
  have rdq : (q:ℚ)*mass (R\D) w+(q:ℚ)*mass D w=(q:ℚ)*mass R w := by rw [← mul_add,rd]
  have wq : (q:ℚ)*mass V w=(q:ℚ)*mass R w+(q:ℚ)*mass (V\R) w := by rw [whole,mul_add]
  have hDq := mul_le_mul_of_nonneg_left hD q0
  linarith

/-- At `q = 3` the inner ancestors respect the swapped-pair cap unless the root is heavy. -/
theorem inner_parents_compatible_three {E : CH.Digraph} {V R H D : Finset ℕ} {w : ℕ→ℚ} {c : ℚ}
    {a u v i : ℕ} (X : TwoExits 3 E V R H w c a u v) (free : QFree E V 3)
    (hd : H⊆D) (dr : D⊆R)
    (light : 9*w a≤5*c-18*(c-mass V w)+18*(w u+w v)+9*min (w u) (w v)-2*w i) :
    27*mass (R\D) w≤14*c-45*(c-mass V w)-2*w i := by
  have room := inner_parent_room (by norm_num) X free hd dr
  push_cast at room
  linarith

/-- General `q`: the inner ancestors respect the cap of `swapped_parent_cap` unless
`2q²·w(a) > 2q²c − 2q(q−1)(qσ + c) + (q−1)²(q−2)(c − w i) + 2q²((q−1)(w u + w v) + min)`. -/
theorem inner_parents_compatible {q : ℕ} {E : CH.Digraph} {V R H D : Finset ℕ} {w : ℕ→ℚ} {c : ℚ}
    {a u v i : ℕ} (hq : 2≤q) (X : TwoExits q E V R H w c a u v) (free : QFree E V q)
    (hd : H⊆D) (dr : D⊆R)
    (light : 2*(q:ℚ)^2*w a≤2*(q:ℚ)^2*c-2*(q:ℚ)*((q:ℚ)-1)*((q:ℚ)*(c-mass V w)+c)
      +((q:ℚ)-1)^2*((q:ℚ)-2)*(c-w i)+2*(q:ℚ)^2*(((q:ℚ)-1)*(w u+w v)+min (w u) (w v))) :
    2*(q:ℚ)^3*mass (R\D) w≤2*(q:ℚ)^2*((q:ℚ)-1)*c-2*(q:ℚ)^3*(c-mass V w)
      -2*(q:ℚ)*((q:ℚ)-1)*((q:ℚ)*(c-mass V w)+c)+((q:ℚ)-1)^2*((q:ℚ)-2)*(c-w i) := by
  have room := inner_parent_room hq X free hd dr
  have scaled := mul_le_mul_of_nonneg_left room (by positivity : (0:ℚ)≤2*(q:ℚ)^2)
  nlinarith

/-- The swapped-pair inequalities currently in Lean are jointly satisfiable at `q = 3`.
Variables: `c`, `σ`, the exit weights `wu, wv`, the joint row `wi`, the pair `wx, wy`, the
root `wa`, the overlap `Δ`, the exterior mass `mO`, the inner mass `mR`, the double-entrance
mass `mD` (it contains the heads, of weight `(c − wa)/3`), and the avoided set `mP`.
Constraints: both AB tests at zero residual, `bank_one` twice, `bank_two`, `overlap_cap`,
the joint row, `swapped_joint_bound`, the forward rectangle, `gap_bound`, the exterior
containing `a, u, v` and the overlap, the inner ball containing `D, i, x, y`, and
`P ⊇ (R ∖ D) ∪ {i, x, y}`. This is a point in these aggregated quantities, not a graph. -/
theorem aggregate_witness_three :
    ∃ c σ wu wv wi wx wy wa Δ mO mR mD mP : ℚ,
      0<σ ∧ 0<wu ∧ 0<wv ∧ 0<wi ∧ 0<wx ∧ 0<wy ∧ 0<wa ∧ 0<Δ ∧ 0<mP ∧
      c=σ+mR+mO ∧
      3*(σ+mO)-c≤2*(wu+2*wv) ∧ 3*(σ+mO)-c≤2*(wv+2*wu) ∧
      c+2*wu≤3*mO ∧ c+2*wv≤3*mO ∧ 2*c+2*(wu+wv)-3*Δ≤3*mO ∧
      3*Δ+min wu wv≤c ∧ 3*(wu+wv)≤c-wi ∧ 6*(3*σ+c-3*Δ)≤2*(c-wi) ∧
      3*mP+2*Δ≤3*(c-σ)-c ∧ σ+wu+wv≤(c-wa)-mR ∧
      wa+wu+wv≤mO ∧ Δ≤mO ∧ (c-wa)/3≤mD ∧ mD+wi+wx+wy≤mR ∧
      mR-mD≤mP ∧ wi+wx+wy≤mP ∧ 27*mP≤14*c-45*σ-2*wi := by
  refine ⟨1,1/100,1/7,1/7,1/10,1/100,1/100,3/10,1/4,76/125,1-1/100-76/125,1/4,1/5,?_⟩
  norm_num

#print axioms ancestor_no_return
#print axioms start_entry
#print axioms double_entrance
#print axioms swapped_parent_cap
#print axioms inner_parent_room
#print axioms inner_parents_compatible_three
#print axioms inner_parents_compatible
#print axioms aggregate_witness_three
end LeanCH.BR.Closure.SwappedParentRoom
