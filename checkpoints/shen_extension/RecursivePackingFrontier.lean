import checkpoints.shen_extension.RecursiveDeficitLevels
import checkpoints.shen_extension.TransitionClosureStatic
import checkpoints.shen_extension.MinimumOrderProfile
import LeanCH.BR.BRsubSat

/-! A source and a global packing minimum supplied by a literal counterexample.
The minimum is over every proper carrier reachable by the delete/add rules.
The degree one lower is valid by least failure at this same cutoff. -/
namespace LeanCH.BR.Closure.PackingFrontier
open BRq2 BRq3 BR45 Finset DeficitLevels

private def Fails (q j : ℕ) : Prop :=
  ∃ D U, U.Nonempty ∧ QFree D U q ∧ U.card ≤ q*j ∧ ∀ u∈U, j≤(outN D U u).card

/-- Data on one source and one minimizing state. -/
structure Frontier {q d : ℕ} (O : Origin q (d+1)) (st : State) : Prop where
  maximal : MaximalReturns q O.G O.V
  lower : OrderLaw q d (q*d+1)
  lower_degrees : ∀ k<d+1, OrderLaw q k (q*k+1)
  reached : Reach (RStep q (d+1)) O.init st
  proper : st.U.card < O.V.card
  minimum : ∀ t, Reach (RStep q (d+1)) O.init t → t.U.card < O.V.card →
    total (d+1) st.H st.U ≤ total (d+1) t.H t.U
  positive : 0 < total (d+1) st.H st.U
  alternative : total (d+1) st.H st.U = d+1 ∨
    (total (d+1) st.H st.U < d+1 ∧ ∃ g e,
      O.V.card+e=q*(d+1) ∧ O.V.card+g=st.U.card+total (d+1) st.H st.U ∧
      let t := (st.U.filter (fun u => 0<cost (d+1) st.H st.U u)).card
      total (d+1) st.H st.U + t*t + t*e ≤ t*(q+2*g))

/-- In every one-hole static packing of this saturated origin the only
admissible family is empty. The statement compares the exact fixed-carrier optimum. -/
theorem no_single_hole_family {q d : ℕ} {O : Origin q (d+1)}
    (maximal : MaximalReturns q O.G O.V) {v : ℕ} (hv : v∈O.V)
    {F : Finset (ℕ × ℕ)} (adm : Admissible O (O.V \ {v}) F) : F=∅ := by
  let U := O.V \ {v}
  have keep : ∀ a∈U, ∀ b∈U, O.G a b=true → addArcs O.G F a b=true := by
    intro a _ b _ h; simp [addArcs,h]
  have eq := one_hole_exact O.free maximal hv O.deg adm.free keep
  have val := shortfall_addArcs O adm
  change total (d+1) (addArcs O.G F) U = total (d+1) O.G U - F.card at val
  change total (d+1) (addArcs O.G F) U = total (d+1) O.G U at eq
  have bound : F.card ≤ total (d+1) O.G U := by
    rw [card_eq_sum_row adm.sub]
    exact sum_le_sum adm.rowCap
  exact card_eq_zero.mp (by omega)

/-- At a first failing degree choose a least-order saturated origin and an
actual global minimizer. No boundary regularity or lower-degree law is assumed. -/
theorem from_candidate {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (hq : 1≤q) (hf : QFree D V q) (live : V.Nonempty)
    (bound : V.card≤q*s) (degree : ∀ u∈V, s≤(outN D V u).card) :
    ∃ d, d+1≤s ∧ ∃ (O : Origin q (d+1)) (st : State), Frontier O st := by
  classical
  have fail : ∃ j, Fails q j := ⟨s,D,V,live,hf,bound,degree⟩
  let j := Nat.find fail
  have js : j≤s := Nat.find_min' fail ⟨D,V,live,hf,bound,degree⟩
  obtain ⟨G,W,wl,gf,ord,deg⟩ := Nat.find_spec fail
  change W.card≤q*j at ord
  have jp : j≠0 := by intro h; rw [h,Nat.mul_zero] at ord; have := card_pos.mpr wl; omega
  obtain ⟨d,ed⟩ := Nat.exists_eq_succ_of_ne_zero jp
  have loAll : ∀ k<d+1, OrderLaw q k (q*k+1) := by
    intro k hk F X ff fd xl
    by_contra! few
    have smaller := Nat.find_min' fail (show Fails q k from ⟨F,X,xl,ff,by omega,fd⟩)
    change j≤k at smaller
    omega
  have lo := loAll d (by omega)
  change ∀ u∈W, j≤(outN G W u).card at deg
  rw [ed] at deg ord js
  obtain ⟨X,xsize⟩ := ShenMinimumOrder.exists_source gf deg wl
  obtain ⟨H,keep,free,sat⟩ := BRsub.exists_satQ X.free
  have dh (u) (hu : u∈X.V) : d+1≤(outN H X.V u).card := by
    apply (X.degree u hu).trans (card_le_card ?_)
    intro z hz
    exact mem_outN.mpr ⟨(mem_outN.mp hz).1,keep _ hu _ (mem_outN.mp hz).1 (mem_outN.mp hz).2⟩
  let O : Origin q (d+1) := ⟨H,X.V,X.nonempty,xsize.trans ord,free,X.least,dh⟩
  have mx : MaximalReturns q O.G O.V := by
    intro u hu z hz no
    obtain ⟨_,k,le,back⟩ := mem_ball.mp (sat z hz u hu no)
    exact ⟨k,by omega,back⟩
  obtain ⟨v,hv⟩ := O.ne
  have off : v∉outN O.G O.V v := fun h => loopfree O.free hq hv (mem_outN.mp h).2
  have two : 1<O.V.card := by
    have inc : insert v (outN O.G O.V v) ⊆ O.V := insert_subset hv outN_subset
    have le := card_le_card inc
    rw [card_insert_of_notMem off] at le
    have := O.deg v hv
    omega
  let single : State := ⟨{v},O.G⟩
  have sub : ({v}:Finset ℕ) ⊂ O.V := ⟨singleton_subset_iff.mpr hv, fun h => by
    have := card_le_card h
    simp only [card_singleton] at this
    omega⟩
  have route : Reach (RStep q (d+1)) O.init single :=
    Relation.ReflTransGen.single (Or.inl ⟨rfl,sub,singleton_nonempty v⟩)
  have singleVal : total (d+1) single.H single.U=d+1 := by
    have no := loopfree O.free hq hv
    have empty : outN O.G {v} v = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨h,e⟩ := mem_outN.mp hz
      exact no ((mem_singleton.mp h) ▸ e)
    simp [total,cost,single,empty]
  let HasCost (k : ℕ) := ∃ t : State, Reach (RStep q (d+1)) O.init t ∧ t.U.card<O.V.card ∧
      total (d+1) t.H t.U=k
  have any : ∃ k, HasCost k := ⟨d+1,single,route,by simpa [single],singleVal⟩
  obtain ⟨st,rr,prop,price⟩ := Nat.find_spec any
  have valid := rreach_valid O rr
  have minCost (t : State) (rt : Reach (RStep q (d+1)) O.init t) (pr : t.U.card<O.V.card) :
      total (d+1) st.H st.U ≤ total (d+1) t.H t.U := by
    rw [price]
    exact Nat.find_min' any ⟨t,rt,pr,rfl⟩
  have atMost := minCost single route (by simpa [single])
  rw [singleVal] at atMost
  have pos : 0<total (d+1) st.H st.U := by
    by_contra! z
    apply valid_not_paid O valid prop
    intro u hu
    have le := single_le_sum (s:=st.U) (f:=cost (d+1) st.H st.U) (fun _ _ => Nat.zero_le _) hu
    change (d+1)-(outN st.H st.U u).card ≤ total (d+1) st.H st.U at le
    omega
  refine ⟨d,js,O,st,mx,lo,loAll,rr,prop,minCost,pos,?_⟩
  rcases lt_or_eq_of_le atMost with small|eq
  · right
    have heads (u) (hu : u∈st.U) : 1≤(outN st.H st.U u).card := by
      have le := single_le_sum (s:=st.U) (f:=cost (d+1) st.H st.U) (fun _ _ => Nat.zero_le _) hu
      change (d+1)-(outN st.H st.U u).card ≤ total (d+1) st.H st.U at le
      omega
    have clone := BRsGen.deficiency_bound_of_size O.least valid.2.2 heads valid.2.1
    change O.V.card≤st.U.card+total (d+1) st.H st.U at clone
    obtain ⟨g,gap⟩ := Nat.exists_eq_add_of_le clone
    obtain ⟨e,extra⟩ := Nat.exists_eq_add_of_le O.order
    exact ⟨small,g,e,extra.symm,gap.symm,valid_budget O valid lo hq extra.symm gap.symm small⟩
  · exact Or.inl eq

#print axioms no_single_hole_family
#print axioms from_candidate
/-- At the maximal shortfall, deleting any vertex exhibits at least s
different degree-s parents. A source with surplus cannot have this profile. -/
theorem high_parents {q d : ℕ} {O : Origin q (d+1)} {st : State}
    (fr : Frontier O st) (high : total (d+1) st.H st.U=d+1) (hq : 1≤q) (v) (hv : v∈O.V) :
    d+1 ≤ (O.V.filter (fun u => (outN O.G O.V u).card=d+1 ∧ O.G u v=true)).card := by
  classical
  let W := O.V.erase v
  have dne : v∉outN O.G O.V v := fun h => loopfree O.free hq hv (mem_outN.mp h).2
  obtain ⟨z,hz⟩ := card_pos.mp (show 0<(outN O.G O.V v).card by have := O.deg v hv; omega)
  have live : W.Nonempty := ⟨z,mem_erase.mpr ⟨fun e => dne (e ▸ hz),outN_subset hz⟩⟩
  have route : Reach (RStep q (d+1)) O.init ⟨W,O.G⟩ :=
    Relation.ReflTransGen.single (Or.inl ⟨rfl,erase_ssubset hv,live⟩)
  have min := fr.minimum _ route (card_lt_card (erase_ssubset hv))
  rw [high] at min
  let w (u : ℕ) : ℕ := if (outN O.G O.V u).card=d+1 ∧ O.G u v=true then 1 else 0
  have row (u) (hu : u∈W) : cost (d+1) O.G W u=w u := by
    have er : outN O.G W u = (outN O.G O.V u).erase v := by
      ext a; simp only [W,mem_outN,mem_erase]; tauto
    have orig := O.deg _ (mem_of_mem_erase hu)
    unfold cost
    rw [er]
    by_cases e : O.G u v=true
    · rw [card_erase_of_mem (mem_outN.mpr ⟨hv,e⟩)]
      simp only [w,e,and_true]
      split_ifs <;> omega
    · have none : v∉outN O.G O.V u := fun h => e (mem_outN.mp h).2
      rw [erase_eq_of_notMem none]
      simp [w,e]; omega
  have eq := sum_congr rfl row
  have sum0 := sum_erase_add O.V w hv
  have zero : w v=0 := by simp [w,loopfree O.free hq hv]
  rw [zero, Nat.add_zero] at sum0
  rw [card_filter]
  change d+1 ≤ ∑ u∈O.V, w u
  change d+1 ≤ ∑ u∈W, cost (d+1) O.G W u at min
  exact min.trans_eq (eq.trans sum0)

/-- The high branch gives a saturated biregular graph at the least failing degree. -/
theorem high_regular {q d : ℕ} {O : Origin q (d+1)} {st : State} (fr : Frontier O st)
    (high : total (d+1) st.H st.U=d+1) (hq : 1≤q) :
    ∀ v∈O.V, (outN O.G O.V v).card=d+1 ∧ (inN O.G O.V v).card=d+1 := by
  classical
  let p (v : ℕ) := (O.V.filter (fun u => (outN O.G O.V u).card=d+1 ∧ O.G u v=true)).card
  let T := O.V.filter (fun u => (outN O.G O.V u).card=d+1)
  have low (v) (hv : v∈O.V) : d+1≤p v := high_parents fr high hq _ hv
  have columns : ∑ v∈O.V, p v = T.card*(d+1) := by
    simp only [p,card_filter]
    rw [sum_comm]
    have per (u) (_hu : u∈O.V) :
        (∑ v∈O.V, if (outN O.G O.V u).card=d+1 ∧ O.G u v=true then 1 else (0:ℕ)) =
        if u∈T then d+1 else 0 := by
      by_cases eq : (outN O.G O.V u).card=d+1
      · have hit : u∈T := mem_filter.mpr ⟨_hu,eq⟩
        simp only [eq,true_and,hit,ite_true]
        rw [← card_filter]
        exact eq
      · have miss : u∉T := fun h => eq (mem_filter.mp h).2
        simp [eq,miss]
    rw [sum_congr rfl per, ← sum_filter]
    have e : O.V.filter (fun x => x∈T) = T := by
      ext x; exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨(mem_filter.mp h).1,h⟩⟩
    simp [e]
  have atLeast := sum_le_sum low
  simp only [sum_const,Nat.nsmul_eq_mul,columns] at atLeast
  have tls : T⊆O.V := filter_subset _ _
  have equal : T=O.V := eq_of_subset_of_card_le tls
    ((Nat.mul_le_mul_right_iff (by omega : 0<d+1)).mp atLeast)
  have out (v) (hv : v∈O.V) : (outN O.G O.V v).card=d+1 :=
    (mem_filter.mp (show v∈T by rwa [equal])).2
  rw [equal] at columns
  intro v hv
  refine ⟨out v hv,?_⟩
  have pc : p v = (inN O.G O.V v).card := by
    apply congrArg Finset.card
    ext u
    simp only [mem_filter,mem_inN]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,out _ h.1,h.2⟩⟩
  have eqp : p v = d+1 := by
    by_contra no
    have strict := sum_lt_sum low ⟨v,hv,lt_of_le_of_ne (low v hv) (Ne.symm no)⟩
    simp only [sum_const,Nat.nsmul_eq_mul,columns,lt_self_iff_false] at strict
  exact pc.symm.trans eqp

#print axioms high_parents
#print axioms high_regular
/-- At exact clone cost there is at least one strict row in the rectangle
bound. This bounds the number of missing vertices independently of degree. -/
theorem equality_radius {q d e : ℕ} {O : Origin q (d+1)} {st : State}
    (fr : Frontier O st) (hq : 1≤q) (size : O.V.card+e=q*(d+1))
    (exactCost : O.V.card=st.U.card+total (d+1) st.H st.U)
    (small : total (d+1) st.H st.U < d+1) :
    4*(total (d+1) st.H st.U+1) ≤ (q-e)^2 := by
  classical
  let T := st.U.filter (fun u => 0<cost (d+1) st.H st.U u)
  let a := cost (d+1) st.H st.U
  have sumT : (∑ u∈T, a u) = total (d+1) st.H st.U := by
    unfold T total a
    rw [sum_filter]
    apply sum_congr rfl
    intro u _
    split_ifs <;> omega
  have live : T.Nonempty := by
    by_contra! none
    have pos := fr.positive
    simp [none] at sumT
    omega
  have valid := rreach_valid O fr.reached
  have sub : T⊆st.U := filter_subset _ _
  have short (v) (hv : v∈T) : 0<a v := (mem_filter.mp hv).2
  have atRow (v) (hv : v∈T) : a v+T.card+e≤q := by
    simpa using row_and_column (g:=0) valid.2.2 O.least fr.lower hq size
      (by simpa using exactCost) small sub short hv
  obtain ⟨v,hv⟩ := (show T.Nonempty from live)
  have cap := atRow v hv
  have few : T.card≤q := by omega
  obtain ⟨w,hw,source⟩ := exists_sink (valid.2.2.reverse.mono_set sub) live few
  have cut := short_row_price (s:=d+1) valid.2.2 (by simpa using fr.lower) hq small (sub hw)
    (short w hw) (erase_subset_erase w sub)
    (fun u hu => ⟨short _ (mem_of_mem_erase hu),source _ (mem_of_mem_erase hu)⟩)
  rw [card_erase_of_mem hw] at cut
  rw [Nat.mul_add,Nat.mul_one] at size
  have tpos := card_pos.mpr live
  change q*d+1+1+a w+(T.card-1)≤st.U.card+total (d+1) st.H st.U at cut
  have one : a w+T.card<q-e := by omega
  have costs := sum_lt_sum (s:=T) (f:=fun u => a u+T.card) (g:=fun _ => q-e)
    (fun u hu => by have := atRow u hu; omega) ⟨w,hw,one⟩
  simp only [sum_add_distrib,sumT,sum_const,Nat.nsmul_eq_mul] at costs
  have integral : total (d+1) st.H st.U+1 + T.card*T.card ≤ T.card*(q-e) := by omega
  zify at integral ⊢
  nlinarith [sq_nonneg (2*(T.card:ℤ)-((q-e:ℕ):ℤ))]

#print axioms equality_radius
end LeanCH.BR.Closure.PackingFrontier
