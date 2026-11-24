import checkpoints.pair_tilt_20261119.PairTilt
import checkpoints.shen_extension.CommonParentEndpointPath

/-! # The covered endpoint child `W = R ∪ {z}`: exact elimination of the exit price

Fix prices `y ≥ 0` on the inner ball `R` and put `t` on the dead exit `z`. Write
`m = y(R)`, `ρ i = row q E R y i` (the row of `i` inside `R`) and `q₁ = q-1`. The hypotheses
of `PairTilt.tilt_pays` on `W` are `Pays q E W H (exitTilt y z t)`.

* `t = 0` (`pays_zero_iff`): the exit is cut; what remains is `m < q·y(H)` and `m < ρ i` on `R`.
* `t > 0` (`pays_pos_iff`): rows `a → z` give lower bounds `q·m − q₁ρ a < q₁²·t`;
  rows `b ↛ z` give upper bounds `q₁·t < q₁ρ b − q·m`; heads give `m + t < q·y(H)`.
* Elimination (`exit_price_iff`): a price `t > 0` exists iff
  (H0) `m < q·y(H)`, (B0) `q·m < q₁ρ b` for every `b ↛ z`,
  (AB) `q²m < q₁(ρ a + q₁ρ b)` for every `a → z`, `b ↛ z`,
  (AH) `q·m − q₁ρ a < q₁²(q·y(H) − m)` for every `a → z`.
* `labelled_obstruction`: on a least source one of these fails at actual labels, for every `y`.
* Structure (`near_rows_miss_exit`, `exit_entered`): rows within `q-3` steps of `H`, in
  particular all heads, miss `z`; some inner row enters `z`. Both sides are populated.
* Native prices (`native_rows`, `native_obstruction`): with flat rows `c`, `ρ i = c − q·L i`,
  where `L i` is the native mass `i` sends outside `R`. Every test becomes a leakage bound
  against `Q = q(c − w(V) + w(V∖R)) − c`, and `native_slack` gives `Q ≥ qσ + q₁·w(z)`. -/
namespace LeanCH.BR.Closure.DeadExit
open Finset BRq2 BRq3 BR45 WeightedSD

/-- The hypotheses of `PairTilt.tilt_pays` on carrier `W`, heads `H`, tilt `y`. -/
def Pays (q : ℕ) (E : CH.Digraph) (W H : Finset ℕ) (y : ℕ→ℚ) : Prop :=
  mass W y<q*mass H y ∧
  (∀i∈BRsub.ballSet E W H (q-2),mass W y<WeightedSD.row q E W y i) ∧
  ∀i∈BRsub.ballSet E W H (q-2),∀j∈W\BRsub.ballSet E W H (q-2),0<y j →
    mass W y<((q:ℚ)-1)*(WeightedSD.row q E W y i-mass W y)+WeightedSD.row q E W y j

/-- Prices `y` on the inner ball and `t` on the exit. -/
def exitTilt (y : ℕ→ℚ) (z : ℕ) (t : ℚ) : ℕ→ℚ := fun v => if v=z then t else y v

theorem tilt_off {y : ℕ→ℚ} {z : ℕ} {t : ℚ} (v : ℕ) (ne : v≠z) : exitTilt y z t v=y v := by
  simp [exitTilt,ne]
theorem tilt_at (y : ℕ→ℚ) (z : ℕ) (t : ℚ) : exitTilt y z t z=t := by simp [exitTilt]

theorem mass_tilt {R : Finset ℕ} {z : ℕ} (zr : z∉R) (y : ℕ→ℚ) (t : ℚ) :
    mass (insert z R) (exitTilt y z t)=mass R y+t := by
  have e : ∑v∈R,exitTilt y z t v=∑v∈R,y v :=
    sum_congr rfl (fun v vr => tilt_off v (fun h => zr (h ▸ vr)))
  unfold mass
  rw [sum_insert zr,e,tilt_at]
  ring

theorem mass_tilt_sub {R S : Finset ℕ} {z : ℕ} (zr : z∉R) (ss : S⊆R) (y : ℕ→ℚ) (t : ℚ) :
    mass S (exitTilt y z t)=mass S y :=
  sum_congr rfl (fun v vs => tilt_off v (fun h => zr (h ▸ ss vs)))

theorem row_tilt_inner (q : ℕ) (E : CH.Digraph) {R : Finset ℕ} {z : ℕ} (zr : z∉R)
    (y : ℕ→ℚ) (t : ℚ) {i : ℕ} (ir : i∈R) :
    WeightedSD.row q E (insert z R) (exitTilt y z t) i=
      WeightedSD.row q E R y i+q*(if E i z=true then t else 0) := by
  have e : (∑v∈R,if E i v=true then exitTilt y z t v else 0)=∑v∈R,if E i v=true then y v else 0 :=
    sum_congr rfl (fun v vr => by
      have vz : v≠z := fun h => zr (h ▸ vr)
      rw [tilt_off (y:=y) (t:=t) v vz])
  have iz : i≠z := fun h => zr (h ▸ ir)
  unfold WeightedSD.row outW
  rw [sum_insert zr,e,tilt_at,tilt_off (y:=y) (t:=t) i iz]
  ring

theorem row_tilt_exit (q : ℕ) (E : CH.Digraph) {R : Finset ℕ} {z : ℕ}
    (dead : ∀v∈insert z R,E z v=false) (y : ℕ→ℚ) (t : ℚ) :
    WeightedSD.row q E (insert z R) (exitTilt y z t) z=t := by
  have e : (∑v∈insert z R,if E z v=true then exitTilt y z t v else 0)=0 :=
    sum_eq_zero (fun v vw => by simp [dead v vw])
  unfold WeightedSD.row outW
  rw [e,tilt_at]
  ring

/-- The tilt hypotheses on the dead-exit child, written on the inner ball. -/
theorem pays_iff (q : ℕ) (E : CH.Digraph) {R H : Finset ℕ} {z : ℕ} (hs : H⊆R) (zr : z∉R)
    (dead : ∀v∈insert z R,E z v=false) (ball : BRsub.ballSet E (insert z R) H (q-2)=R)
    (y : ℕ→ℚ) (t : ℚ) :
    Pays q E (insert z R) H (exitTilt y z t) ↔
      mass R y+t<q*mass H y ∧
      (∀i∈R,mass R y+t<WeightedSD.row q E R y i+q*(if E i z=true then t else 0)) ∧
      (0<t → ∀i∈R,mass R y<((q:ℚ)-1)*
        (WeightedSD.row q E R y i+q*(if E i z=true then t else 0)-(mass R y+t))) := by
  have out : insert z R\R={z} := by
    ext j
    simp only [mem_sdiff,mem_insert,mem_singleton]
    constructor
    · rintro ⟨h|h,n⟩
      · exact h
      · exact absurd h n
    · rintro rfl
      exact ⟨Or.inl rfl,zr⟩
  unfold Pays
  rw [ball,out,mass_tilt zr,mass_tilt_sub zr hs]
  constructor
  · rintro ⟨heavy,inner,pair⟩
    refine ⟨heavy,fun i ir => ?_,fun tp i ir => ?_⟩
    · have h := inner i ir
      rwa [row_tilt_inner q E zr y t ir] at h
    · have h := pair i ir z (mem_singleton_self z) (by rwa [tilt_at])
      rw [row_tilt_inner q E zr y t ir,row_tilt_exit q E dead y t] at h
      linarith
  · rintro ⟨heavy,inner,pair⟩
    refine ⟨heavy,fun i ir => ?_,fun i ir j jz jp => ?_⟩
    · rw [row_tilt_inner q E zr y t ir]; exact inner i ir
    · obtain rfl := mem_singleton.mp jz
      rw [tilt_at] at jp
      rw [row_tilt_inner q E zr y t ir,row_tilt_exit q E dead y t]
      linarith [pair jp i ir]

/-- `t = 0`: the exit is cut, the paired test is vacuous. -/
theorem pays_zero_iff (q : ℕ) (E : CH.Digraph) {R H : Finset ℕ} {z : ℕ} (hs : H⊆R) (zr : z∉R)
    (dead : ∀v∈insert z R,E z v=false) (ball : BRsub.ballSet E (insert z R) H (q-2)=R)
    (y : ℕ→ℚ) :
    Pays q E (insert z R) H (exitTilt y z 0) ↔
      mass R y<q*mass H y ∧ ∀i∈R,mass R y<WeightedSD.row q E R y i := by
  rw [pays_iff q E hs zr dead ball y 0]
  constructor
  · rintro ⟨h,i,_⟩
    exact ⟨by simpa using h,fun j jr => by simpa using i j jr⟩
  · rintro ⟨h,i⟩
    exact ⟨by simpa using h,fun j jr => by simpa using i j jr,fun t0 => absurd t0 (lt_irrefl 0)⟩

/-- `t > 0`: rows entering the exit bound the price from below, rows missing it from above. -/
theorem pays_pos_iff {q : ℕ} (hq : 2≤q) (E : CH.Digraph) {R H : Finset ℕ} {z : ℕ} (hs : H⊆R)
    (zr : z∉R) (dead : ∀v∈insert z R,E z v=false) (ball : BRsub.ballSet E (insert z R) H (q-2)=R)
    (y : ℕ→ℚ) (mnn : 0≤mass R y) {t : ℚ} (tp : 0<t) :
    Pays q E (insert z R) H (exitTilt y z t) ↔
      mass R y+t<q*mass H y ∧
      (∀i∈R,E i z=true → q*mass R y-((q:ℚ)-1)*WeightedSD.row q E R y i<((q:ℚ)-1)^2*t) ∧
      (∀i∈R,E i z=false → ((q:ℚ)-1)*t<((q:ℚ)-1)*WeightedSD.row q E R y i-q*mass R y) := by
  rw [pays_iff q E hs zr dead ball y t]
  have q1 : (0:ℚ)<(q:ℚ)-1 := by
    have : (2:ℚ)≤q := by exact_mod_cast hq
    linarith
  constructor
  · rintro ⟨heavy,_,pair⟩
    refine ⟨heavy,fun i ir hz => ?_,fun i ir hz => ?_⟩
    · have h := pair tp i ir
      simp only [hz,ite_true] at h
      nlinarith
    · have h := pair tp i ir
      simp only [hz,Bool.false_eq_true,ite_false,mul_zero,add_zero] at h
      nlinarith
  · rintro ⟨heavy,lowA,upB⟩
    have pair : ∀i∈R,mass R y<((q:ℚ)-1)*
        (WeightedSD.row q E R y i+q*(if E i z=true then t else 0)-(mass R y+t)) := by
      intro i ir
      cases hz : E i z
      · have h := upB i ir hz
        simp only [Bool.false_eq_true,ite_false,mul_zero,add_zero]
        nlinarith
      · have h := lowA i ir hz
        simp only [ite_true]
        nlinarith
    refine ⟨heavy,fun i ir => ?_,fun _ => pair⟩
    have h := pair i ir
    by_contra! le
    have := mul_le_mul_of_nonneg_left (sub_nonpos.mpr le) q1.le
    linarith

/-- Fourier–Motzkin for one variable with a fixed lower bound 0 and a fixed upper bound. -/
theorem fm_exists {α : Type} (SA SB : Finset α) (ℓ u : α→ℚ) (uH : ℚ) (h0 : 0<uH)
    (hB : ∀b∈SB,0<u b) (hA : ∀a∈SA,ℓ a<uH) (hAB : ∀a∈SA,∀b∈SB,ℓ a<u b) :
    ∃t:ℚ,0<t ∧ t<uH ∧ (∀a∈SA,ℓ a<t) ∧ ∀b∈SB,t<u b := by
  obtain ⟨L,L0,Lge,LH,LB⟩ : ∃L:ℚ,0≤L ∧ (∀a∈SA,ℓ a≤L) ∧ L<uH ∧ ∀b∈SB,L<u b := by
    rcases SA.eq_empty_or_nonempty with e|ne
    · exact ⟨0,le_rfl,fun a ha => by simp [e] at ha,h0,hB⟩
    · obtain ⟨a,ha,top⟩ := SA.exists_max_image ℓ ne
      exact ⟨max 0 (ℓ a),le_max_left _ _,fun x hx => (top x hx).trans (le_max_right _ _),
        max_lt h0 (hA a ha),fun b hb => max_lt (hB b hb) (hAB a ha b hb)⟩
  obtain ⟨U,LU,UH,UB⟩ : ∃U:ℚ,L<U ∧ U≤uH ∧ ∀b∈SB,U≤u b := by
    rcases SB.eq_empty_or_nonempty with e|ne
    · exact ⟨uH,LH,le_rfl,fun b hb => by simp [e] at hb⟩
    · obtain ⟨b,hb,bot⟩ := SB.exists_min_image u ne
      exact ⟨min uH (u b),lt_min LH (LB b hb),min_le_left _ _,
        fun x hx => (min_le_right _ _).trans (bot x hx)⟩
  refine ⟨(L+U)/2,by linarith,by linarith,fun a ha => by linarith [Lge a ha],
    fun b hb => by linarith [UB b hb]⟩

/-- Exact elimination of the exit price on fixed inner prices. -/
theorem exit_price_iff {q : ℕ} (hq : 2≤q) (E : CH.Digraph) (R : Finset ℕ) (z : ℕ)
    (ρ : ℕ→ℚ) (m h : ℚ) :
    (∃t:ℚ,0<t ∧ m+t<q*h ∧ (∀i∈R,E i z=true → q*m-((q:ℚ)-1)*ρ i<((q:ℚ)-1)^2*t) ∧
        ∀i∈R,E i z=false → ((q:ℚ)-1)*t<((q:ℚ)-1)*ρ i-q*m) ↔
      m<q*h ∧ (∀b∈R,E b z=false → q*m<((q:ℚ)-1)*ρ b) ∧
      (∀a∈R,E a z=true → ∀b∈R,E b z=false → (q:ℚ)^2*m<((q:ℚ)-1)*(ρ a+((q:ℚ)-1)*ρ b)) ∧
      ∀a∈R,E a z=true → q*m-((q:ℚ)-1)*ρ a<((q:ℚ)-1)^2*(q*h-m) := by
  classical
  have q1 : (0:ℚ)<(q:ℚ)-1 := by
    have : (2:ℚ)≤q := by exact_mod_cast hq
    linarith
  have q2 : (0:ℚ)<((q:ℚ)-1)^2 := pow_pos q1 2
  constructor
  · rintro ⟨t,tp,heavy,lowA,upB⟩
    refine ⟨by linarith,fun b hb hz => ?_,fun a ha az b hb bz => ?_,fun a ha az => ?_⟩
    · have := upB b hb hz
      nlinarith
    · have la := lowA a ha az
      have ub := mul_lt_mul_of_pos_left (upB b hb bz) q1
      nlinarith
    · have la := lowA a ha az
      have hh := mul_lt_mul_of_pos_left (show t<q*h-m by linarith) q2
      linarith
  · rintro ⟨H0,B0,AB,AH⟩
    let SA := R.filter (fun i => E i z=true)
    let SB := R.filter (fun i => E i z=false)
    let ℓ : ℕ→ℚ := fun a => (q*m-((q:ℚ)-1)*ρ a)/((q:ℚ)-1)^2
    let u : ℕ→ℚ := fun b => (((q:ℚ)-1)*ρ b-q*m)/((q:ℚ)-1)
    obtain ⟨t,tp,tH,tA,tB⟩ := fm_exists SA SB ℓ u (q*h-m) (by linarith)
      (fun b hb => by
        obtain ⟨br,bz⟩ := mem_filter.mp hb
        exact div_pos (by linarith [B0 b br bz]) q1)
      (fun a ha => by
        obtain ⟨ar,az⟩ := mem_filter.mp ha
        rw [div_lt_iff₀ q2]
        linarith [AH a ar az])
      (fun a ha b hb => by
        obtain ⟨ar,az⟩ := mem_filter.mp ha
        obtain ⟨br,bz⟩ := mem_filter.mp hb
        rw [div_lt_div_iff₀ q2 q1]
        have key := mul_lt_mul_of_pos_left (AB a ar az b br bz) q1
        nlinarith)
    refine ⟨t,tp,by linarith,fun a ar az => ?_,fun b br bz => ?_⟩
    · have := tA a (mem_filter.mpr ⟨ar,az⟩)
      rw [div_lt_iff₀ q2] at this
      linarith
    · have := tB b (mem_filter.mpr ⟨br,bz⟩)
      rw [lt_div_iff₀ q1] at this
      linarith

/-- A positive exit price exists exactly when the four labelled tests pass. -/
theorem exit_exists_iff {q : ℕ} (hq : 2≤q) (E : CH.Digraph) {R H : Finset ℕ} {z : ℕ} (hs : H⊆R)
    (zr : z∉R) (dead : ∀v∈insert z R,E z v=false) (ball : BRsub.ballSet E (insert z R) H (q-2)=R)
    (y : ℕ→ℚ) (mnn : 0≤mass R y) :
    (∃t:ℚ,0<t ∧ Pays q E (insert z R) H (exitTilt y z t)) ↔
      mass R y<q*mass H y ∧
      (∀b∈R,E b z=false → q*mass R y<((q:ℚ)-1)*WeightedSD.row q E R y b) ∧
      (∀a∈R,E a z=true → ∀b∈R,E b z=false →
        (q:ℚ)^2*mass R y<((q:ℚ)-1)*(WeightedSD.row q E R y a+((q:ℚ)-1)*WeightedSD.row q E R y b)) ∧
      ∀a∈R,E a z=true → q*mass R y-((q:ℚ)-1)*WeightedSD.row q E R y a<
        ((q:ℚ)-1)^2*(q*mass H y-mass R y) := by
  rw [← exit_price_iff hq E R z (WeightedSD.row q E R y) (mass R y) (mass H y)]
  constructor
  · rintro ⟨t,tp,p⟩
    exact ⟨t,tp,(pays_pos_iff hq E hs zr dead ball y mnn tp).mp p⟩
  · rintro ⟨t,tp,p⟩
    exact ⟨t,tp,(pays_pos_iff hq E hs zr dead ball y mnn tp).mpr p⟩

/-- On a least source no exit price works, at either end. -/
theorem dead_exit_closed {q : ℕ} {D E : CH.Digraph} {V R H : Finset ℕ} {z : ℕ} (hq : 2≤q)
    (free : QFree D V q) (small : SmallerSmallRow q V.card) (sub : ∀i j,E i j=true → D i j=true)
    (inside : insert z R⊆V) (room : (insert z R).card+1<V.card) (hs : H⊆R) (live : H.Nonempty)
    (y : ℕ→ℚ) (nonneg : ∀v∈R,0≤y v) (t : ℚ) (tn : 0≤t) :
    ¬Pays q E (insert z R) H (exitTilt y z t) := by
  rintro ⟨heavy,inner,pair⟩
  refine PairTilt.no_tilt hq free small (insert z R) H E (exitTilt y z t) inside room sub
    (hs.trans (subset_insert _ _)) live ?_ heavy inner pair
  intro v vw
  by_cases e : v=z
  · rw [e,tilt_at]; exact tn
  · rw [tilt_off v e]; exact nonneg v ((mem_insert.mp vw).resolve_left e)

/-- Every inner pricing of the dead-exit child fails at actual labels. `t = 0` fails at a
small row of the inner ball (or at the heads); every `t > 0` fails at one of four tests. -/
theorem labelled_obstruction {q : ℕ} {D E : CH.Digraph} {V R H : Finset ℕ} {z : ℕ} (hq : 2≤q)
    (free : QFree D V q) (small : SmallerSmallRow q V.card) (sub : ∀i j,E i j=true → D i j=true)
    (inside : insert z R⊆V) (room : (insert z R).card+1<V.card) (hs : H⊆R) (live : H.Nonempty)
    (zr : z∉R) (dead : ∀v∈insert z R,E z v=false) (ball : BRsub.ballSet E (insert z R) H (q-2)=R)
    (y : ℕ→ℚ) (nonneg : ∀v∈R,0≤y v) :
    (q*mass H y≤mass R y ∨ ∃i∈R,WeightedSD.row q E R y i≤mass R y) ∧
    (q*mass H y≤mass R y ∨
      (∃b∈R,E b z=false ∧ ((q:ℚ)-1)*WeightedSD.row q E R y b≤q*mass R y) ∨
      (∃a∈R,E a z=true ∧ ∃b∈R,E b z=false ∧
        ((q:ℚ)-1)*(WeightedSD.row q E R y a+((q:ℚ)-1)*WeightedSD.row q E R y b)≤(q:ℚ)^2*mass R y) ∨
      ∃a∈R,E a z=true ∧ ((q:ℚ)-1)^2*(q*mass H y-mass R y)≤
        q*mass R y-((q:ℚ)-1)*WeightedSD.row q E R y a) := by
  have mnn : 0≤mass R y := mass_nonneg nonneg
  have closed := dead_exit_closed hq free small sub inside room hs live y nonneg
  constructor
  · by_contra! no
    exact closed 0 le_rfl ((pays_zero_iff q E hs zr dead ball y).mpr ⟨no.1,no.2⟩)
  · by_contra! no
    obtain ⟨t,tp,p⟩ := (exit_exists_iff hq E hs zr dead ball y mnn).mpr
      ⟨no.1,no.2.1,no.2.2.1,no.2.2.2⟩
    exact closed t tp.le p

/-! ## Which rows sit on which side -/

/-- A row within `q-3` steps of the heads never enters an exit outside the inner ball.
For `q ≥ 3` this includes every head. -/
theorem near_rows_miss_exit {q : ℕ} {E : CH.Digraph} {U H : Finset ℕ} {z : ℕ} (hq : 3≤q)
    (zu : z∈U) (zr : z∉BRsub.ballSet E U H (q-2)) :
    ∀r∈BRsub.ballSet E U H (q-3),E r z=false := by
  intro r rr
  apply Bool.eq_false_iff.mpr
  intro e
  apply zr
  obtain ⟨h,hh,hit⟩ := BRsub.mem_ballSet.mp rr
  have step := ball_step hit zu e
  rw [show q-3+1=q-2 by omega] at step
  exact BRsub.mem_ballSet.mpr ⟨h,hh,step⟩

theorem heads_miss_exit {q : ℕ} {E : CH.Digraph} {U H : Finset ℕ} {z : ℕ} (hq : 3≤q)
    (hs : H⊆U) (zu : z∈U) (zr : z∉BRsub.ballSet E U H (q-2)) : ∀h∈H,E h z=false :=
  fun h hh => near_rows_miss_exit hq zu zr h
    (BRsub.mem_ballSet.mpr ⟨h,hh,self_mem_ball (hs hh)⟩)

/-- At a covered endpoint the exit is entered from the inner ball: the lower-bound side is
populated. -/
theorem exit_entered {q : ℕ} {E : CH.Digraph} {U H T : Finset ℕ} (hq : 3≤q) (free : QFree E U q)
    (hs : H⊆U) (hl : H.Nonempty) (ts : T⊆U) (size : T.card<q)
    (cover : ∀r∈BRsub.ballSet E U H (q-2),∃k∈T,E r k=true)
    {z : ℕ} (zt : z∈T\BRsub.ballSet E U H (q-2)) :
    ∃a∈BRsub.ballSet E U H (q-2),E a z=true := by
  obtain ⟨_,_,s,st,p,len,_,_,entry,single,_,_,_⟩ :=
    CommonParentEndpointPath.full_cover (by omega) free hs hl ts size cover
  have zp : z=p.vertex p.len := mem_singleton.mp (single ▸ zt)
  obtain ⟨h,hh⟩ := hl
  have first : E h (p.vertex 0)=true := p.start.symm ▸ (entry h hh s st).2 rfl
  have walk : Walk E U h (p.vertex p.len) (p.len-0+1) :=
    .step (ts (p.mem 0 (Nat.zero_le _))) first ((p.walk (Nat.zero_le _) le_rfl).mono ts)
  have zu : z∈U := ts (mem_sdiff.mp zt).1
  have far : z∉ball E U h (q-2) := fun hit =>
    (mem_sdiff.mp zt).2 (BRsub.mem_ballSet.mpr ⟨h,hh,hit⟩)
  have near : z∈ball E U h (q-2+1) := by
    rw [zp] at zu ⊢
    exact mem_ball.mpr ⟨zu,p.len-0+1,by omega,walk⟩
  obtain ⟨a,ab,az⟩ := ball_succ_pred (hs hh) near far
  exact ⟨a,BRsub.mem_ballSet.mpr ⟨h,hh,ab⟩,az⟩

/-- The child carrier of the covered replay is exactly `insert z R`. -/
theorem carrier_eq {C R : Finset ℕ} {z : ℕ} (rc : R⊆C) (one : C\R={z}) : C=insert z R := by
  ext v
  constructor
  · intro vc
    by_cases vr : v∈R
    · exact mem_insert_of_mem vr
    · exact mem_insert.mpr (Or.inl (mem_singleton.mp (one ▸ mem_sdiff.mpr ⟨vc,vr⟩)))
  · intro vi
    rcases mem_insert.mp vi with rfl|vr
    · exact (mem_sdiff.mp (one.symm ▸ mem_singleton_self v : v∈C\R)).1
    · exact rc vr

/-! ## Native prices -/

/-- With flat native rows, the inner row of `i` is the common value less `q` times the native
mass that `i` sends outside the inner ball. -/
theorem native_rows {q : ℕ} {E : CH.Digraph} {V R : Finset ℕ} {w : ℕ→ℚ} {c : ℚ} (rs : R⊆V)
    (flat : ∀i∈V,WeightedSD.row q E V w i=c) :
    ∀i∈R,WeightedSD.row q E R w i=c-q*mass ((V\R).filter (fun v => E i v=true)) w := by
  intro i ir
  have e := flat i (rs ir)
  have split := sum_sdiff rs (f:=fun v => if E i v=true then w v else 0)
  have leak : mass ((V\R).filter (fun v => E i v=true)) w=
      ∑v∈V\R,(if E i v=true then w v else 0) := by
    unfold mass; rw [sum_filter]
  unfold WeightedSD.row outW at e ⊢
  rw [leak]
  rw [← split] at e
  linarith

/-- Native prices on the dead-exit child: each failing test is a leakage bound. Write
`L i` for the native mass `i` sends outside `R` and `Q = q(c − w(V) + w(V∖R)) − c`. -/
theorem native_obstruction {q : ℕ} {D E : CH.Digraph} {V R H : Finset ℕ} {z : ℕ} (hq : 2≤q)
    (free : QFree D V q) (small : SmallerSmallRow q V.card) (sub : ∀i j,E i j=true → D i j=true)
    (inside : insert z R⊆V) (room : (insert z R).card+1<V.card) (hs : H⊆R) (live : H.Nonempty)
    (zr : z∉R) (dead : ∀v∈insert z R,E z v=false) (ball : BRsub.ballSet E (insert z R) H (q-2)=R)
    (w : ℕ→ℚ) (pos : ∀v∈V,0<w v) {c : ℚ} (flat : ∀i∈V,WeightedSD.row q E V w i=c) :
    let L : ℕ→ℚ := fun i => mass ((V\R).filter (fun v => E i v=true)) w
    let Q : ℚ := q*(c-mass V w+mass (V\R) w)-c
    q*mass H w≤mass R w ∨
      (∃b∈R,E b z=false ∧ Q≤q*((q:ℚ)-1)*L b) ∨
      (∃a∈R,E a z=true ∧ ∃b∈R,E b z=false ∧ Q≤((q:ℚ)-1)*(L a+((q:ℚ)-1)*L b)) ∨
      ∃a∈R,E a z=true ∧ ((q:ℚ)-1)^2*(q*mass H w-mass R w)≤q*((q:ℚ)-1)*L a-Q := by
  intro L Q
  have rs : R⊆V := (subset_insert _ _).trans inside
  have rows := native_rows rs flat
  have whole : mass V w=mass R w+mass (V\R) w := by
    unfold mass; rw [add_comm]; exact (sum_sdiff rs).symm
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  rcases (labelled_obstruction hq free small sub inside room hs live zr dead ball w
    (fun v vr => (pos v (rs vr)).le)).2 with heads|⟨b,br,bz,fail⟩|⟨a,ar,az,b,br,bz,fail⟩|⟨a,ar,az,fail⟩
  · exact Or.inl heads
  · right; left
    refine ⟨b,br,bz,?_⟩
    rw [rows b br] at fail
    simp only [Q,L]
    nlinarith
  · right; right; left
    refine ⟨a,ar,az,b,br,bz,?_⟩
    rw [rows a ar,rows b br] at fail
    simp only [Q,L]
    apply le_of_mul_le_mul_left _ qp
    nlinarith
  · right; right; right
    refine ⟨a,ar,az,?_⟩
    rw [rows a ar] at fail
    simp only [Q,L]
    nlinarith

/-- The exterior bank of the covered endpoint makes the native slack positive:
`Q ≥ qσ + (q−1)w(z)` with `σ = c − w(V)`. -/
theorem native_slack {q : ℕ} {D : CH.Digraph} {V U H T : Finset ℕ} (hq : 2≤q) (free : QFree D V q)
    (us : U⊆V) (hs : H⊆U) (hl : H.Nonempty) (ts : T⊆U) (size : T.card<q)
    (cover : ∀i∈BRsub.ballSet D U H (q-2),∃k∈T,D i k=true)
    {z : ℕ} (zt : z∈T\BRsub.ballSet D U H (q-2))
    (w : ℕ→ℚ) (pos : ∀x∈V,0<w x) {c : ℚ} (flat : ∀i∈V,WeightedSD.row q D V w i=c) :
    (q:ℚ)*(c-mass V w)+((q:ℚ)-1)*w z≤
      q*(c-mass V w+mass (V\BRsub.ballSet D U H (q-2)) w)-c := by
  classical
  have zv : z∈V := us (ts (mem_sdiff.mp zt).1)
  obtain ⟨_,disj,bank⟩ := CommonParentEndpointPath.exterior_bank hq free us hs hl ts size cover zt
    w pos (flat z zv)
  have inB : V.filter (fun x => ∀k∈T,D x k=false)⊆V\BRsub.ballSet D U H (q-2) := by
    intro x hx
    exact mem_sdiff.mpr ⟨(mem_filter.mp hx).1,fun xr => disjoint_left.mp disj hx xr⟩
  have cap := sum_le_sum_of_subset_of_nonneg inB (fun x hx _ => (pos x (mem_sdiff.mp hx).1).le)
  change mass _ w≤mass _ w at cap
  have qp : (0:ℚ)≤q := Nat.cast_nonneg q
  nlinarith [mul_le_mul_of_nonneg_left cap qp]

/-- Native inner rows within `q-3` of the heads leak only outside the original carrier. -/
theorem near_leak {q : ℕ} {E : CH.Digraph} {V U H : Finset ℕ} (hq : 3≤q) {r : ℕ}
    (rr : r∈BRsub.ballSet E U H (q-3)) :
    (V\BRsub.ballSet E U H (q-2)).filter (fun v => E r v=true)⊆V\U := by
  intro x hx
  obtain ⟨xd,xe⟩ := mem_filter.mp hx
  obtain ⟨xv,xr⟩ := mem_sdiff.mp xd
  refine mem_sdiff.mpr ⟨xv,fun xu => xr ?_⟩
  obtain ⟨h,hh,hit⟩ := BRsub.mem_ballSet.mp rr
  have step := ball_step hit xu xe
  rw [show q-3+1=q-2 by omega] at step
  exact BRsub.mem_ballSet.mpr ⟨h,hh,step⟩


/-! ## The replay's actual child with repaired prices -/

/-- The covered replay child (`replay_one_exterior`, `Fork`) is `insert z R`, and no exit price
pays it on the repaired prices: every `t ≥ 0` fails, at the labels of `labelled_obstruction`. -/
theorem fork_child {q : ℕ} {D : CH.Digraph} {V U H R : Finset ℕ} (hq : 2≤q)
    (free : QFree D V q) (small : SmallerSmallRow q V.card) (us : U⊆V) (room : U.card+1<V.card)
    (hl : H.Nonempty) {s : CommonParentReplay.State} (valid : CommonParentReplay.Valid q D H R U s)
    {z : ℕ} (zr : z∉R) (one : s.carrier\R={z}) (sink : outN D s.carrier z=∅) :
    s.carrier=insert z R ∧ (∀t:ℚ,0≤t → ¬Pays q D (insert z R) H (exitTilt s.weights z t)) ∧
    (q*mass H s.weights≤mass R s.weights ∨
      (∃b∈R,D b z=false ∧ ((q:ℚ)-1)*WeightedSD.row q D R s.weights b≤q*mass R s.weights) ∨
      (∃a∈R,D a z=true ∧ ∃b∈R,D b z=false ∧
        ((q:ℚ)-1)*(WeightedSD.row q D R s.weights a+((q:ℚ)-1)*WeightedSD.row q D R s.weights b)≤
          (q:ℚ)^2*mass R s.weights) ∨
      ∃a∈R,D a z=true ∧ ((q:ℚ)-1)^2*(q*mass H s.weights-mass R s.weights)≤
        q*mass R s.weights-((q:ℚ)-1)*WeightedSD.row q D R s.weights a) := by
  have same : BRsub.ballSet D s.carrier H (q-2)=R := valid.same
  have rc : R⊆s.carrier := by
    intro r rr
    rw [← same] at rr
    obtain ⟨_,_,hit⟩ := BRsub.mem_ballSet.mp rr
    exact (mem_ball.mp hit).1
  have ceq := carrier_eq rc one
  have hs : H⊆R := fun h hh => same ▸ BRsub.mem_ballSet.mpr ⟨h,hh,self_mem_ball (valid.keeps hh)⟩
  have dead : ∀v∈insert z R,D z v=false := by
    intro v vi
    apply Bool.eq_false_iff.mpr
    intro e
    have : v∈outN D s.carrier z := mem_outN.mpr ⟨ceq ▸ vi,e⟩
    simp [sink] at this
  have ball : BRsub.ballSet D (insert z R) H (q-2)=R := ceq ▸ same
  have inside : insert z R⊆V := ceq ▸ valid.inside.trans us
  have room' : (insert z R).card+1<V.card := by
    have := card_le_card valid.inside
    rw [ceq] at this
    omega
  have nonneg : ∀v∈R,0≤s.weights v := fun v vr => (valid.positive v (rc vr)).le
  exact ⟨ceq,dead_exit_closed hq free small (fun _ _ e => e) inside room' hs hl s.weights nonneg,
    (labelled_obstruction hq free small (fun _ _ e => e) inside room' hs hl zr dead ball
      s.weights nonneg).2⟩

/-! ## Native tests that always pass -/

/-- Natively the heads test passes: `q·w(H) = c − w(a)` exceeds the inner mass. -/
theorem native_heads_pass {q : ℕ} {E : CH.Digraph} {V R H : Finset ℕ} {w : ℕ→ℚ} {c : ℚ} {a : ℕ}
    (pos : ∀v∈V,0<w v) (flat : ∀i∈V,WeightedSD.row q E V w i=c) (high : mass V w<c)
    (av : a∈V) (hv : H⊆V) (heads : ∀v∈V,E a v=true ↔ v∈H) (rs : R⊆V) (aR : a∉R) :
    mass R w<q*mass H w := by
  have out : outN E V a=H := by
    ext v
    rw [mem_outN]
    exact ⟨fun ⟨vv,e⟩ => (heads v vv).mp e,fun vh => ⟨hv vh,(heads v (hv vh)).mpr vh⟩⟩
  have e := flat a av
  rw [WeightedSD.row,outW_eq_mass,out] at e
  have sub : R⊆V.erase a := fun r rr => mem_erase.mpr ⟨fun h => aR (h ▸ rr),rs rr⟩
  have cap : mass R w≤mass (V.erase a) w :=
    sum_le_sum_of_subset_of_nonneg sub (fun v vv _ => (pos v (mem_of_mem_erase vv)).le)
  have split : mass (V.erase a) w+w a=mass V w := sum_erase_add _ _ av
  linarith

/-- Natively a row within `q-3` steps of the heads that sends nothing outside the original
carrier has zero leakage; with `Q > 0` it passes the upper-bound test. -/
theorem native_near_pass {q : ℕ} {E : CH.Digraph} {V U H : Finset ℕ} {w : ℕ→ℚ} (hq : 3≤q) {r : ℕ}
    (rr : r∈BRsub.ballSet E U H (q-3)) (inU : ∀x∈V\U,E r x=false) {Q : ℚ} (Qpos : 0<Q) :
    q*((q:ℚ)-1)*mass ((V\BRsub.ballSet E U H (q-2)).filter (fun v => E r v=true)) w<Q := by
  have empty : (V\BRsub.ballSet E U H (q-2)).filter (fun v => E r v=true)=∅ := by
    apply eq_empty_of_forall_notMem
    intro x hx
    have xo := near_leak (V:=V) hq rr hx
    have := inU x xo
    simp [this] at hx
  rw [empty]
  simpa [mass] using Qpos

/-- Natively the cut exit (`t = 0`) fails at a row whose leakage is at least `(σ + w(V∖R))/q`. -/
theorem native_zero_label {q : ℕ} {D E : CH.Digraph} {V R H : Finset ℕ} {z : ℕ} (hq : 2≤q)
    (free : QFree D V q) (small : SmallerSmallRow q V.card) (sub : ∀i j,E i j=true → D i j=true)
    (inside : insert z R⊆V) (room : (insert z R).card+1<V.card) (hs : H⊆R) (live : H.Nonempty)
    (zr : z∉R) (dead : ∀v∈insert z R,E z v=false) (ball : BRsub.ballSet E (insert z R) H (q-2)=R)
    (w : ℕ→ℚ) (pos : ∀v∈V,0<w v) {c : ℚ} (flat : ∀i∈V,WeightedSD.row q E V w i=c)
    (heavy : mass R w<q*mass H w) :
    ∃i∈R,c-mass R w≤q*mass ((V\R).filter (fun v => E i v=true)) w := by
  have rs : R⊆V := (subset_insert _ _).trans inside
  rcases (labelled_obstruction hq free small sub inside room hs live zr dead ball w
    (fun v vr => (pos v (rs vr)).le)).1 with h|⟨i,ir,low⟩
  · exact absurd heavy (not_lt.mpr h)
  · exact ⟨i,ir,by rw [native_rows rs flat i ir] at low; linarith⟩

#print axioms pays_pos_iff
#print axioms pays_zero_iff
#print axioms exit_price_iff
#print axioms exit_exists_iff
#print axioms labelled_obstruction
#print axioms exit_entered
#print axioms native_obstruction
#print axioms native_slack
#print axioms near_leak
#print axioms fork_child
#print axioms native_heads_pass
#print axioms native_near_pass
#print axioms native_zero_label
end LeanCH.BR.Closure.DeadExit
