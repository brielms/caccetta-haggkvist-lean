import checkpoints.shen_extension.OpposedPairPrices
import LeanCH.BR.BRWeightedArcInverse
import Mathlib.Combinatorics.Hall.Finite
import LeanCH.BR.BRFiniteThresholdUnit

namespace LeanCH.BR.Closure.CanonicalCycleLaw
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShenCycleSuccessor
open FullCycleTransfer OpposedPairPrices
open scoped Matrix

/-- Constant excess on the deleted columns and zero excess elsewhere. -/
private def level (V D : Finset ℕ) (t : ℝ) (z : ↥V) : ℝ := if (z : ℕ) ∈ D then t else 0

/-- The inverse converts the prescribed column excess into a law on actual rows. -/
noncomputable def law {V : Finset ℕ} (K : Matrix V V ℝ) (D : Finset ℕ) (t : ℝ) : ℕ → ℝ :=
  realExtendWeight V (level V D t ᵥ* K)

private theorem level_mass {V D : Finset ℕ} {x : ℕ → ℝ} {gap : ℝ} {K : Matrix V V ℝ}
    (dv : D ⊆ V) (positive : 0 < realMass D x)
    (rows : ∀ z : ↥V, x z = gap * ∑ b, K z b) :
    (∑ b, (level V D (gap / realMass D x) ᵥ* K) b) = 1 := by
  classical
  let total := realMass D x
  have reduce (z : ↥V) : level V D (gap/total) z * (∑ b, K z b) =
      if (z : ℕ) ∈ D then x z / total else 0 := by
    by_cases h : (z : ℕ) ∈ D
    · simp only [level,ite_eq_left h,rows z]
      ring
    · simp [level,h]
  have filt : V.filter (· ∈ D) = D := by ext z; simp only [mem_filter]; exact and_iff_right_of_imp (fun h => dv h)
  calc
    _ = ∑ z : ↥V, ∑ b : ↥V, level V D (gap/total) z * K z b := sum_comm
    _ = ∑ z : ↥V, if (z : ℕ) ∈ D then x z / total else 0 :=
      sum_congr rfl fun z _ => (mul_sum ..).symm.trans (reduce z)
    _ = 1 := by
      rw [sum_coe_sort V (fun z => if z ∈ D then x z / total else 0),←sum_filter,filt,←sum_div]
      exact div_self positive.ne'

/-- The law is nonnegative and normalized. Its ambient column prices are
exactly one off D and one plus the specified excess on D. -/
theorem two_levels {q E} {V D : Finset ℕ} {K : Matrix V V ℝ} (hK : CommonInverse (realMatrix q E V) K)
    {x : ℕ → ℝ} {gap : ℝ} (dv : D ⊆ V) (positive : 0 < realMass D x) (high : 0 < gap)
    (rows : ∀ z : ↥V, x z = gap * ∑ b, K z b) :
    let t := gap / realMass D x
    let l := law K D t
    (∀ b ∈ V, 0 ≤ l b) ∧ realMass V l = 1 ∧
      ∀ z ∈ V, price q E V l z = 1 + (if z ∈ D then t else 0) := by
  classical
  intro t l
  have norm := level_mass dv positive rows
  refine ⟨?_,(realMass_extendWeight V _).trans norm,?_⟩
  · intro b bv
    change 0 ≤ realExtendWeight V _ (⟨b,bv⟩ : ↥V)
    rw [realExtendWeight_on]
    apply sum_nonneg
    intro z _
    exact mul_nonneg (by dsimp [level,t]; split_ifs <;> positivity) (hK.nonneg z _)
  · intro z zv
    let i : ↥V := ⟨z,zv⟩
    have e := residual_columns hK (level V D t) norm i
    have col := realCol_extendWeight q E V (level V D t ᵥ* K) i
    change realCol q E V l z = ((level V D t ᵥ* K) ᵥ* realMatrix q E V) i at col
    change (if z ∈ V then l z else 0) + q*realInW E V l z = _
    rw [ite_eq_left zv]
    exact col.trans e

/-- The inverse column link is exactly the support of the canonical law. -/
theorem support_iff {q E} {V D : Finset ℕ} {K : Matrix V V ℝ} (hK : CommonInverse (realMatrix q E V) K)
    {t : ℝ} (ht : 0 < t) (b : ↥V) :
    0 < law K D t b ↔ ∃ y : ↥V, (y : ℕ) ∈ D ∧ 0 < K y b := by
  classical
  rw [law,realExtendWeight_on]
  change 0 < ∑ y : ↥V, level V D t y * K y b ↔ _
  have nonneg (y : ↥V) : 0 ≤ level V D t y * K y b :=
    mul_nonneg (by dsimp [level]; split_ifs <;> positivity) (hK.nonneg y b)
  constructor
  · intro high
    by_contra! none
    have vanish (y : ↥V) (_ : y ∈ univ) : level V D t y * K y b = 0 := by
      by_cases yd : (y : ℕ) ∈ D
      · simp [level,yd,le_antisymm (none y yd) (hK.nonneg y b)]
      · simp [level,yd]
    rw [sum_eq_zero vanish] at high
    exact high.false
  · rintro ⟨y,yd,link⟩
    exact (show 0 < level V D t y * K y b by simpa [level,yd] using mul_pos ht link).trans_le
      (single_le_sum (fun z _ => nonneg z) (mem_univ y))

/-- Total debit of a column-price function under the actual full pairing. -/
noncomputable def debit {E A M} (P : Pairing E A M) (x h : ℕ → ℝ) : ℝ :=
  ∑ y ∈ A \ M, x y * (h y - h (P.label y))

theorem debit_sub {E A M} (P : Pairing E A M) (x h k : ℕ → ℝ) :
    debit P x (fun z => h z-k z) = debit P x h - debit P x k := by
  unfold debit
  rw [←sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- For any legal completion the canonical price accounts for exactly one gap. -/
theorem canonical_debit {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M)
    (P : Pairing E A M) {x l : ℕ → ℝ} {gap : ℝ} (positive : 0 < realMass (A \ M) x)
    (prices : ∀ z ∈ V, price q E V l z = 1 + (if z ∈ A \ M then gap/realMass (A \ M) x else 0)) :
    debit P x (price q E V l) = gap := by
  classical
  let D := A \ M
  have entry (y) (yd : y ∈ D) : price q E V l y - price q E V l (P.label y) =
      gap / realMass D x := by
    have rm := (mem_sdiff.mp (P.destination yd)).1
    have outside : P.label y ∉ A \ M := fun h => (mem_sdiff.mp h).2 rm
    rw [prices y (a.sub (mem_sdiff.mp yd).1), prices _ (m.sub rm),ite_eq_left yd,ite_eq_right outside]
    ring
  unfold debit
  rw [sum_congr rfl (fun y hy => congrArg (x y * ·) (entry y hy)),←sum_mul]
  change realMass D x * (gap/realMass D x) = gap
  rw [mul_comm,div_mul_cancel₀ _ (show realMass D x ≠ 0 from positive.ne')]

private theorem price_diff {V T : Finset ℕ} (tv : T ⊆ V) (q : ℕ) (E : CH.Digraph)
    (p l : ℕ → ℝ) {z} (zv : z ∈ V) :
    price q E V (fun b => maskReal T p b - l b) z =
      price q E T p z - price q E V l z := by
  have diff : realInW E V (fun b => maskReal T p b - l b) z =
      realInW E V (maskReal T p) z - realInW E V l z := by
    unfold realInW
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro b _
    by_cases edge : E b z=true <;> simp [edge]
  unfold price
  rw [ite_eq_left zv,ite_eq_left zv,diff,maskReal_inW tv]
  unfold maskReal
  ring

/-- Subtracting the canonical probability law leaves a zero-mass signed
correction. Every discarded-cycle coordinate has prescribed correction and
the signed debit is exactly the original exterior debit minus its gap. -/
theorem correction {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M)
    {x l p : ℕ → ℝ} {gap : ℝ} (lx : realMass V l = 1) (pm : realMass (V \ A) p = 1)
    (positive : 0 < realMass (A \ M) x)
    (prices : ∀ z ∈ V, price q E V l z = 1 + (if z ∈ A \ M then gap/realMass (A \ M) x else 0)) :
    let eta := fun b => maskReal (V \ A) p b - l b
    realMass V eta = 0 ∧ (∀ b ∈ A, eta b = -l b) ∧ ∀ P : Pairing E A M,
      debit P x (price q E V eta) = debit P x (price q E (V \ A) p) - gap := by
  classical
  intro eta
  refine ⟨?_,?_,?_⟩
  · change (∑ v ∈ V, (maskReal (V \ A) p v - l v)) = 0
    rw [sum_sub_distrib]
    change realMass V (maskReal (V \ A) p) - realMass V l = 0
    rw [maskReal_mass sdiff_subset,pm,lx,sub_self]
  · intro b ba
    have out : b ∉ V \ A := fun h => (mem_sdiff.mp h).2 ba
    simp only [eta,maskReal,ite_eq_right out,zero_sub]
  · intro P
    have same : debit P x (price q E V eta) =
        debit P x (fun z => price q E (V \ A) p z - price q E V l z) := by
      apply sum_congr rfl
      intro y hy
      rw [price_diff sdiff_subset q E p l (a.sub (mem_sdiff.mp hy).1),
        price_diff sdiff_subset q E p l (m.sub (mem_sdiff.mp (P.destination hy)).1)]
    rw [same,debit_sub,canonical_debit a m P positive prices]

/-- An actual child-dual certificate selects a failed row of positive
certificate weight even when some of its coordinates vanish. -/
private theorem supported_light {q E U w p} (hp : RealDual q E U 1 p)
    (wn : ∀ v ∈ U, 0 ≤ w v) :
    ∃ b ∈ U, 0 < p b ∧ realRow q E U w b ≤ realMass U w := by
  classical
  have upper := sum_le_sum (s:=U) (fun v hv =>
    mul_le_mul_of_nonneg_left (hp.columns v hv) (wn v hv))
  simp only [mul_one] at upper
  change (∑ v ∈ U,w v*realCol q E U p v) ≤ realMass U w at upper
  rw [←real_cross_rows] at upper
  have somePos : ∃ b ∈ U, 0 < p b := by
    by_contra! none
    have hz : realMass U p = 0 := sum_eq_zero fun b hb => le_antisymm (none b hb) (hp.nonneg b hb)
    linarith only [hz,hp.normalized]
  obtain ⟨j,ju,jpos⟩ := somePos
  by_contra! none
  have le (b) (bu : b ∈ U) : p b*realMass U w ≤ p b*realRow q E U w b := by
    rcases (hp.nonneg b bu).eq_or_lt with eq|pos
    · simp [←eq]
    · exact mul_le_mul_of_nonneg_left (none b bu pos).le pos.le
  have strict := sum_lt_sum le ⟨j,ju,mul_lt_mul_of_pos_left (none j ju jpos) jpos⟩
  rw [←sum_mul] at strict
  change realMass U p*realMass U w < _ at strict
  rw [hp.normalized,one_mul] at strict
  exact strict.not_ge upper

/-- For every matching a full-step failure can be selected inside the
canonical support outside A. The inverse link and the lost arc have the same
actual failed row; their donor labels v and y are separately witnessed. -/
theorem supported_failure {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M)
    {K : Matrix V V ℝ} (hK : CommonInverse (realMatrix q E V) K)
    {x lambda : ℕ → ℝ} {t : ℝ} (ht : 0 < t) (pos : ∀ z ∈ V, 0 ≤ x z)
    (strict : ∀ z ∈ V, realMass V x < realRow q E V x z)
    (childDual : RealDual q E (V \ (A \ M)) 1 lambda) (P : Pairing E A M) :
    let D := A \ M
    let U := V \ D
    let w := fun z => x z + P.deposit x z
    ∃ b : ↥V, (b : ℕ) ∈ V \ A ∧ 0 < lambda b ∧ 0 < law K D t b ∧
      realRow q E U w b ≤ realMass U w ∧
      (∃ v : ↥V, (v : ℕ) ∈ D ∧ 1 < price q E U lambda v ∧ 0 < K v b) ∧
      ∃ y ∈ D, E b y = true ∧ E b (P.label y) = false := by
  classical
  intro D U w
  have uv : U ⊆ V := sdiff_subset
  have dep (b) : 0 ≤ P.deposit x b := by
    apply sum_nonneg
    intro y hy
    split_ifs
    · exact pos y (a.sub (mem_sdiff.mp hy).1)
    · exact le_rfl
  obtain ⟨b,bu,pb,low⟩ := supported_light childDual (w:=w) (fun v vu => add_nonneg (pos v (uv vu)) (dep v))
  let B : ↥V := ⟨b,uv bu⟩
  have old := strict b (uv bu)
  have mass : realMass U w = realMass V x := P.mass_balance a m x
  have missed : ∃ y ∈ D, E b y = true ∧ E b (P.label y) = false := by
    by_contra! none
    have cov := P.covered_heads a m x (fun y hy => pos y (a.sub (mem_sdiff.mp hy).1)) b
      (fun y hy hit => Bool.eq_true_of_not_eq_false (none y hy hit))
    have keep : realRow q E V x b ≤ realRow q E U w b :=
      add_le_add (le_add_of_nonneg_right (dep b)) (mul_le_mul_of_nonneg_left cov (Nat.cast_nonneg q))
    exact old.not_ge (keep.trans (low.trans mass.le))
  obtain ⟨y,yd,hit,miss⟩ := missed
  have outside : b ∉ A := by
    intro ba
    have bm : b ∈ M := by_contra fun h => (mem_sdiff.mp bu).2 (mem_sdiff.mpr ⟨ba,h⟩)
    have ya := (mem_sdiff.mp yd).1
    have yes := P.successor b (mem_inter.mpr ⟨ba,bm⟩) ⟨y,ya⟩ hit
    rw [P.label_apply ya,yes] at miss
    contradiction
  have cert := cutCertificate_of_realDual uv childDual
  have member : b ∈ U := bu
  have marked : 0 < maskReal U lambda B := by simpa only [maskReal,B,ite_eq_left member] using pb
  obtain ⟨v,omitted,overload,link⟩ := positive_source hK cert marked
  have vu : (v : ℕ) ∉ U := by simpa [hostCut] using omitted
  have vd : (v : ℕ) ∈ D := by_contra fun h => vu (mem_sdiff.mpr ⟨v.property,h⟩)
  have priceId : price q E U lambda v =
      ((fun i : ↥V => maskReal U lambda i) ᵥ* realMatrix q E V) v := by
    rw [realMatrix_col,realCol,maskReal_inW uv]
    rfl
  exact ⟨B,mem_sdiff.mpr ⟨uv bu,outside⟩,pb,(support_iff hK ht B).mpr ⟨v,vd,link⟩,low,
    ⟨v,vd,priceId ▸ overload,link⟩,y,yd,hit,miss⟩

theorem unit_columns {q E U p} (hq : 2 ≤ q)
    (tight : ∀ z ∈ U, realCol q E U p z = 1) :
    (realMass U p = 1 → (U.card : ZMod q) = 1) ∧ ∀ z ∈ U, p z ≠ 0 := by
  classical
  let J : Matrix (↥U) (↥U) ℤ := fun i j => if E j i = true then 1 else 0
  let v := fun i : ↥U => p i
  have formula (i : ↥U) : v i+(q : ℝ)*(∑ j : ↥U, (J i j : ℝ)*v j) = 1 := by
    have inner : (∑ j : ↥U,(J i j : ℝ)*v j) = realInW E U p i := by
      rw [realInW,←sum_coe_sort U (fun j => if E j i = true then p j else 0)]
      apply sum_congr rfl
      intro j _
      by_cases ed : E j i = true <;> simp [ed,J,v]
    rw [inner]
    exact tight i i.property
  have mat : ((Rat.castHom ℝ).mapMatrix (WeightedArithmetic.rationalMatrix q J)) *ᵥ v = fun _ => 1 := by
    funext i
    simpa [WeightedArithmetic.rationalMatrix,WeightedArithmetic.closedMatrix,Matrix.mulVec,dotProduct,
      sum_add_distrib,mul_sum,add_mul,mul_assoc,ite_mul,apply_ite] using formula i
  refine ⟨fun norm => ?_,?_⟩
  · have hm := (sum_coe_sort U p).trans norm
    simpa only [Fintype.card_coe] using InverseDiagonal.real_unit_card_mod hq J v hm formula
  intro z zu
  exact real_unit_coordinates_ne_zero hq J v mat ⟨z,zu⟩

/-- The actual smaller-host law and its mass before conditioning on the
exterior. The witness is independent of the subsequent choice of matching. -/
def FromChild (q : ℕ) (E : CH.Digraph) (V A M : Finset ℕ) (mu : ℕ→ℝ) : Prop :=
  ∃ raw : ℕ→ℝ, RealDual q E (V\(A\M)) 1 raw ∧ 0<realMass (V\A) raw ∧
    mu=fun b => raw b/realMass (V\A) raw

/-- One exterior law, chosen before the matching, supplies a uniform floor for
the signed debit after subtracting the full canonical gap. The floor is
strictly positive if the cycles overlap or the smaller order is not 1 mod q. -/
theorem exterior_with_child {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M)
    {K : Matrix V V ℝ} (hK : CommonInverse (realMatrix q E V) K)
    {x : ℕ → ℝ} {c : ℝ} (hq : 2 ≤ q) (pos : ∀ z ∈ V, 0 < x z)
    (unit : realMass V x = 1) (high : 1 < c) (equalized : ∀ z ∈ V, realRow q E V x z = c)
    (positive : 0 < realMass (A \ M) x) (massK : ∀ z : ↥V, x z = (c-1)*∑ b,K z b)
    (small : SmallRow q E (V \ (A \ M))) :
    let D := A \ M
    let T := V \ A
    let l := law K D ((c-1)/realMass D x)
    ∃ (mu : ℕ → ℝ) (margin : ℝ), FromChild q E V A M mu ∧ 0 ≤ margin ∧
      ((A ∩ M).Nonempty ∨ ((V \ D).card : ZMod q) ≠ 1 → 0 < margin) ∧
      (∀ b ∈ T, 0 ≤ mu b) ∧ realMass T mu = 1 ∧
      (∀ b ∈ T, 0 < mu b → 0 < l b) ∧
      let eta := fun b => maskReal T mu b - l b
      realMass V eta = 0 ∧ (∀ b ∈ A, eta b = -l b) ∧ ∀ P : Pairing E A M,
        margin ≤ debit P x (price q E V eta) ∧
        debit P x (price q E T mu) = (c-1) + debit P x (price q E V eta) := by
  classical
  intro D T l
  let U := V \ D
  have uv : U ⊆ V := sdiff_subset
  have tu : T ⊆ U := fun b bt => mem_sdiff.mpr ⟨(mem_sdiff.mp bt).1,
    fun bd => (mem_sdiff.mp bt).2 (mem_sdiff.mp bd).1⟩
  have gap : 0 < c-1 := sub_pos.mpr high
  obtain ⟨_,ln,prices⟩ := two_levels hK (sdiff_subset.trans a.sub) positive gap massK
  obtain ⟨p,hp,bill⟩ := PairingPressure.uniform a m small (fun z zv => (pos z zv).le)
    (fun z zv => (equalized z zv).ge)
  let d := realMass T p
  have pn (b) (bt : b ∈ T) : 0 ≤ p b := hp.nonneg b (tu bt)
  have cap : d ≤ 1 := hp.normalized ▸ sum_le_sum_of_subset_of_nonneg tu
    (fun b bu _ => hp.nonneg b bu)
  have dp : 0 < d := by
    by_contra! zero
    have vanish (b) (bt : b ∈ T) : p b = 0 :=
      le_antisymm ((single_le_sum pn bt).trans zero) (pn b bt)
    obtain ⟨P⟩ := exists_pairing a m
    have bound := bill P
    change c-realMass V x ≤ ∑ b ∈ T,p b*(c-realRow q E U (fun z => x z+P.deposit x z) b) at bound
    rw [unit, sum_congr rfl (fun b (bt : b ∈ T) =>
      show p b*(c-realRow q E U (fun z => x z+P.deposit x z) b) = 0 by rw [vanish b bt,zero_mul]),
      sum_const_zero] at bound
    exact gap.not_ge bound
  let mu (b : ℕ) := p b / d
  have norm : realMass T mu = 1 := by
    change (∑ b ∈ T,p b/d) = 1
    rw [←sum_div]
    exact div_self dp.ne'
  have corr := correction a m (l:=l) ln norm positive prices
  let eps := internalDefect q E U x p
  have epsTerm (z) (zu : z ∈ U) : 0 ≤ x z*(1-realCol q E U p z) :=
    mul_nonneg (pos z (uv zu)).le (sub_nonneg.mpr (hp.columns z zu))
  have eps0 : 0 ≤ eps := sum_nonneg epsTerm
  let margin := eps + (1-d)*(c-1)
  have margin0 : 0 ≤ margin := add_nonneg eps0 (mul_nonneg (sub_nonneg.mpr cap) gap.le)
  have parts := sum_sdiff tu (f:=p)
  change (∑ b ∈ U \ T,p b)+d = realMass U p at parts
  rw [hp.normalized] at parts
  refine ⟨mu,margin,⟨p,hp,dp,rfl⟩,margin0,?_,fun b bt => div_nonneg (pn b bt) dp.le,norm,?_,corr.1,corr.2.1,?_⟩
  · intro condition
    by_contra! notpos
    change eps+(1-d)*(c-1) ≤ 0 at notpos
    have zero : eps = 0 := by linarith only [eps0,notpos,mul_nonneg (sub_nonneg.mpr cap) gap.le]
    have full : d = 1 := by
      by_contra ne
      have term := mul_pos (sub_pos.mpr (lt_of_le_of_ne cap ne)) gap
      linarith
    have tight (z) (zu : z ∈ U) : realCol q E U p z = 1 := by
      have t := single_le_sum epsTerm zu
      change x z*(1-realCol q E U p z) ≤ eps at t
      exact le_antisymm (hp.columns z zu) (by
        by_contra! bad
        have := mul_pos (pos z (uv zu)) (sub_pos.mpr bad)
        linarith)
    obtain ⟨residue,nonzero⟩ := unit_columns hq tight
    have modulo := residue hp.normalized
    have allpos (s) (su : s ∈ U) := lt_of_le_of_ne (hp.nonneg s su) (Ne.symm (nonzero s su))
    rcases condition with ⟨s,shared⟩|modNe
    · have ⟨sa,sm⟩ := mem_inter.mp shared
      have su : s ∈ U := mem_sdiff.mpr ⟨m.sub sm,fun del => (mem_sdiff.mp del).2 sm⟩
      have st : s ∈ U \ T := mem_sdiff.mpr ⟨su,fun out => (mem_sdiff.mp out).2 sa⟩
      have bound := single_le_sum (fun b (hb : b ∈ U \ T) => hp.nonneg b (mem_sdiff.mp hb).1) st
      linarith only [bound,full,parts,allpos s su]
    · exact modNe modulo
  · intro b bt weight
    have bu : b ∈ U := tu bt
    let B : ↥V := ⟨b,uv bu⟩
    have pb : 0 < p b := (div_pos_iff_of_pos_right dp).mp weight
    have cert := cutCertificate_of_realDual uv hp
    have supply : 0 < maskReal U p B := by simpa only [maskReal,B,ite_eq_left bu] using pb
    obtain ⟨v,omitted,_,link⟩ := positive_source hK cert supply
    have vu : (v : ℕ) ∉ U := by simpa [hostCut] using omitted
    have vd : (v : ℕ) ∈ D := by_contra fun no => vu (mem_sdiff.mpr ⟨v.property,no⟩)
    exact (support_iff hK (div_pos gap positive) B).mpr ⟨v,vd,link⟩
  · intro P
    let w := fun v => x v+P.deposit x v
    let R := fun b => realRow q E U w b
    have dep (z) : 0 ≤ P.deposit x z := by
      apply sum_nonneg
      intro y hy
      split_ifs
      · exact (pos y (a.sub (mem_sdiff.mp hy).1)).le
      · exact le_rfl
    have reserve : eps ≤ internalDefect q E U w p :=
      sum_le_sum (fun z zu => mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (dep z))
        (sub_nonneg.mpr (hp.columns z zu)))
    rw [internalDefect_eq,←real_cross_rows] at reserve
    have massW : realMass U w = 1 := (P.mass_balance a m x).trans unit
    rw [massW] at reserve
    have sharedBound (b) (hb : b ∈ U \ T) : c ≤ R b := by
      have bu := (mem_sdiff.mp hb).1
      have ba : b ∈ A := by_contra fun out => (mem_sdiff.mp hb).2 (mem_sdiff.mpr ⟨uv bu,out⟩)
      have bm : b ∈ M := by_contra fun out => (mem_sdiff.mp bu).2 (mem_sdiff.mpr ⟨ba,out⟩)
      have cov := P.covered_heads a m x (fun y hy => (pos y (a.sub (mem_sdiff.mp hy).1)).le) b (by
        intro y hy ed
        rw [P.label_apply (mem_sdiff.mp hy).1]
        exact P.successor b (mem_inter.mpr ⟨ba,bm⟩) _ ed)
      rw [←equalized b (uv bu)]
      exact add_le_add (le_add_of_nonneg_right (dep b)) (mul_le_mul_of_nonneg_left cov (Nat.cast_nonneg q))
    have paid := sum_le_sum (fun b hb => mul_le_mul_of_nonneg_left (sharedBound b hb)
      (hp.nonneg b (mem_sdiff.mp hb).1))
    rw [←sum_mul] at paid
    have split := sum_sdiff tu (f:=fun b => p b*R b)
    have scale : (∑ b ∈ T,mu b*R b)*d = ∑ b ∈ T,p b*R b := by
      simp only [mu,div_mul_eq_mul_div,←sum_div,div_mul_cancel₀ _ dp.ne']
    have old : (∑ b ∈ T,mu b*realRow q E V x b) = c := by
      calc
        _ = ∑ b ∈ T,mu b*c := sum_congr rfl fun b bt => by rw [equalized b (uv (tu bt))]
        _ = c := by rw [←sum_mul,show (∑ b ∈ T,mu b) = 1 from norm,one_mul]
    have priceBill := OpposedPairPrices.bill a m P x mu
    change (∑ b ∈ T,mu b*realRow q E V x b)-(∑ b ∈ T,mu b*R b) =
      debit P x (price q E T mu) at priceBill
    rw [old] at priceBill
    have eqn := corr.2.2 P
    have base : margin ≤ d*(1-∑ b ∈ T,mu b*R b) := by
      dsimp only [margin]
      change eps ≤ 1-∑ b ∈ U,p b*R b at reserve
      nlinarith only [reserve,paid,split,scale,congrArg (· * c) parts]
    have nonnegLoss : 0 ≤ 1-∑ b ∈ T,mu b*R b :=
      nonneg_of_mul_nonneg_right (margin0.trans base) dp
    have lower := base.trans (mul_le_of_le_one_left nonnegLoss cap)
    exact ⟨by linarith only [eqn,lower,priceBill],by linarith only [eqn]⟩

theorem exterior_correction {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M)
    {K : Matrix V V ℝ} (hK : CommonInverse (realMatrix q E V) K)
    {x : ℕ → ℝ} {c : ℝ} (hq : 2 ≤ q) (pos : ∀ z ∈ V, 0 < x z)
    (unit : realMass V x = 1) (high : 1 < c) (equalized : ∀ z ∈ V, realRow q E V x z = c)
    (positive : 0 < realMass (A \ M) x) (massK : ∀ z : ↥V, x z = (c-1)*∑ b,K z b)
    (small : SmallRow q E (V \ (A \ M))) :
    let D := A \ M
    let T := V \ A
    let l := law K D ((c-1)/realMass D x)
    ∃ (mu : ℕ → ℝ) (margin : ℝ), 0 ≤ margin ∧
      ((A ∩ M).Nonempty ∨ ((V \ D).card : ZMod q) ≠ 1 → 0 < margin) ∧
      (∀ b ∈ T, 0 ≤ mu b) ∧ realMass T mu = 1 ∧
      (∀ b ∈ T, 0 < mu b → 0 < l b) ∧
      let eta := fun b => maskReal T mu b - l b
      realMass V eta = 0 ∧ (∀ b ∈ A, eta b = -l b) ∧ ∀ P : Pairing E A M,
        margin ≤ debit P x (price q E V eta) ∧
        debit P x (price q E T mu) = (c-1) + debit P x (price q E V eta) := by
  obtain ⟨mu,m,_,rest⟩ := exterior_with_child a m hK hq pos unit high equalized positive massK small
  exact ⟨mu,m,rest⟩

/-- Actual possible recipients of a deleted label. An edge must pay its
shared predecessor and every exterior parent in the inverse support of D. -/
noncomputable def recipients {V : Finset ℕ} (E : CH.Digraph) (K : Matrix V V ℝ)
    (A M : Finset ℕ) (y : ↥(A \ M)) : Finset ↥(M \ A) := by
  classical
  exact univ.filter fun r =>
    (∀ u ∈ A ∩ M, E u y = true → E u r = true) ∧
      ∀ b : ↥V, (b : ℕ) ∉ A → (∃ v : ↥V, (v : ℕ) ∈ A \ M ∧ 0 < K v b) →
        E b y = true → E b r = true

private theorem complete_choice {E V q A M} (a : Cycle E V q A) (m : Cycle E V q M)
    (f : ↥(A \ M) → ↥(M \ A)) (inj : Function.Injective f)
    (heads : ∀ d : ↥(A \ M), ∀ u ∈ A ∩ M, E u d = true → E u (f d) = true) :
    ∃ P : Pairing E A M, ∀ d : ↥(A \ M), P.label d = (f d : ℕ) := by
  classical
  let go (y : ↥A) : ↥M := if ym : (y : ℕ) ∈ M then ⟨y,ym⟩ else
    let d : ↥(A \ M) := ⟨y,mem_sdiff.mpr ⟨y.property,ym⟩⟩
    ⟨f d,(mem_sdiff.mp (f d).property).1⟩
  have fix (y : ↥A) (ym : (y : ℕ) ∈ M) : (go y : ℕ) = y := by simp [go,ym]
  have send (y : ↥A) (ym : (y : ℕ) ∉ M) :
      (go y : ℕ) = (f ⟨y,mem_sdiff.mpr ⟨y.property,ym⟩⟩ : ℕ) := by simp [go,ym]
  have out (y : ↥A) (ym : (y : ℕ) ∉ M) : (go y : ℕ) ∉ A :=
    send y ym ▸ (mem_sdiff.mp (f ⟨y,mem_sdiff.mpr ⟨y.property,ym⟩⟩).property).2
  have inject : Function.Injective go := by
    intro u v eq
    have same := congrArg Subtype.val eq
    by_cases um : (u : ℕ) ∈ M
    · by_cases vm : (v : ℕ) ∈ M
      · exact Subtype.ext ((fix u um).symm.trans (same.trans (fix v vm)))
      · exact (out v vm ((same.symm.trans (fix u um)) ▸ u.property)).elim
    · by_cases vm : (v : ℕ) ∈ M
      · exact (out u um ((same.trans (fix v vm)) ▸ v.property)).elim
      · have s := (send u um).symm.trans (same.trans (send v vm))
        exact Subtype.ext (congrArg (fun z : ↥(A \ M) => (z : ℕ)) (inj (Subtype.ext s)))
  let e := Equiv.ofBijective go ((Fintype.bijective_iff_injective_and_card go).mpr
    ⟨inject,by simp only [Fintype.card_coe,a.size,m.size]⟩)
  let P : Pairing E A M := ⟨e,fix,by
    intro u shared y arc
    by_cases ym : (y : ℕ) ∈ M
    · simpa only [show (e y : ℕ) = y from fix y ym] using arc
    · change E u (go y) = true
      rw [send y ym]
      exact heads _ u shared arc⟩
  refine ⟨P,?_⟩
  intro d
  rw [P.label_apply (mem_sdiff.mp d.property).1]
  exact send _ (mem_sdiff.mp d.property).2

/-- Hall fails on the deleted labels themselves, even though coverage is
tested only on exterior parents positively linked by the inverse to a donor.
The neighbour deficit is independent of the matching and the choice of dual. -/
theorem hall_deficit {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M)
    {K : Matrix V V ℝ} (hK : CommonInverse (realMatrix q E V) K)
    {x : ℕ → ℝ} (pos : ∀ z ∈ V, 0 ≤ x z) (strict : ∀ z ∈ V, realMass V x < realRow q E V x z)
    (small : SmallRow q E (V \ (A \ M))) :
    ∃ S : Finset ↥(A \ M), (S.biUnion (recipients E K A M)).card < S.card := by
  classical
  by_contra! hall
  obtain ⟨f,inject,allowed⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' (recipients E K A M)).mp hall
  obtain ⟨P,mapped⟩ := complete_choice a m f inject (fun y => (mem_filter.mp (allowed y)).2.1)
  obtain ⟨z,zm⟩ := card_pos.mp (show 0 < M.card by rw [m.size]; omega)
  obtain ⟨p,hp⟩ := realDual_of_smallRow small
    ⟨z,mem_sdiff.mpr ⟨m.sub zm,fun zd => (mem_sdiff.mp zd).2 zm⟩⟩
  obtain ⟨b,ba,_,_,_,⟨v,vd,_,link⟩,y,yd,hit,miss⟩ :=
    supported_failure a m hK (t:=1) zero_lt_one pos strict hp P
  let d : ↥(A \ M) := ⟨y,yd⟩
  have yes := (mem_filter.mp (allowed d)).2.2 b (mem_sdiff.mp ba).2 ⟨v,vd,link⟩ hit
  have pair : P.label y = (f d : ℕ) := mapped d
  rw [pair,yes] at miss
  contradiction

/-- On the chosen global source one inverse supplies all deleted sets
before cycles, exterior laws or matchings are chosen. -/
theorem on_source {q E V} (free : QFree E V q) (small : SmallerSmallRow q V.card)
    {x : ℕ → ℚ} {c : ℚ} (pos : ∀ z ∈ V, 0 < x z) (unit : mass V x = 1)
    (high : 1 < c) (equalized : ∀ z ∈ V, WeightedSD.row q E V x z = c) :
    let w := fun z => (x z : ℝ)
    let gap := (c : ℝ)-1
    ∃ K : Matrix V V ℝ, CommonInverse (realMatrix q E V) K ∧
      ∀ D ⊆ V, D.Nonempty →
        let t := gap / realMass D w
        let l := law K D t
        (∀ b ∈ V, 0 ≤ l b) ∧ realMass V l = 1 ∧
          ∀ z ∈ V, price q E V l z = 1 + (if z ∈ D then t else 0) := by
  classical
  intro w gap
  obtain ⟨K,hK⟩ := strict_inverse_of_proper_smallRow (small.induced free) x
    (fun z zv => (pos z zv).le) (fun z zv => by rw [unit,equalized z zv]; exact high)
  refine ⟨K,hK,?_⟩
  intro D dv live
  have positive : 0 < realMass D w := sum_pos (fun z zd => by
    change (0 : ℝ) < (x z : ℝ)
    exact_mod_cast pos z (dv zd)) live
  have hgap : 0 < gap := sub_pos.mpr (by exact_mod_cast high)
  exact two_levels hK dv positive hgap (inverse_row_sum_of_equalizer hK x unit c equalized)

/-- A probability law omitting a surviving row cannot have constant prices
on the survivor set. Thus no rescaling of a two-level canonical price can
absorb the whole support correction on an overlapping cycle pair. -/
theorem survivor_oscillation {q : ℕ} (hq : 2 ≤ q) (E : CH.Digraph) {T U : Finset ℕ}
    (tu : T ⊆ U) (missing : (U \ T).Nonempty) {mu : ℕ → ℝ}
    (nonneg : ∀ b ∈ T, 0 ≤ mu b) (norm : realMass T mu = 1) :
    ∃ i ∈ U, ∃ j ∈ U, price q E T mu i < price q E T mu j := by
  classical
  obtain ⟨s,sh⟩ := missing
  have su := (mem_sdiff.mp sh).1
  have st := (mem_sdiff.mp sh).2
  by_contra! none
  let k := price q E T mu s
  have flat (z) (zu : z ∈ U) : price q E T mu z = k :=
    le_antisymm (none s su z zu) (none z zu s su)
  have live : ∃ b ∈ T, 0 < mu b := by
    by_contra! zero
    have h : realMass T mu = 0 := sum_eq_zero fun b bt => le_antisymm (zero b bt) (nonneg b bt)
    linarith only [norm,h]
  obtain ⟨b,bt,bp⟩ := live
  have kp : 0 < k := by
    rw [← flat b (tu bt),price,ite_eq_left bt]
    apply bp.trans_le (le_add_of_nonneg_right ?_)
    apply mul_nonneg (Nat.cast_nonneg q) (sum_nonneg ?_)
    intro i hi
    split_ifs
    · exact nonneg i hi
    · exact le_rfl
  let v := fun z => maskReal T mu z / k
  have tight (z) (zu : z ∈ U) : realCol q E U v z = 1 := by
    have ins : realInW E U v z = realInW E T mu z / k := by
      rw [←maskReal_inW tu]
      unfold realInW
      rw [sum_div]
      apply sum_congr rfl
      intro j _
      by_cases edge : E j z = true <;> simp [v,edge]
    rw [realCol,ins]
    change maskReal T mu z/k+(q : ℝ)*(realInW E T mu z/k) = 1
    rw [←mul_div_assoc,←add_div]
    change price q E T mu z / k = 1
    rw [flat z zu,div_self kp.ne']
  have nz := (unit_columns hq tight).2 s su
  exact nz (by simp only [v,maskReal,ite_eq_right st,zero_div])

#print axioms two_levels
#print axioms support_iff
#print axioms canonical_debit
#print axioms correction
#print axioms supported_failure
#print axioms exterior_with_child
#print axioms exterior_correction
#print axioms hall_deficit
#print axioms on_source
#print axioms survivor_oscillation
end LeanCH.BR.Closure.CanonicalCycleLaw
