import checkpoints.shen_extension.TwoSeymourVertices
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.StdSimplex

/-!
Weighted second neighbourhoods and the dual weighting on tied vertices.

* `weighted_good_nat`, `weighted_good_real`: for positive weights some vertex has
  second-neighbourhood weight at least first-neighbourhood weight (blow-up, then rounding).
* `tied_dual`: if no vertex is strict at `w`, there is a probability weighting `p` on the
  tied vertices such that every coordinate is balanced:
  `p {v | z ∈ S(v)} = p {v | z ∈ O(v)}` for every `z`.
* `tied_cycle`: in a sinkless graph with no strict vertex, some nonempty set of tied vertices
  has a predecessor inside the set for each of its members.
-/

namespace LeanCH.BR.TwoSeymour

open OAI.SeymourSecondNeighborhood
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem weighted_good_nat [Nonempty V] (r : V → V → Prop) (hr : IsOriented r)
    (w : V → ℕ) (hw : ∀ v, 0 < w v) :
    ∃ v, ∑ z ∈ firstNeighbors r v, w z ≤ ∑ z ∈ secondNeighbors r v, w z := by
  classical
  have hne : Nonempty (Σ v : V, Fin (w v)) := ⟨⟨Classical.arbitrary V, ⟨0, hw _⟩⟩⟩
  let R : (Σ v : V, Fin (w v)) → (Σ v : V, Fin (w v)) → Prop := fun a b => r a.1 b.1
  have hR : IsOriented R :=
    ⟨fun a => hr.loopless a.1, fun hab hba => hr.asymmetric hab hba⟩
  obtain ⟨a, good⟩ := exists_goodVertex R hR
  refine ⟨a.1, ?_⟩
  have hfirst : firstNeighbors R a =
      (firstNeighbors r a.1).sigma (fun z => (Finset.univ : Finset (Fin (w z)))) := by
    ext b
    constructor
    · intro hb
      have hab : r a.1 b.1 := (mem_firstNeighbors (r := R)).mp hb
      exact Finset.mem_sigma.mpr ⟨mem_firstNeighbors.mpr hab, Finset.mem_univ _⟩
    · intro hb
      have hab : r a.1 b.1 := mem_firstNeighbors.mp (Finset.mem_sigma.mp hb).1
      exact (mem_firstNeighbors (r := R)).mpr hab
  have hsecond : secondNeighbors R a ⊆
      (secondNeighbors r a.1).sigma (fun z => (Finset.univ : Finset (Fin (w z)))) := by
    intro b hb
    obtain ⟨_, hnot, u, hau, hub⟩ := (mem_secondNeighbors (r := R)).mp hb
    have hau' : r a.1 u.1 := hau
    have hub' : r u.1 b.1 := hub
    have hnot' : ¬ r a.1 b.1 := hnot
    refine Finset.mem_sigma.mpr
      ⟨mem_secondNeighbors.mpr ⟨?_, hnot', u.1, hau', hub'⟩, Finset.mem_univ _⟩
    intro heq
    rw [heq] at hub'
    exact hr.asymmetric hau' hub'
  have h1 := congrArg Finset.card hfirst
  have h2 := Finset.card_le_card hsecond
  simp only [Finset.card_sigma, Finset.card_univ, Fintype.card_fin] at h1 h2
  unfold GoodVertex at good
  omega

theorem weighted_good_real [Nonempty V] (r : V → V → Prop) (hr : IsOriented r)
    (w : V → ℝ) (hw : ∀ v, 0 < w v) :
    ∃ v, ∑ z ∈ firstNeighbors r v, w z ≤ ∑ z ∈ secondNeighbors r v, w z := by
  classical
  by_contra hno
  have hlt : ∀ v, ∑ z ∈ secondNeighbors r v, w z < ∑ z ∈ firstNeighbors r v, w z := by
    intro v
    by_contra hv
    exact hno ⟨v, not_lt.mp hv⟩
  obtain ⟨v0, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun v => ∑ z ∈ firstNeighbors r v, w z - ∑ z ∈ secondNeighbors r v, w z)
    Finset.univ_nonempty
  have hεpos : 0 < ∑ z ∈ firstNeighbors r v0, w z - ∑ z ∈ secondNeighbors r v0, w z :=
    sub_pos.mpr (hlt v0)
  obtain ⟨N, hN⟩ := exists_nat_gt ((Fintype.card V : ℝ) /
    (∑ z ∈ firstNeighbors r v0, w z - ∑ z ∈ secondNeighbors r v0, w z))
  have hNpos : (0 : ℝ) < N :=
    lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg _) hεpos.le) hN
  have hNε : (Fintype.card V : ℝ) <
      N * (∑ z ∈ firstNeighbors r v0, w z - ∑ z ∈ secondNeighbors r v0, w z) := by
    rwa [div_lt_iff₀ hεpos] at hN
  have hw' : ∀ z, 0 < ⌈(N : ℝ) * w z⌉₊ := fun z => Nat.ceil_pos.mpr (mul_pos hNpos (hw z))
  obtain ⟨v, hv⟩ := weighted_good_nat r hr (fun z => ⌈(N : ℝ) * w z⌉₊) hw'
  have hv' : (∑ z ∈ firstNeighbors r v, ((⌈(N : ℝ) * w z⌉₊ : ℕ) : ℝ)) ≤
      ∑ z ∈ secondNeighbors r v, ((⌈(N : ℝ) * w z⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast hv
  have lower : ∑ z ∈ firstNeighbors r v, (N : ℝ) * w z ≤
      ∑ z ∈ firstNeighbors r v, ((⌈(N : ℝ) * w z⌉₊ : ℕ) : ℝ) :=
    Finset.sum_le_sum (fun z _ => Nat.le_ceil _)
  have upper : ∑ z ∈ secondNeighbors r v, ((⌈(N : ℝ) * w z⌉₊ : ℕ) : ℝ) ≤
      ∑ z ∈ secondNeighbors r v, ((N : ℝ) * w z + 1) :=
    Finset.sum_le_sum (fun z _ =>
      (Nat.ceil_lt_add_one (mul_nonneg hNpos.le (hw z).le)).le)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at upper
  have hcard : ((secondNeighbors r v).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Finset.card_le_univ _
  rw [← Finset.mul_sum] at lower upper
  have hgap := hmin v (Finset.mem_univ v)
  have hmul := mul_le_mul_of_nonneg_left hgap hNpos.le
  rw [mul_sub] at hmul hNε
  rw [mul_sub] at hmul
  linarith

theorem sum_abs_bound (A : Finset V) (u : V → ℝ) : |∑ z ∈ A, u z| ≤ ∑ z, |u z| :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun _ _ _ => abs_nonneg _))

theorem sum_indicator_mul (A : Finset V) (u : V → ℝ) :
    ∑ z, (if z ∈ A then (1 : ℝ) else 0) * u z = ∑ z ∈ A, u z := by
  classical
  have h : ∀ z ∈ (Finset.univ : Finset V),
      (if z ∈ A then (1 : ℝ) else 0) * u z = if z ∈ A then u z else 0 := by
    intro z _
    by_cases hz : z ∈ A
    · simp [hz]
    · simp [hz]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_mem, Finset.univ_inter]

/-- The dual weighting on tied vertices. -/
theorem tied_dual [Nonempty V] (r : V → V → Prop) (hr : IsOriented r)
    (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hno : ∀ v, ∑ z ∈ secondNeighbors r v, w z ≤ ∑ z ∈ firstNeighbors r v, w z) :
    ∃ p : V → ℝ, (∀ v, 0 ≤ p v) ∧ ∑ v, p v = 1 ∧
      (∀ v, p v ≠ 0 →
        ∑ z ∈ secondNeighbors r v, w z = ∑ z ∈ firstNeighbors r v, w z) ∧
      ∀ z, ∑ v ∈ Finset.univ.filter (fun v => z ∈ secondNeighbors r v), p v =
        ∑ v ∈ Finset.univ.filter (fun v => z ∈ firstNeighbors r v), p v := by
  classical
  let a : V → V → ℝ := fun v z =>
    (if z ∈ secondNeighbors r v then (1 : ℝ) else 0) -
      (if z ∈ firstNeighbors r v then (1 : ℝ) else 0)
  have hdot : ∀ (v : V) (u : V → ℝ), ∑ z, a v z * u z =
      ∑ z ∈ secondNeighbors r v, u z - ∑ z ∈ firstNeighbors r v, u z := by
    intro v u
    simp only [a, sub_mul, Finset.sum_sub_distrib, sum_indicator_mul]
  let tied : V → Prop := fun v =>
    ∑ z ∈ secondNeighbors r v, w z = ∑ z ∈ firstNeighbors r v, w z
  let Z : Set (V → ℝ) := {p | ∀ v, ¬ tied v → p v = 0}
  let L : (V → ℝ) → (V → ℝ) := fun p z => ∑ v, p v * a v z
  have hLlin : IsLinearMap ℝ L := by
    constructor
    · intro p q
      funext z
      simp only [L, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    · intro c p
      funext z
      simp only [L, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
  have hLcont : Continuous L := by
    apply continuous_pi
    intro z
    exact continuous_finsetSum _ (fun v _ => (continuous_apply v).mul continuous_const)
  have hZclosed : IsClosed Z := by
    have : Z = ⋂ v, ⋂ (_ : ¬ tied v), {p : V → ℝ | p v = 0} := by
      ext p
      simp only [Z, Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter (fun v => isClosed_iInter (fun _ =>
      isClosed_eq (continuous_apply v) continuous_const))
  have hZconvex : Convex ℝ Z := by
    intro p hp q hq c d _ _ _ v hv
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp v hv, hq v hv, mul_zero, add_zero]
  have hcompact : IsCompact (stdSimplex ℝ V ∩ Z) :=
    (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex ℝ V)
      (stdSimplex_subset_Icc ℝ)).inter_right hZclosed
  have hKclosed : IsClosed (L '' (stdSimplex ℝ V ∩ Z)) := (hcompact.image hLcont).isClosed
  have hKconvex : Convex ℝ (L '' (stdSimplex ℝ V ∩ Z)) :=
    ((convex_stdSimplex ℝ V).inter hZconvex).is_linear_image hLlin
  by_cases h0 : (0 : V → ℝ) ∈ L '' (stdSimplex ℝ V ∩ Z)
  · obtain ⟨p, ⟨hps, hpZ⟩, hLp⟩ := h0
    refine ⟨p, hps.1, hps.2, ?_, ?_⟩
    · intro v hv
      by_contra hnt
      exact hv (hpZ v hnt)
    · intro z
      have hz : L p z = 0 := by rw [hLp]; rfl
      have e1 : ∑ v ∈ Finset.univ.filter (fun v => z ∈ secondNeighbors r v), p v =
          ∑ v, p v * (if z ∈ secondNeighbors r v then (1 : ℝ) else 0) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : z ∈ secondNeighbors r v
        · simp [hv]
        · simp [hv]
      have e2 : ∑ v ∈ Finset.univ.filter (fun v => z ∈ firstNeighbors r v), p v =
          ∑ v, p v * (if z ∈ firstNeighbors r v then (1 : ℝ) else 0) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : z ∈ firstNeighbors r v
        · simp [hv]
        · simp [hv]
      have hsplit : L p z =
          ∑ v, p v * (if z ∈ secondNeighbors r v then (1 : ℝ) else 0) -
            ∑ v, p v * (if z ∈ firstNeighbors r v then (1 : ℝ) else 0) := by
        simp only [L, a, mul_sub, Finset.sum_sub_distrib]
      rw [e1, e2]
      linarith
  · exfalso
    obtain ⟨f, s, hf0, hfK⟩ := geometric_hahn_banach_point_closed hKconvex hKclosed h0
    rw [map_zero] at hf0
    have hrep : ∀ b : V → ℝ, f b = ∑ z, b z * f (Pi.single z 1) := by
      intro b
      have h := congrArg f (pi_eq_sum_univ' b)
      rw [map_sum] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro z _
      rw [map_smul, smul_eq_mul]
    -- tied vertices lie on the positive side
    have htied : ∀ v, tied v → 0 < f (a v) := by
      intro v hv
      have hmem : a v ∈ L '' (stdSimplex ℝ V ∩ Z) := by
        refine ⟨Pi.single v 1, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · intro x
          by_cases hx : x = v
          · rw [hx, Pi.single_eq_same]
            exact zero_le_one
          · rw [Pi.single_eq_of_ne hx]
        · rw [Finset.sum_pi_single']
          simp
        · intro x hx
          have hxv : x ≠ v := by
            intro heq
            rw [heq] at hx
            exact hx hv
          exact Pi.single_eq_of_ne hxv 1
        · funext z
          show ∑ x, (Pi.single v (1 : ℝ) : V → ℝ) x * a x z = a v z
          rw [Finset.sum_eq_single v]
          · rw [Pi.single_eq_same, one_mul]
          · intro x _ hx
            rw [Pi.single_eq_of_ne hx, zero_mul]
          · intro hv'
            exact absurd (Finset.mem_univ v) hv'
      linarith [hfK (a v) hmem]
    let u : V → ℝ := fun z => - f (Pi.single z 1)
    have hu : ∀ v, tied v →
        ∑ z ∈ secondNeighbors r v, u z < ∑ z ∈ firstNeighbors r v, u z := by
      intro v hv
      have h1 := hdot v u
      have h2 : ∑ z, a v z * u z = - f (a v) := by
        rw [hrep (a v), ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro z _
        simp only [u, mul_neg]
      have h3 := htied v hv
      linarith
    -- sizes of the perturbation
    obtain ⟨z0, -, hwmin⟩ := Finset.exists_min_image Finset.univ w Finset.univ_nonempty
    let gap : V → ℝ := fun v => if tied v then 1 else
      ∑ z ∈ firstNeighbors r v, w z - ∑ z ∈ secondNeighbors r v, w z
    have hgappos : ∀ v, 0 < gap v := by
      intro v
      by_cases hv : tied v
      · simp only [gap, hv, if_true]
        exact one_pos
      · simp only [gap, hv, if_false]
        have hle := hno v
        have hne : ∑ z ∈ secondNeighbors r v, w z ≠ ∑ z ∈ firstNeighbors r v, w z := hv
        have := lt_of_le_of_ne hle hne
        linarith
    obtain ⟨v1, -, hgmin⟩ := Finset.exists_min_image Finset.univ gap Finset.univ_nonempty
    have hεpos : 0 < min (w z0) (gap v1) := lt_min (hw z0) (hgappos v1)
    have hUnn : 0 ≤ ∑ z, |u z| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hMpos : 0 < 1 + 2 * ∑ z, |u z| := by linarith
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = min (w z0) (gap v1) / (2 * (1 + 2 * ∑ z, |u z|)) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by
      rw [hδ]
      exact div_pos hεpos (by linarith)
    have hδM : δ * (1 + 2 * ∑ z, |u z|) = min (w z0) (gap v1) / 2 := by
      rw [hδ]
      field_simp
    have hδU : 2 * (δ * ∑ z, |u z|) < min (w z0) (gap v1) / 2 := by
      have : 2 * (δ * ∑ z, |u z|) < δ * (1 + 2 * ∑ z, |u z|) := by nlinarith
      linarith
    have hsum : ∀ A : Finset V, ∑ z ∈ A, (w z + δ * u z) =
        ∑ z ∈ A, w z + δ * ∑ z ∈ A, u z := by
      intro A
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have hw'pos : ∀ z, 0 < w z + δ * u z := by
      intro z
      have h1 : |u z| ≤ ∑ x, |u x| :=
        Finset.single_le_sum (fun x _ => abs_nonneg (u x)) (Finset.mem_univ z)
      have h2 : -|u z| ≤ u z := neg_abs_le (u z)
      have h3 : min (w z0) (gap v1) ≤ w z :=
        (min_le_left _ _).trans (hwmin z (Finset.mem_univ z))
      have h4 : δ * |u z| ≤ δ * ∑ x, |u x| := mul_le_mul_of_nonneg_left h1 hδpos.le
      have h5 : -(δ * |u z|) ≤ δ * u z := by nlinarith
      linarith
    obtain ⟨v, hv⟩ := weighted_good_real r hr (fun z => w z + δ * u z) hw'pos
    rw [hsum, hsum] at hv
    by_cases hvt : tied v
    · have h1 := hu v hvt
      have h2 : ∑ z ∈ secondNeighbors r v, w z = ∑ z ∈ firstNeighbors r v, w z := hvt
      have h3 : δ * ∑ z ∈ secondNeighbors r v, u z < δ * ∑ z ∈ firstNeighbors r v, u z :=
        mul_lt_mul_of_pos_left h1 hδpos
      linarith
    · have hg : gap v = ∑ z ∈ firstNeighbors r v, w z - ∑ z ∈ secondNeighbors r v, w z := by
        simp only [gap, hvt, if_false]
      have h1 : min (w z0) (gap v1) ≤ gap v :=
        (min_le_right _ _).trans (hgmin v (Finset.mem_univ v))
      have hS := sum_abs_bound (secondNeighbors r v) u
      have hO := sum_abs_bound (firstNeighbors r v) u
      have hS' : ∑ z ∈ secondNeighbors r v, u z ≤ ∑ z, |u z| := (le_abs_self _).trans hS
      have hO' : -(∑ z, |u z|) ≤ ∑ z ∈ firstNeighbors r v, u z :=
        (neg_le_neg hO).trans (neg_abs_le _)
      have h2 : δ * ∑ z ∈ secondNeighbors r v, u z ≤ δ * ∑ z, |u z| :=
        mul_le_mul_of_nonneg_left hS' hδpos.le
      have h3 : δ * (-(∑ z, |u z|)) ≤ δ * ∑ z ∈ firstNeighbors r v, u z :=
        mul_le_mul_of_nonneg_left hO' hδpos.le
      rw [mul_neg] at h3
      linarith

/-- In a sinkless graph with no strict vertex, some nonempty set of tied vertices is
closed under taking a predecessor. -/
theorem tied_cycle [Nonempty V] (r : V → V → Prop) (hr : IsOriented r)
    (hsl : ∀ v, ∃ z, r v z) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hno : ∀ v, ∑ z ∈ secondNeighbors r v, w z ≤ ∑ z ∈ firstNeighbors r v, w z) :
    ∃ T : Finset V, T.Nonempty ∧
      (∀ v ∈ T, ∑ z ∈ secondNeighbors r v, w z = ∑ z ∈ firstNeighbors r v, w z) ∧
      ∀ v ∈ T, ∃ u ∈ T, r u v := by
  classical
  -- a smallest nonempty out-closed set
  let F : Finset (Finset V) :=
    Finset.univ.filter (fun C => C.Nonempty ∧ image r C ⊆ C)
  have hF : F.Nonempty :=
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.univ_nonempty,
      Finset.subset_univ _⟩⟩
  obtain ⟨C, hCF, hCmin⟩ := Finset.exists_min_image F Finset.card hF
  obtain ⟨-, hCne, hcl⟩ := Finset.mem_filter.mp hCF
  have hminimal : ∀ C' : Finset V, C'.Nonempty → image r C' ⊆ C' → C' ⊆ C → C' = C := by
    intro C' hne' hcl' hsub
    have hle := hCmin C' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne', hcl'⟩)
    exact Finset.eq_of_subset_of_card_le hsub hle
  have hneC : Nonempty ↥C := ⟨⟨hCne.choose, hCne.choose_spec⟩⟩
  have hsumS : ∀ v : ↥C, ∑ z ∈ secondNeighbors (induced r C) v, w z.1 =
      ∑ z ∈ secondNeighbors r v.1, w z := by
    intro v
    rw [← secondNeighbors_induced_map hcl v, Finset.sum_map]
    rfl
  have hsumO : ∀ v : ↥C, ∑ z ∈ firstNeighbors (induced r C) v, w z.1 =
      ∑ z ∈ firstNeighbors r v.1, w z := by
    intro v
    rw [← firstNeighbors_induced_map hcl v, Finset.sum_map]
    rfl
  obtain ⟨p, hpnn, hpsum, hptied, hpcoord⟩ := tied_dual (induced r C)
    (isOriented_induced hr C) (fun z : ↥C => w z.1) (fun z => hw z.1) (by
      intro v
      rw [hsumS, hsumO]
      exact hno v.1)
  let T0 : Finset ↥C := Finset.univ.filter (fun c => p c ≠ 0)
  have hT0ne : T0.Nonempty := by
    by_contra hemp
    have hall : ∀ c ∈ (Finset.univ : Finset ↥C), p c = 0 := by
      intro c _
      by_contra hc
      exact hemp ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩⟩
    rw [Finset.sum_eq_zero hall] at hpsum
    exact zero_ne_one hpsum
  -- the union of the first neighbourhoods of the support is out-closed
  let W : Finset ↥C := image (induced r C) T0
  have hWclosed : ∀ z ∈ W, ∀ z' : ↥C, r z.1 z'.1 → z' ∈ W := by
    intro z hz z' hzz'
    obtain ⟨v, hvT, hvz⟩ := mem_image.mp hz
    have hvz' : r v.1 z.1 := hvz
    have hpv : p v ≠ 0 := (Finset.mem_filter.mp hvT).2
    by_cases hdirect : r v.1 z'.1
    · exact mem_image.mpr ⟨v, hvT, hdirect⟩
    · have hsec : z' ∈ secondNeighbors (induced r C) v := by
        apply mem_secondNeighbors.mpr
        refine ⟨?_, hdirect, z, hvz', hzz'⟩
        intro heq
        rw [heq] at hzz'
        exact hr.asymmetric hvz' hzz'
      have hpos : 0 < ∑ x ∈ Finset.univ.filter
          (fun x => z' ∈ secondNeighbors (induced r C) x), p x := by
        have hle := Finset.single_le_sum (f := p)
          (s := Finset.univ.filter (fun x => z' ∈ secondNeighbors (induced r C) x))
          (fun x _ => hpnn x) (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hsec⟩)
        have := lt_of_le_of_ne (hpnn v) (Ne.symm hpv)
        linarith
      rw [hpcoord z'] at hpos
      obtain ⟨x, hx, hpx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
      have hxz' : r x.1 z'.1 :=
        (mem_firstNeighbors (r := induced r C)).mp (Finset.mem_filter.mp hx).2
      exact mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hpx⟩, hxz'⟩
  have hWne : W.Nonempty := by
    obtain ⟨v, hv⟩ := hT0ne
    obtain ⟨z, hz⟩ := hsl v.1
    have hzC : z ∈ C := hcl (mem_image.mpr ⟨v.1, v.2, hz⟩)
    exact ⟨⟨z, hzC⟩, mem_image.mpr ⟨v, hv, hz⟩⟩
  have hWall : W.map ⟨Subtype.val, Subtype.val_injective⟩ = C := by
    apply hminimal
    · obtain ⟨z, hz⟩ := hWne
      exact ⟨z.1, Finset.mem_map.mpr ⟨z, hz, rfl⟩⟩
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := mem_image.mp hy
      obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp hx
      have hzx' : z.1 = x := hzx
      rw [← hzx'] at hxy
      have hyC : y ∈ C := hcl (mem_image.mpr ⟨z.1, z.2, hxy⟩)
      exact Finset.mem_map.mpr ⟨⟨y, hyC⟩, hWclosed z hz ⟨y, hyC⟩ hxy, rfl⟩
    · intro y hy
      obtain ⟨z, _, hzy⟩ := Finset.mem_map.mp hy
      have hzy' : z.1 = y := hzy
      rw [← hzy']
      exact z.2
  refine ⟨T0.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hT0ne
    exact ⟨v.1, Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩
  · intro y hy
    obtain ⟨v, hv, hvy⟩ := Finset.mem_map.mp hy
    have hvy' : v.1 = y := hvy
    rw [← hvy', ← hsumS v, ← hsumO v]
    exact hptied v (Finset.mem_filter.mp hv).2
  · intro y hy
    obtain ⟨v, hv, hvy⟩ := Finset.mem_map.mp hy
    have hvy' : v.1 = y := hvy
    have hvW : v.1 ∈ W.map ⟨Subtype.val, Subtype.val_injective⟩ := by
      rw [hWall]
      exact v.2
    obtain ⟨z, hz, hzv⟩ := Finset.mem_map.mp hvW
    have hzv' : z = v := Subtype.ext hzv
    rw [hzv'] at hz
    obtain ⟨u, hu, huv⟩ := mem_image.mp hz
    have huv' : r u.1 v.1 := huv
    rw [hvy'] at huv'
    exact ⟨u.1, Finset.mem_map.mpr ⟨u, hu, rfl⟩, huv'⟩

end LeanCH.BR.TwoSeymour

#print axioms LeanCH.BR.TwoSeymour.weighted_good_real
#print axioms LeanCH.BR.TwoSeymour.tied_dual
#print axioms LeanCH.BR.TwoSeymour.tied_cycle
