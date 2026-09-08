import Definitions.Def_TranscendenceTowerConverse

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower.FiniteInformation
open TranscendenceTower.ConversePlatform

/-! ## Two-variable groundwork -/

private theorem c_fstMarginal_nonneg {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (h : ∀ a b, 0 ≤ joint a b) (a : α) :
    0 ≤ fstMarginal joint a :=
  Finset.sum_nonneg fun b _ => h a b

private theorem c_sndMarginal_nonneg {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (h : ∀ a b, 0 ≤ joint a b) (b : β) :
    0 ≤ sndMarginal joint b :=
  Finset.sum_nonneg fun a _ => h a b

private theorem c_sum_sndMarginal {α β : Type} [Fintype α] [Fintype β]
    (joint : α → β → ℝ) :
    ∑ b, sndMarginal joint b = ∑ a, ∑ b, joint a b := by
  simp only [sndMarginal]
  exact Finset.sum_comm

private theorem c_le_fst {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) (a : α) (b : β) :
    joint a b ≤ fstMarginal joint a :=
  Finset.single_le_sum (f := fun b => joint a b)
    (fun b _ => hnn a b) (Finset.mem_univ b)

private theorem c_le_snd {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) (a : α) (b : β) :
    joint a b ≤ sndMarginal joint b :=
  Finset.single_le_sum (f := fun a => joint a b)
    (fun a _ => hnn a b) (Finset.mem_univ a)

private theorem c_chain_cell {j pa : ℝ} (hj : 0 ≤ j) (hle : j ≤ pa) :
    shannon j
      = (if j = 0 then 0 else j * Real.log (pa / j)) + j * Real.log pa⁻¹ := by
  by_cases hz : j = 0
  · simp [hz]
  · have hjpos : 0 < j := lt_of_le_of_ne hj (Ne.symm hz)
    have hpa : 0 < pa := lt_of_lt_of_le hjpos hle
    simp only [hz, if_false, shannon]
    rw [Real.log_div (ne_of_gt hpa) hz, Real.log_inv, Real.log_inv]
    ring

private theorem c_chain_rule {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) :
    jointEntropy joint = entropy (fstMarginal joint) + condEntropy joint := by
  unfold jointEntropy entropy condEntropy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsplit : ∀ b ∈ (Finset.univ : Finset β),
      shannon (joint a b)
        = (if joint a b = 0 then 0
            else joint a b * Real.log (fstMarginal joint a / joint a b))
          + joint a b * Real.log (fstMarginal joint a)⁻¹ :=
    fun b _ => c_chain_cell (hnn a b) (c_le_fst hnn a b)
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [shannon, fstMarginal]
  ring

private theorem c_mi_cell {j pa pb : ℝ} (hj : 0 ≤ j) (hja : j ≤ pa) (hjb : j ≤ pb) :
    (if j = 0 then 0 else j * Real.log (j / (pa * pb)))
      = j * Real.log pa⁻¹ + j * Real.log pb⁻¹ - shannon j := by
  by_cases hz : j = 0
  · simp [hz]
  · have hjpos : 0 < j := lt_of_le_of_ne hj (Ne.symm hz)
    have hpa : 0 < pa := lt_of_lt_of_le hjpos hja
    have hpb : 0 < pb := lt_of_lt_of_le hjpos hjb
    simp only [hz, if_false, shannon]
    rw [Real.log_div hz (by positivity),
      Real.log_mul (ne_of_gt hpa) (ne_of_gt hpb),
      Real.log_inv, Real.log_inv, Real.log_inv]
    ring

private theorem c_mi_eq_entropies {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) :
    mutualInfo joint
      = entropy (fstMarginal joint) + entropy (sndMarginal joint)
        - jointEntropy joint := by
  have hrw : mutualInfo joint
      = ∑ a, ∑ b, (joint a b * Real.log (fstMarginal joint a)⁻¹
          + joint a b * Real.log (sndMarginal joint b)⁻¹
          - shannon (joint a b)) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      c_mi_cell (hnn a b) (c_le_fst hnn a b) (c_le_snd hnn a b)
  have e1 : ∑ a, ∑ b, joint a b * Real.log (fstMarginal joint a)⁻¹
      = entropy (fstMarginal joint) :=
    Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_mul]; rfl
  have e2 : ∑ a, ∑ b, joint a b * Real.log (sndMarginal joint b)⁻¹
      = entropy (sndMarginal joint) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [← Finset.sum_mul]; rfl
  rw [hrw]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [e1, e2]
  rfl

private theorem c_mi_eq_sub_cond {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) :
    mutualInfo joint = entropy (sndMarginal joint) - condEntropy joint := by
  rw [c_mi_eq_entropies hnn, c_chain_rule hnn]
  ring

private theorem c_sum_marginal_product {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b)
    (hsum : ∑ a, ∑ b, joint a b = 1) :
    ∑ a, ∑ b, fstMarginal joint a * sndMarginal joint b = 1 := by
  have hfs : ∑ a, fstMarginal joint a = 1 := hsum
  have hss : ∑ b, sndMarginal joint b = 1 := by
    rw [c_sum_sndMarginal]; exact hsum
  have hrow : ∀ a ∈ (Finset.univ : Finset α),
      ∑ b, fstMarginal joint a * sndMarginal joint b
        = fstMarginal joint a * ∑ b, sndMarginal joint b :=
    fun a _ => (Finset.mul_sum _ _ _).symm
  rw [Finset.sum_congr rfl hrow, ← Finset.sum_mul, hfs, hss, one_mul]

private theorem c_mi_nonneg {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b)
    (hsum : ∑ a, ∑ b, joint a b = 1) : 0 ≤ mutualInfo joint := by
  have hcell : ∀ a b,
      -(if joint a b = 0 then 0
        else joint a b *
          Real.log (joint a b / (fstMarginal joint a * sndMarginal joint b)))
        ≤ fstMarginal joint a * sndMarginal joint b - joint a b := by
    intro a b
    by_cases hz : joint a b = 0
    · rw [hz]
      simpa using mul_nonneg (c_fstMarginal_nonneg hnn a) (c_sndMarginal_nonneg hnn b)
    · have hjpos : 0 < joint a b := lt_of_le_of_ne (hnn a b) (Ne.symm hz)
      have hpa : 0 < fstMarginal joint a := lt_of_lt_of_le hjpos (c_le_fst hnn a b)
      have hpb : 0 < sndMarginal joint b := lt_of_lt_of_le hjpos (c_le_snd hnn a b)
      simp only [hz, if_false]
      have hflip : -(joint a b *
            Real.log (joint a b / (fstMarginal joint a * sndMarginal joint b)))
          = joint a b *
            Real.log ((fstMarginal joint a * sndMarginal joint b) / joint a b) := by
        rw [show (fstMarginal joint a * sndMarginal joint b) / joint a b
              = (joint a b / (fstMarginal joint a * sndMarginal joint b))⁻¹ from
            (inv_div _ _).symm, Real.log_inv]
        ring
      rw [hflip]
      have hlog :
          Real.log ((fstMarginal joint a * sndMarginal joint b) / joint a b)
            ≤ (fstMarginal joint a * sndMarginal joint b) / joint a b - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      calc joint a b *
              Real.log ((fstMarginal joint a * sndMarginal joint b) / joint a b)
          ≤ joint a b *
              ((fstMarginal joint a * sndMarginal joint b) / joint a b - 1) :=
            mul_le_mul_of_nonneg_left hlog (le_of_lt hjpos)
        _ = fstMarginal joint a * sndMarginal joint b - joint a b := by field_simp
  have hle : -mutualInfo joint
      ≤ ∑ a, ∑ b, (fstMarginal joint a * sndMarginal joint b - joint a b) := by
    unfold mutualInfo
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun b _ => hcell a b
  have hzero : ∑ a, ∑ b, (fstMarginal joint a * sndMarginal joint b - joint a b)
      = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [c_sum_marginal_product hnn hsum, hsum, sub_self]
  linarith [hle, hzero.ge, hzero.le]

private theorem c_jointEntropy_le_add {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b)
    (hsum : ∑ a, ∑ b, joint a b = 1) :
    jointEntropy joint
      ≤ entropy (fstMarginal joint) + entropy (sndMarginal joint) := by
  have h := c_mi_nonneg hnn hsum
  rw [c_mi_eq_entropies hnn] at h
  linarith

private theorem c_shannon_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    shannon (x * y) = y * shannon x + x * shannon y := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  · unfold shannon
    rw [mul_inv, Real.log_mul (by simpa using hx0) (by simpa using hy0)]
    ring

private theorem c_jointEntropy_product {α β : Type} [Fintype α] [Fintype β]
    {p : α → ℝ} {q : β → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (hps : ∑ a, p a = 1) (hqs : ∑ b, q b = 1) :
    jointEntropy (fun a b => p a * q b) = entropy p + entropy q := by
  unfold jointEntropy entropy
  have hcell : ∀ a ∈ (Finset.univ : Finset α),
      ∑ b, shannon (p a * q b)
        = ∑ b, (q b * shannon (p a) + p a * shannon (q b)) :=
    fun a _ => Finset.sum_congr rfl fun b _ => c_shannon_mul (hp a) (hq b)
  rw [Finset.sum_congr rfl hcell]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hqs,
    one_mul, mul_one]
  rw [hps, one_mul]

/-! ## Words and product laws -/

private theorem c_sum_snoc {β : Type} [Fintype β] [DecidableEq β] {n : ℕ}
    (f : (Fin (n + 1) → β) → ℝ) :
    ∑ w : Fin (n + 1) → β, f w
      = ∑ w : Fin n → β, ∑ b : β, f (Fin.snoc w b) := by
  have h : ∑ p : (Fin n → β) × β, f (Fin.snoc p.1 p.2)
      = ∑ w : Fin (n + 1) → β, f w :=
    Fintype.sum_equiv (snocEquiv n) _ _ (fun _ => rfl)
  rw [← h, Fintype.sum_prod_type]

private theorem c_snd_splitLast {β : Type} [Fintype β] [DecidableEq β] {n : ℕ}
    (law : (Fin (n + 1) → β) → ℝ) :
    sndMarginal (splitLast law) = coordMarginal law (Fin.last n) := by
  funext b
  unfold sndMarginal coordMarginal splitLast
  rw [c_sum_snoc]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [Fin.snoc_last]

private theorem c_coord_fst_splitLast {β : Type} [Fintype β] [DecidableEq β]
    {n : ℕ} (law : (Fin (n + 1) → β) → ℝ) (i : Fin n) :
    coordMarginal (fstMarginal (splitLast law)) i
      = coordMarginal law i.castSucc := by
  funext b
  unfold coordMarginal fstMarginal splitLast
  rw [c_sum_snoc]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : w i = b
  · simp [h]
  · simp [h]

private theorem c_indep_bound {β : Type} [Fintype β] [DecidableEq β] :
    ∀ (n : ℕ) (law : (Fin n → β) → ℝ), (∀ w, 0 ≤ law w) → (∑ w, law w = 1) →
      entropy law ≤ ∑ i : Fin n, entropy (coordMarginal law i) := by
  intro n
  induction n with
  | zero =>
    intro law _ hsum
    rw [Finset.univ_unique, Finset.sum_singleton] at hsum
    unfold entropy
    rw [Finset.univ_unique, Finset.sum_singleton, hsum, shannon_one]
    simp
  | succ n ih =>
    intro law hnn hsum
    have hjn : ∀ w b, 0 ≤ splitLast law w b := fun _ _ => hnn _
    have hjs : ∑ w : Fin n → β, ∑ b : β, splitLast law w b = 1 := by
      unfold splitLast
      rw [← c_sum_snoc]
      exact hsum
    have hsplit : entropy law = jointEntropy (splitLast law) := by
      unfold entropy jointEntropy splitLast
      exact c_sum_snoc _
    have hsub := c_jointEntropy_le_add hjn hjs
    have hih := ih (fstMarginal (splitLast law))
      (fun w => Finset.sum_nonneg fun b _ => hjn w b) hjs
    rw [hsplit]
    have hlast : entropy (sndMarginal (splitLast law))
        = entropy (coordMarginal law (Fin.last n)) := by
      rw [c_snd_splitLast]
    have hrest : ∑ i : Fin n, entropy (coordMarginal (fstMarginal (splitLast law)) i)
        = ∑ i : Fin n, entropy (coordMarginal law i.castSucc) :=
      Finset.sum_congr rfl fun i _ => by rw [c_coord_fst_splitLast]
    rw [hrest] at hih
    rw [Fin.sum_univ_castSucc]
    linarith [hsub, hih, hlast.ge, hlast.le]

private theorem c_productLaw_snoc {β : Type} [Fintype β] [DecidableEq β] {n : ℕ}
    (rows : Fin (n + 1) → β → ℝ) (w : Fin n → β) (b : β) :
    productLaw rows (Fin.snoc w b)
      = productLaw (fun i => rows i.castSucc) w * rows (Fin.last n) b := by
  unfold productLaw
  rw [Fin.prod_univ_castSucc]
  simp

private theorem c_productLaw_nonneg {β : Type} [Fintype β] [DecidableEq β]
    {n : ℕ} {rows : Fin n → β → ℝ} (hnn : ∀ i b, 0 ≤ rows i b) (w : Fin n → β) :
    0 ≤ productLaw rows w :=
  Finset.prod_nonneg fun i _ => hnn i (w i)

private theorem c_sum_productLaw {β : Type} [Fintype β] [DecidableEq β] :
    ∀ (n : ℕ) (rows : Fin n → β → ℝ),
      ∑ w : Fin n → β, productLaw rows w = ∏ i, ∑ b, rows i b := by
  intro n
  induction n with
  | zero =>
    intro rows
    rw [Finset.univ_unique, Finset.sum_singleton]
    simp [productLaw]
  | succ n ih =>
    intro rows
    rw [c_sum_snoc]
    have hrow : ∀ w ∈ (Finset.univ : Finset (Fin n → β)),
        ∑ b, productLaw rows (Fin.snoc w b)
          = productLaw (fun i => rows i.castSucc) w * ∑ b, rows (Fin.last n) b := by
      intro w _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => c_productLaw_snoc rows w b
    rw [Finset.sum_congr rfl hrow, ← Finset.sum_mul, ih, Fin.prod_univ_castSucc]

private theorem c_entropy_productLaw {β : Type} [Fintype β] [DecidableEq β] :
    ∀ (n : ℕ) (rows : Fin n → β → ℝ), (∀ i b, 0 ≤ rows i b) →
      (∀ i, ∑ b, rows i b = 1) →
      entropy (productLaw rows) = ∑ i : Fin n, entropy (rows i) := by
  intro n
  induction n with
  | zero =>
    intro rows _ _
    unfold entropy
    rw [Finset.univ_unique, Finset.sum_singleton]
    simp [productLaw]
  | succ n ih =>
    intro rows hnn hsum
    have hrest : ∀ (i : Fin n) (b : β), 0 ≤ rows (Fin.castSucc i) b :=
      fun i b => hnn _ b
    have hrests : ∀ i : Fin n, ∑ b, rows (Fin.castSucc i) b = 1 := fun i => hsum _
    have hprefix : ∑ w : Fin n → β, productLaw (fun i => rows i.castSucc) w = 1 := by
      rw [c_sum_productLaw]
      simp [hrests]
    have hsplit : entropy (productLaw rows)
        = jointEntropy (fun (w : Fin n → β) (b : β) =>
            productLaw (fun i => rows i.castSucc) w * rows (Fin.last n) b) := by
      unfold entropy jointEntropy
      rw [c_sum_snoc]
      exact Finset.sum_congr rfl fun w _ =>
        Finset.sum_congr rfl fun b _ => by rw [c_productLaw_snoc]
    rw [hsplit, c_jointEntropy_product (c_productLaw_nonneg hrest)
      (fun b => hnn (Fin.last n) b) hprefix (hsum (Fin.last n)),
      ih (fun i => rows i.castSucc) hrest hrests, Fin.sum_univ_castSucc]

/-! ## The memoryless channel joint -/

private theorem c_fst_channelJoint {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {n : ℕ} (prior : (Fin n → α) → ℝ)
    (K : α → β → ℝ) (hK : ∀ a, ∑ b, K a b = 1) :
    fstMarginal (channelJoint prior K) = prior := by
  funext x
  unfold fstMarginal channelJoint
  rw [← Finset.mul_sum, c_sum_productLaw]
  simp [hK]

private theorem c_cond_cell {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (if p * q = 0 then 0 else (p * q) * Real.log (p / (p * q)))
      = p * shannon q := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hq0 : q = 0
  · simp [hq0]
  · have hpq : p * q ≠ 0 := mul_ne_zero hp0 hq0
    simp only [hpq, if_false, shannon]
    rw [show p / (p * q) = q⁻¹ by field_simp]
    ring

private theorem c_cond_channelJoint {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {n : ℕ} (prior : (Fin n → α) → ℝ)
    (K : α → β → ℝ) (hpn : ∀ x, 0 ≤ prior x) (hKn : ∀ a b, 0 ≤ K a b)
    (hK : ∀ a, ∑ b, K a b = 1) :
    condEntropy (channelJoint prior K)
      = ∑ x : Fin n → α, prior x * ∑ i : Fin n, entropy (K (x i)) := by
  unfold condEntropy
  rw [c_fst_channelJoint prior K hK]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcell : ∀ y ∈ (Finset.univ : Finset (Fin n → β)),
      (if channelJoint prior K x y = 0 then 0
        else channelJoint prior K x y
          * Real.log (prior x / channelJoint prior K x y))
        = prior x * shannon (productLaw (fun i => K (x i)) y) :=
    fun y _ => c_cond_cell (hpn x) (c_productLaw_nonneg (fun i b => hKn _ b) y)
  rw [Finset.sum_congr rfl hcell, ← Finset.mul_sum]
  congr 1
  exact c_entropy_productLaw n (fun i => K (x i)) (fun i b => hKn _ b)
    (fun i => hK _)

private theorem c_sum_apply_coord {α : Type} [Fintype α] [DecidableEq α]
    {n : ℕ} (prior : (Fin n → α) → ℝ) (i : Fin n) (f : α → ℝ) :
    ∑ x : Fin n → α, prior x * f (x i)
      = ∑ a : α, coordMarginal prior i a * f a := by
  unfold coordMarginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  symm
  rw [Finset.sum_eq_single (x i)]
  · simp
  · intro a _ hne
    simp [Ne.symm hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem c_cond_coord {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {n : ℕ} (prior : (Fin n → α) → ℝ)
    (K : α → β → ℝ) (hpn : ∀ x, 0 ≤ prior x) (hKn : ∀ a b, 0 ≤ K a b)
    (hK : ∀ a, ∑ b, K a b = 1) :
    condEntropy (channelJoint prior K)
      = ∑ i : Fin n, ∑ a : α, coordMarginal prior i a * entropy (K a) := by
  rw [c_cond_channelJoint prior K hpn hKn hK]
  have hswap : ∑ x : Fin n → α, prior x * ∑ i : Fin n, entropy (K (x i))
      = ∑ i : Fin n, ∑ x : Fin n → α, prior x * entropy (K (x i)) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]
  exact Finset.sum_congr rfl fun i _ =>
    c_sum_apply_coord prior i (fun a => entropy (K a))

private theorem c_channelJoint_nonneg {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {n : ℕ} {prior : (Fin n → α) → ℝ}
    {K : α → β → ℝ} (hpn : ∀ x, 0 ≤ prior x) (hKn : ∀ a b, 0 ≤ K a b)
    (x : Fin n → α) (y : Fin n → β) : 0 ≤ channelJoint prior K x y :=
  mul_nonneg (hpn x) (c_productLaw_nonneg (fun i b => hKn _ b) y)

private theorem c_sum_channelJoint {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {n : ℕ} {prior : (Fin n → α) → ℝ}
    {K : α → β → ℝ} (hps : ∑ x, prior x = 1) (hK : ∀ a, ∑ b, K a b = 1) :
    ∑ x : Fin n → α, ∑ y : Fin n → β, channelJoint prior K x y = 1 := by
  have h : ∀ x ∈ (Finset.univ : Finset (Fin n → α)),
      ∑ y : Fin n → β, channelJoint prior K x y = prior x :=
    fun x _ => congrFun (c_fst_channelJoint prior K hK) x
  rw [Finset.sum_congr rfl h]
  exact hps

private theorem c_nuse {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {n : ℕ} (prior : (Fin n → α) → ℝ)
    (K : α → β → ℝ) (hpn : ∀ x, 0 ≤ prior x) (hps : ∑ x, prior x = 1)
    (hKn : ∀ a b, 0 ≤ K a b) (hK : ∀ a, ∑ b, K a b = 1) :
    mutualInfo (channelJoint prior K)
      ≤ ∑ i : Fin n,
          (entropy (coordMarginal (sndMarginal (channelJoint prior K)) i)
            - ∑ a : α, coordMarginal prior i a * entropy (K a)) := by
  have hnn := c_channelJoint_nonneg (prior := prior) (K := K) hpn hKn
  have hsum := c_sum_channelJoint (prior := prior) (K := K) hps hK
  have houtnn : ∀ y, 0 ≤ sndMarginal (channelJoint prior K) y :=
    fun y => Finset.sum_nonneg fun x _ => hnn x y
  have houts : ∑ y, sndMarginal (channelJoint prior K) y = 1 := by
    rw [c_sum_sndMarginal]; exact hsum
  have hind := c_indep_bound n (sndMarginal (channelJoint prior K)) houtnn houts
  rw [c_mi_eq_sub_cond hnn, c_cond_coord prior K hpn hKn hK,
    Finset.sum_sub_distrib]
  linarith

/-! ## Fano and the weak converse -/

private theorem c_correct_add_error {γ : Type} [Fintype γ] [DecidableEq γ]
    (J : γ → γ → ℝ) :
    correctProb J + errorProb J = ∑ g, ∑ w, J g w := by
  unfold correctProb errorProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  symm
  have hsplit : ∀ w ∈ (Finset.univ : Finset γ),
      J g w = (if w = g then J g w else 0) + (if w = g then 0 else J g w) :=
    fun w _ => by by_cases h : w = g <;> simp [h]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ g (fun w => J g w)]
  simp

private theorem c_le_correctProb {γ : Type} [Fintype γ] [DecidableEq γ]
    {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w) (g : γ) :
    J g g ≤ correctProb J :=
  Finset.single_le_sum (f := fun g => J g g) (fun g _ => hnn g g)
    (Finset.mem_univ g)

private theorem c_le_errorProb {γ : Type} [Fintype γ] [DecidableEq γ]
    {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w) {g w : γ} (hwg : w ≠ g) :
    J g w ≤ errorProb J := by
  have hrownn : ∀ g' : γ, 0 ≤ ∑ w', if w' = g' then 0 else J g' w' :=
    fun g' => Finset.sum_nonneg fun w' _ => by
      by_cases h : w' = g' <;> simp [h, hnn]
  have h1 : (if w = g then 0 else J g w)
      ≤ ∑ w', if w' = g then 0 else J g w' :=
    Finset.single_le_sum (f := fun w' => if w' = g then 0 else J g w')
      (fun w' _ => by by_cases h : w' = g <;> simp [h, hnn]) (Finset.mem_univ w)
  have h2 : (∑ w', if w' = g then 0 else J g w') ≤ errorProb J :=
    Finset.single_le_sum (f := fun g' => ∑ w', if w' = g' then 0 else J g' w')
      (fun g' _ => hrownn g') (Finset.mem_univ g)
  rw [if_neg hwg] at h1
  linarith

private theorem c_gibbs_cell {j p q : ℝ} (hj : 0 ≤ j) (hjp : j ≤ p) (hq : 0 ≤ q)
    (hjq : j ≠ 0 → 0 < q) :
    (if j = 0 then 0 else j * Real.log (p / j))
      ≤ (if j = 0 then 0 else j * Real.log (p / q)) + (q - j) := by
  by_cases hz : j = 0
  · simp [hz, hq]
  · have hjpos : 0 < j := lt_of_le_of_ne hj (Ne.symm hz)
    have hppos : 0 < p := lt_of_lt_of_le hjpos hjp
    have hqpos : 0 < q := hjq hz
    simp only [hz, if_false]
    have hlog : Real.log (q / j) ≤ q / j - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have key : j * Real.log (p / j) - j * Real.log (p / q)
        = j * Real.log (q / j) := by
      rw [Real.log_div hppos.ne' hjpos.ne', Real.log_div hppos.ne' hqpos.ne',
        Real.log_div hqpos.ne' hjpos.ne']
      ring
    have hmul : j * Real.log (q / j) ≤ j * (q / j - 1) :=
      mul_le_mul_of_nonneg_left hlog hj
    have hfin : j * (q / j - 1) = q - j := by field_simp
    linarith

private theorem c_error_log_split {e m : ℝ} (he : 0 ≤ e) (hm : 0 < m) :
    e * Real.log (e / m)⁻¹ = shannon e + e * Real.log m := by
  by_cases hz : e = 0
  · simp [hz]
  · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
    unfold shannon
    rw [inv_div, Real.log_div hm.ne' hepos.ne', Real.log_inv]
    ring

private theorem c_fano {γ : Type} [Fintype γ] [DecidableEq γ]
    {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w)
    (hsum : ∑ g, ∑ w, J g w = 1) :
    condEntropy J
      ≤ shannon (correctProb J) + shannon (errorProb J)
        + errorProb J * Real.log (Fintype.card γ) := by
  have hne : Nonempty γ := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hsum
  have hM : (0 : ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hPcnn : 0 ≤ correctProb J := Finset.sum_nonneg fun g _ => hnn g g
  have hPenn : 0 ≤ errorProb J :=
    Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun w _ => by
      by_cases h : w = g <;> simp [h, hnn]
  have hpnn : ∀ g : γ, 0 ≤ fstMarginal J g := fun g =>
    Finset.sum_nonneg fun w _ => hnn g w
  have hJp : ∀ g w, J g w ≤ fstMarginal J g := fun g w =>
    Finset.single_le_sum (f := fun w => J g w) (fun w _ => hnn g w)
      (Finset.mem_univ w)
  have hpc : correctProb J + errorProb J = 1 := by
    rw [c_correct_add_error]; exact hsum
  have hwnn : ∀ g w, 0 ≤ fanoWeight J g w := by
    intro g w
    unfold fanoWeight
    by_cases h : w = g
    · simpa [h] using hPcnn
    · have hd : (0 : ℝ) ≤ errorProb J / (Fintype.card γ : ℝ) := by positivity
      simpa [h] using hd
  have hQnn : ∀ g w, 0 ≤ fanoComparison J g w := fun g w =>
    mul_nonneg (hpnn g) (hwnn g w)
  have hwpos : ∀ g w, J g w ≠ 0 → 0 < fanoWeight J g w := by
    intro g w hz
    have hjpos : 0 < J g w := lt_of_le_of_ne (hnn g w) (Ne.symm hz)
    unfold fanoWeight
    by_cases h : w = g
    · subst h
      have hle := c_le_correctProb hnn w
      rw [if_pos rfl]
      linarith
    · rw [if_neg h]
      have hle := c_le_errorProb hnn h
      have hepos : 0 < errorProb J := lt_of_lt_of_le hjpos hle
      positivity
  have hQpos : ∀ g w, J g w ≠ 0 → 0 < fanoComparison J g w := by
    intro g w hz
    have hjpos : 0 < J g w := lt_of_le_of_ne (hnn g w) (Ne.symm hz)
    exact mul_pos (lt_of_lt_of_le hjpos (hJp g w)) (hwpos g w hz)
  have hrow : ∀ g : γ, ∑ w, fanoComparison J g w ≤ fstMarginal J g := by
    intro g
    have hdnn : (0 : ℝ) ≤ fstMarginal J g * (errorProb J / (Fintype.card γ : ℝ)) := by
      have := hpnn g
      positivity
    have hstep : ∀ w ∈ (Finset.univ : Finset γ),
        fanoComparison J g w
          ≤ fstMarginal J g * (if w = g then correctProb J else 0)
            + fstMarginal J g * (errorProb J / (Fintype.card γ : ℝ)) := by
      intro w _
      unfold fanoComparison fanoWeight
      by_cases h : w = g
      · rw [if_pos h, if_pos h]
        linarith
      · rw [if_neg h, if_neg h, mul_zero, zero_add]
    have he1 : ∑ w : γ, fstMarginal J g * (if w = g then correctProb J else 0)
        = fstMarginal J g * correctProb J := by
      rw [← Finset.mul_sum,
        Finset.sum_ite_eq' Finset.univ g (fun _ : γ => correctProb J)]
      simp
    have he2 : ∑ _w : γ, fstMarginal J g * (errorProb J / (Fintype.card γ : ℝ))
        = fstMarginal J g * errorProb J := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    have hle := Finset.sum_le_sum hstep
    rw [Finset.sum_add_distrib, he1, he2] at hle
    calc ∑ w, fanoComparison J g w
        ≤ fstMarginal J g * correctProb J + fstMarginal J g * errorProb J := hle
      _ = fstMarginal J g := by rw [← mul_add, hpc, mul_one]
  have hQsum : ∑ g, ∑ w, fanoComparison J g w ≤ 1 := by
    calc ∑ g, ∑ w, fanoComparison J g w
        ≤ ∑ g, fstMarginal J g := Finset.sum_le_sum fun g _ => hrow g
      _ = 1 := hsum
  have hX : ∀ g w,
      (if J g w = 0 then 0
        else J g w * Real.log (fstMarginal J g / fanoComparison J g w))
        = J g w * Real.log (fanoWeight J g w)⁻¹ := by
    intro g w
    by_cases hz : J g w = 0
    · simp [hz]
    · have hjpos : 0 < J g w := lt_of_le_of_ne (hnn g w) (Ne.symm hz)
      have hppos : 0 < fstMarginal J g := lt_of_lt_of_le hjpos (hJp g w)
      have hcp : 0 < fanoWeight J g w := hwpos g w hz
      rw [if_neg hz]
      unfold fanoComparison
      rw [show fstMarginal J g / (fstMarginal J g * fanoWeight J g w)
            = (fanoWeight J g w)⁻¹ by field_simp]
  have hXsum : ∑ g, ∑ w, J g w * Real.log (fanoWeight J g w)⁻¹
      = shannon (correctProb J)
        + errorProb J * Real.log (errorProb J / (Fintype.card γ : ℝ))⁻¹ := by
    have hrowsplit : ∀ g ∈ (Finset.univ : Finset γ),
        ∑ w, J g w * Real.log (fanoWeight J g w)⁻¹
          = J g g * Real.log (correctProb J)⁻¹
            + ∑ w, (if w = g then 0 else J g w)
                * Real.log (errorProb J / (Fintype.card γ : ℝ))⁻¹ := by
      intro g _
      have hsplit : ∀ w ∈ (Finset.univ : Finset γ),
          J g w * Real.log (fanoWeight J g w)⁻¹
            = (if w = g then J g w * Real.log (correctProb J)⁻¹ else 0)
              + (if w = g then 0 else J g w)
                * Real.log (errorProb J / (Fintype.card γ : ℝ))⁻¹ := by
        intro w _
        unfold fanoWeight
        by_cases h : w = g <;> simp [h]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ g
          (fun w => J g w * Real.log (correctProb J)⁻¹)]
      simp
    have h1 : ∑ g : γ, J g g * Real.log (correctProb J)⁻¹
        = shannon (correctProb J) := by
      unfold shannon correctProb
      rw [Finset.sum_mul]
    have h2 : ∑ g : γ, ∑ w : γ, (if w = g then 0 else J g w)
          * Real.log (errorProb J / (Fintype.card γ : ℝ))⁻¹
        = errorProb J * Real.log (errorProb J / (Fintype.card γ : ℝ))⁻¹ := by
      unfold errorProb
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun g _ => (Finset.sum_mul _ _ _).symm
    rw [Finset.sum_congr rfl hrowsplit, Finset.sum_add_distrib, h1, h2]
  have hbound : condEntropy J
      ≤ (∑ g, ∑ w, J g w * Real.log (fanoWeight J g w)⁻¹)
        + (∑ g, ∑ w, fanoComparison J g w) - 1 := by
    unfold condEntropy
    have hcellsum : ∑ g, ∑ w,
        (if J g w = 0 then 0 else J g w * Real.log (fstMarginal J g / J g w))
          ≤ ∑ g, ∑ w,
              ((if J g w = 0 then 0
                else J g w * Real.log (fstMarginal J g / fanoComparison J g w))
                + (fanoComparison J g w - J g w)) :=
      Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun w _ =>
        c_gibbs_cell (hnn g w) (hJp g w) (hQnn g w) (hQpos g w)
    have hrhs : ∑ g, ∑ w,
        ((if J g w = 0 then 0
          else J g w * Real.log (fstMarginal J g / fanoComparison J g w))
          + (fanoComparison J g w - J g w))
        = (∑ g, ∑ w, J g w * Real.log (fanoWeight J g w)⁻¹)
          + (∑ g, ∑ w, fanoComparison J g w) - 1 := by
      have hstep : ∀ g ∈ (Finset.univ : Finset γ), ∑ w,
          ((if J g w = 0 then 0
            else J g w * Real.log (fstMarginal J g / fanoComparison J g w))
            + (fanoComparison J g w - J g w))
          = (∑ w, J g w * Real.log (fanoWeight J g w)⁻¹)
            + (∑ w, fanoComparison J g w) - (∑ w, J g w) := by
        intro g _
        have hin : ∑ w, (if J g w = 0 then 0
              else J g w * Real.log (fstMarginal J g / fanoComparison J g w))
            = ∑ w, J g w * Real.log (fanoWeight J g w)⁻¹ :=
          Finset.sum_congr rfl fun w _ => hX g w
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hin]
        ring
      rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hsum]
    linarith [hcellsum, hrhs.ge, hrhs.le]
  rw [hXsum, c_error_log_split hPenn hM] at hbound
  linarith [hbound, hQsum]

private theorem c_weak_converse {γ : Type} [Fintype γ] [DecidableEq γ]
    {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w)
    (hsum : ∑ g, ∑ w, J g w = 1) {bound : ℝ} (hI : mutualInfo J ≤ bound) :
    entropy (sndMarginal J)
      ≤ bound + shannon (correctProb J) + shannon (errorProb J)
        + errorProb J * Real.log (Fintype.card γ) := by
  have hfano := c_fano hnn hsum
  have hsplit := c_mi_eq_sub_cond hnn
  linarith

/-- Repeated use of a memoryless channel, and what a decoder can recover. -/
theorem solution (α β γ : Type) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] :
    -- the independence bound on words
    (∀ (n : ℕ) (law : (Fin n → β) → ℝ), (∀ w, 0 ≤ law w) → (∑ w, law w = 1) →
        entropy law ≤ ∑ i : Fin n, entropy (coordMarginal law i))
    -- memorylessness: entropy is additive across coordinates
    ∧ (∀ (n : ℕ) (rows : Fin n → β → ℝ), (∀ i b, 0 ≤ rows i b) →
        (∀ i, ∑ b, rows i b = 1) →
        entropy (productLaw rows) = ∑ i : Fin n, entropy (rows i))
    -- the n-use bound, for an arbitrary and possibly correlated input prior
    ∧ (∀ (n : ℕ) (prior : (Fin n → α) → ℝ) (K : α → β → ℝ),
        (∀ x, 0 ≤ prior x) → (∑ x, prior x = 1) → (∀ a b, 0 ≤ K a b) →
        (∀ a, ∑ b, K a b = 1) →
        mutualInfo (channelJoint prior K)
          ≤ ∑ i : Fin n,
              (entropy (coordMarginal (sndMarginal (channelJoint prior K)) i)
                - ∑ a : α, coordMarginal prior i a * entropy (K a)))
    -- Fano's inequality
    ∧ (∀ J : γ → γ → ℝ, (∀ g w, 0 ≤ J g w) → (∑ g, ∑ w, J g w = 1) →
        condEntropy J
          ≤ shannon (correctProb J) + shannon (errorProb J)
            + errorProb J * Real.log (Fintype.card γ))
    -- and the weak converse it supports
    ∧ (∀ (J : γ → γ → ℝ) (bound : ℝ), (∀ g w, 0 ≤ J g w) →
        (∑ g, ∑ w, J g w = 1) → mutualInfo J ≤ bound →
        entropy (sndMarginal J)
          ≤ bound + shannon (correctProb J) + shannon (errorProb J)
            + errorProb J * Real.log (Fintype.card γ)) := by
  refine ⟨c_indep_bound, c_entropy_productLaw, ?_, ?_, ?_⟩
  · intro n prior K hpn hps hKn hK
    exact c_nuse prior K hpn hps hKn hK
  · intro J hnn hsum
    exact c_fano hnn hsum
  · intro J bound hnn hsum hI
    exact c_weak_converse hnn hsum hI

#print axioms solution
