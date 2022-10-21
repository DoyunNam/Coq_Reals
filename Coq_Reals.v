From mathcomp Require Import all_ssreflect.

Require Import QArith.


(* ----------------------------------------------------------- *)
(*                      Logic Lemma starts                     *)
(* ----------------------------------------------------------- *)


Axiom excluded_middle :
forall P : Prop, P \/ not P.

Lemma and_or_distr (A B C : Prop) :
(A /\ B) \/ C <-> (A \/ C) /\ (B \/ C).
Proof.
split.
{ intros [[H1 H2] | H3].
  { split. { left. apply H1. } { left. apply H2. } }
  { split. { right. apply H3. } { right. apply H3. } } }
{ intros [[H1 | H2] [H3 | H4]].
  { left. split. apply H1. apply H3. }
  { right. apply H4. }
  { right. apply H2. }
  { right. apply H2. } }
Qed.

Lemma or_and_distr (A B C : Prop) :
(A \/ B) /\ C <-> (A /\ C) \/ (B /\ C).
Proof.
split.
{ intros [[H1 | H2] H3].
  { left. split. apply H1. apply H3. }
  { right. split. apply H2. apply H3. } }
{ intros [[H1 H3] | [H2 H3]].
  { split. { left. apply H1. } { apply H3. } }
  { split. { right. apply H2. } { apply H3. } } }  
Qed.

Lemma and_comm (P Q : Prop) :
P /\ Q <-> Q /\ P.
Proof.
split.
{ intros. split; apply H. }
{ intros. split; apply H. }
Qed.

Lemma or_trans (A : Prop) (B : Prop) (C : Prop) :
(A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
split.
{ intros [[H1 | H2] | H3].
  { left. exact H1. } { right. left. exact H2. }  
  { right. right. exact H3. } }
{ intros [H1 | [H2 | H3]].
  { left. left. exact H1. } { left. right. exact H2. }
  { right. exact H3. } }
Qed.

Lemma contrapositive (P Q : Prop) :
(P -> Q) -> (not Q -> not P).
Proof.
unfold not. intros.
apply H0. apply H. exact H1.
Qed.

Lemma imply_not_or (P Q : Prop) :
(P -> Q) <-> (not P \/ Q).
Proof.
split.
{ intros. specialize (excluded_middle P) as HP.
  destruct HP. { right. exact (H H0). } { left. exact H0. } }
{ unfold not. intros. destruct H; last first. { exact H. }
  { apply H in H0. contradiction. } }
Qed.

Lemma not_not_equiv (P : Prop) :
P <-> (not (not P)).
Proof.
split.
{ unfold not. intros. apply H0 in H. exact H. }
{ unfold not. intros.
  specialize (excluded_middle P) as HP. destruct HP.
  { exact H0. } { apply H in H0. contradiction. } }
Qed.

Lemma all_prop (S : Set) (P : S -> Prop) :
(forall x : S, (P x)) <-> not (exists x : S, not (P x)).
Proof.
split.
{ unfold not. intros. destruct H0 as [x Hx].
  apply Hx. apply H. }
{ unfold not. intros.
  specialize (excluded_middle (P x)) as Hx.
  destruct Hx. { exact H0. }
  { destruct H. exists x. exact H0. } }
Qed.

Lemma not_all_prop (S : Set) (P : S -> Prop) :
not (forall x : S, (P x)) <-> exists x : S, not (P x).
Proof.
rewrite all_prop. symmetry. apply not_not_equiv.
Qed.

Lemma not_exists_prop (S : Set) (P : S -> Prop) :
not (exists x : S, (P x)) <-> forall x : S, not (P x).
Proof.
symmetry. rewrite all_prop.
setoid_rewrite <- not_not_equiv. reflexivity.
Qed.

Lemma not_imply_equiv (P Q : Prop) :
not (P -> Q) <-> not (not P \/ Q).
Proof.
rewrite imply_not_or. reflexivity.
Qed.

Lemma not_or (P Q : Prop) :
not (P \/ Q) <-> not P /\ not Q.
Proof.
split.
{ unfold not. intros. split.
  { intros. apply H. left. exact H0. }
  { intros. apply H. right. exact H0. } }
{ unfold not. intros. destruct H. destruct H0.
  { exact (H H0). } { exact (H1 H0). } }
Qed.

Lemma equiv_not_equiv1 (P Q : Prop) :
(P <-> Q) -> (not P <-> not Q).
Proof.
intros. rewrite H. reflexivity.
Qed.

Lemma equiv_not_equiv2 (P Q : Prop) :
(not P <-> not Q) -> (P <-> Q).
Proof.
intros. apply equiv_not_equiv1 in H.
rewrite <- !not_not_equiv in H. exact H.
Qed.

Lemma equiv_not_equiv (P Q : Prop) :
(P <-> Q) <-> (not P <-> not Q).
Proof.
split. { apply equiv_not_equiv1. }
{ apply equiv_not_equiv2. }
Qed.

Lemma not_and (P Q : Prop) :
not (P /\ Q) <-> not P \/ not Q.
Proof.
rewrite equiv_not_equiv. rewrite not_or.
rewrite <- !not_not_equiv. reflexivity.
Qed.

Lemma all_or_pro_distr (S : Set) (P Q : S -> Prop) :
(forall x : S, (P x \/ Q x)) ->
(forall x : S, P x) \/ (exists x : S, Q x).
Proof.
intros.
specialize (excluded_middle (exists x : S, Q x)) as H1.
destruct H1. { right. exact H0. }
{ rewrite not_exists_prop in H0. left. intros.
  specialize (H0 x) as H1. destruct (H x) as [H2|H2].
  { exact H2. } { unfold not in H1. apply H1 in H2. contradiction. } }
Qed.



(* ----------------------------------------------------------- *)
(*                      Other Lemma starts                     *)
(* ----------------------------------------------------------- *)



Lemma Zlt_le_0 (n : Z) :
(0 < n)%Z -> (0 <= n)%Z.
Proof.
intros. apply Zlt_le_succ in H. simpl in H.
assert (H0 : 0 <= 1). { by []. }
apply Z.le_trans with 1%Z. exact H0. exact H.
Qed.

Lemma Qlt_le (a b : Q) :
a < b -> a <= b.
Proof.
destruct a, b. unfold Qle, Qlt. simpl. intros.
apply Zplus_le_reg_r with (- (Qnum * Z.pos Qden0))%Z.
rewrite Z.add_opp_diag_r. apply Zlt_le_0.
assert (H1 : (Qnum * Z.pos Qden0 +
             (- (Qnum * Z.pos Qden0)) = 0)%Z).
{ rewrite Z.add_opp_diag_r. reflexivity. }
rewrite -H1. apply Zplus_lt_compat_r. exact H.
Qed.

Lemma Qlt_plus_transpose (a b c : Q) :
a - b < c <-> a < b + c.
Proof.
assert (H : a - b < c <-> (a + (-b)) + b < c + b).
{ symmetry. apply Qplus_lt_l with (x := a-b) (y := c) (z := b). }
  rewrite <- Qplus_assoc in H.
  rewrite [(-b) + _]Qplus_comm in H.
  rewrite Qplus_opp_r in H. rewrite Qplus_0_r in H.
  rewrite H. rewrite Qplus_comm. reflexivity.
Qed.

Lemma Zlt_0_lt (n m : Z) :
(n < m)%Z -> (0 < (m - n))%Z.
Proof.
assert (H : (0 = n - n)%Z). { ring. }
rewrite H. apply Zplus_lt_compat_r.
Qed.

Lemma Qnum_eq (a b : Z) (c : positive) :
a = b -> a # c == b # c.
Proof.
intros. unfold Qeq. simpl. rewrite H. reflexivity.
Qed.

Lemma reduce_den (a b c : Z) (d : positive) :
(a - b <= c)%Z -> (a # d) - (b # d) <= (c # d).
Proof.
intros.
unfold Qminus. unfold Qplus. simpl.
unfold Qle. simpl.
rewrite Z.mul_add_distr_r.
assert (H0 : (Z.pos d * Z.pos d = Z.pos (d*d))%Z ).
{ symmetry. apply Pos2Z.inj_mul. }
rewrite Zmult_assoc_reverse. rewrite Zmult_assoc_reverse.
rewrite H0. rewrite <- Z.mul_add_distr_r.
apply Zmult_le_compat_r. exact H. by [].
Qed.

Lemma Q_midpoint_lt (x : Q) (y : Q) :
x < y -> x < x + (y-x)/2 /\ x + (y-x)/2 < y.
Proof.
intros.
assert (H0 : 0 < y - x).
{ rewrite Qlt_minus_iff in H. exact H. }
assert (H1 : 0 < 1/2). { apply Qinv_lt_0_compat. by []. }
assert (H2 : 1/2 < 1). { by []. }
split.
{ setoid_rewrite <- Qplus_0_r at 1. rewrite Qplus_lt_r.
  apply Qmult_lt_0_compat. exact H0. exact H2. }
{ apply Qplus_lt_r with (-x). rewrite Qplus_assoc.
  rewrite [-x + x]Qplus_comm. rewrite Qplus_opp_r.
  rewrite Qplus_0_l. rewrite [-x + y]Qplus_comm.
  setoid_rewrite <- Qmult_1_r at 6.
  apply Qmult_le_lt_compat_pos.
  { split. exact H0. apply Qle_refl. }
  { split. exact H1. exact H2. } }
Qed.

Lemma Qtrichotomy (p : Q) (q : Q) :
(p < q) \/ (p == q) \/ (q < p).
Proof.
unfold Qlt. unfold Qeq.
exact (Z.lt_trichotomy (Qnum p * QDen q)%Z
       (Qnum q * QDen p)%Z).
Qed.

Lemma Qnot_le_equiv (x : Q) (y : Q) :
not (x <= y) <-> x > y.
Proof.
split. apply Qnot_le_lt. apply Qlt_not_le.
Qed.

Lemma Zlt_or_eq_equiv (n : Z) (m : Z) :
(n < m)%Z \/ (n = m)%Z <-> (n <= m)%Z.
Proof.
assert (H : (n = m)%Z = (inject_Z n == inject_Z m)).
{ unfold inject_Z. unfold Qeq. simpl.
  rewrite Z.mul_comm. rewrite Z.mul_1_l.
  rewrite Z.mul_comm. rewrite Z.mul_1_l. reflexivity. }
rewrite Zle_Qle. rewrite Zlt_Qlt. rewrite H.
rewrite Qle_lteq. reflexivity.
Qed.


Lemma Qle_or_not_le (x : Q) (y : Q) :
x <= y \/ not (x <= y).
Proof.
rewrite Qnot_le_equiv. unfold Qle. unfold Qlt.
rewrite -Zlt_or_eq_equiv. rewrite or_trans.
setoid_rewrite <- Z.gt_lt_iff at 2.
apply Ztrichotomy.
Qed.

Lemma Qminus_1_lt (q : Q) : q - 1 < q.
Proof.
apply Qlt_minus_iff. rewrite Qopp_plus. rewrite Qopp_opp.
rewrite Qplus_assoc. rewrite Qplus_opp_r. rewrite Qplus_0_l.
by [].
Qed.

Lemma Qplus_1_lt (q : Q) : q < q + 1.
Proof.
apply Qlt_minus_iff. rewrite [q + 1]Qplus_comm.
rewrite -Qplus_assoc. rewrite Qplus_opp_r.
rewrite Qplus_0_r. by [].
Qed.

(* every two elements a, b of X are equal or not equal. *)
Lemma ele_X_comp :
forall X : Set, forall a b : X, not (a = b) \/ (a = b).
Proof.
intros. apply or_comm. apply excluded_middle.
Qed.

Lemma functions_eq_or_not :
forall f g : (Q -> bool),
(forall q : Q, f q = g q) \/ (exists q : Q, f q <> g q).
Proof.
intros.
rewrite all_prop. apply or_comm. apply excluded_middle.
Qed.

Lemma Qle_bool_false (x y : Q) :
Qle_bool x y = false <-> y < x.
Proof.
split.
{ destruct (Qlt_le_dec y x) as [H|H]. { intros. exact H. }
  { rewrite -Qle_bool_iff in H. intros.
    rewrite H0 in H. discriminate H. } }
{ intros. rewrite Qgt_alt in H. unfold Qcompare in H.
  unfold Qle_bool. unfold Zle_bool. rewrite H.
  reflexivity. }
Qed.

(* 1 # n is equal to 1/n *)
Lemma Archimedean :
forall q : Q, 0 < q ->
exists n : positive, 1 # n < q.
Proof.
intros. destruct q. exists (Qden + 1)%positive. unfold Qlt. simpl.
specialize (Zgt_succ (Z.pos Qden)) as H0. simpl in H0.
apply Z.gt_lt in H0. setoid_rewrite <- Zmult_1_l at 1.
apply Zmult_lt_compat2.
{ assert (H1 : (0 < Qnum)%Z).
  { unfold Qlt in H. simpl in H. rewrite Zmult_1_r in H. exact H. }
  specialize (Zlt_le_succ _ _ H1) as H2. simpl in H2.
  split. by []. exact H2. }
{ split. by []. exact H0. }
Qed.

Lemma minus_cancel (a b c d e : Q) :
a <= b + (-c) -> d <= e + (-b) -> a + d <= e + (-c).
Proof.
intros.
specialize (Qplus_le_compat a (b + -c) d (e + -b) H H0) as H1.
assert (H2 : b + (-c) + (e + -b) == e + -c).
{ rewrite Qplus_comm. rewrite Qplus_assoc.
  rewrite -[_ + -b + b]Qplus_assoc. rewrite [-b + _]Qplus_comm.
  rewrite Qplus_opp_r. rewrite Qplus_0_r. reflexivity. }
rewrite H2 in H1. exact H1.
Qed.

Lemma Pos_max_two (a b : positive) : 
exists x : positive, (a <= x /\ b <= x)%positive.
Proof.
exists (Pos.max a b). split.
apply Pos.le_max_l. apply Pos.le_max_r.
Qed.

Lemma Pos_max_three (a b c : positive) : 
exists x : positive, (a <= x /\ b <= x /\ c <= x)%positive.
Proof.
exists (Pos.max (Pos.max a b) c). repeat split.
{ apply Pos.le_trans with (Pos.max a b)%positive.
  apply Pos.le_max_l. apply Pos.le_max_l. }
{ apply Pos.le_trans with (Pos.max a b)%positive.
  apply Pos.le_max_r. apply Pos.le_max_l. }
{ apply Pos.le_max_r. }
Qed.

Lemma Pos_max_four (a b c d : positive) :
exists x : positive, (a <= x /\ b <= x /\ c <= x /\ d <= x)%positive.
Proof.
exists (Pos.max (Pos.max a b) (Pos.max c d)). repeat split.
{ apply Pos.le_trans with (Pos.max a b)%positive.
  apply Pos.le_max_l. apply Pos.le_max_l. }
{ apply Pos.le_trans with (Pos.max a b)%positive.
  apply Pos.le_max_r. apply Pos.le_max_l. }
{ apply Pos.le_trans with (Pos.max c d)%positive.
  apply Pos.le_max_l. apply Pos.le_max_r. }
{ apply Pos.le_trans with (Pos.max c d)%positive.
  apply Pos.le_max_r. apply Pos.le_max_r. }
Qed.

Lemma Pos_max_six (a b c d e f : positive) : 
exists x : positive, (a <= x /\ b <= x /\ c <= x 
/\ d <= x /\ e <= x /\ f <= x)%positive.
Proof.
destruct (Pos_max_three a b c) as [y [H1 [H2 H3]]].
destruct (Pos_max_three d e f) as [z [H4 [H5 H6]]].
destruct (Pos_max_two y z) as [w [H7 H8]].
exists w. repeat split.
{ exact (Pos.le_trans _ _ _ H1 H7). }
{ exact (Pos.le_trans _ _ _ H2 H7). }
{ exact (Pos.le_trans _ _ _ H3 H7). }
{ exact (Pos.le_trans _ _ _ H4 H8). }
{ exact (Pos.le_trans _ _ _ H5 H8). }
{ exact (Pos.le_trans _ _ _ H6 H8). }
Qed.

Lemma Pos_max_le_l (a b c : positive) :
(Pos.max a b <= c -> a <= c)%positive.
Proof.
intros.
apply Pos.le_trans with (Pos.max a b)%positive.
apply Pos.le_max_l. exact H.
Qed.

Lemma Pos_max_le_r (a b c : positive) :
(Pos.max a b <= c -> b <= c)%positive.
Proof.
intros.
apply Pos.le_trans with (Pos.max a b)%positive.
apply Pos.le_max_r. exact H.
Qed.

Lemma Pos_le_trans_four (a b c d : positive) : 
(a <= b)%positive -> (b <= c)%positive -> 
(c <= d)%positive -> (a <= d)%positive.
Proof.
intros. apply Pos.le_trans with b%positive. exact H.
exact (Pos.le_trans _ _ _ H0 H1).
Qed.

Lemma Q_le_trans_four (a b c d : Q) : 
a <= b -> b <= c -> c <= d -> a <= d.
Proof. 
intros. apply Qle_trans with b. exact H.
exact (Qle_trans _ _ _ H0 H1).
Qed.

Lemma Pos_inv_le_Q : 
forall q : Q, (0 < q)%Q -> exists m : positive, (1 # m <= q)%Q.
Proof.
intros. destruct q. exists (Qden)%positive. unfold Qle. simpl.
setoid_rewrite <- Z.mul_1_l at 1. apply Z.mul_le_mono_nonneg_r. { by []. } 
{ unfold Qlt in H. simpl in H. rewrite Z.mul_1_r in H.
  rewrite -Z.lt_pred_le. simpl. exact H. }
Qed.

Lemma Pos_inv_lt_Q : 
forall q : Q, (0 < q)%Q -> exists m : positive, (1 # m < q)%Q.
Proof.
intros. destruct q. unfold Qlt in H. simpl in H. rewrite Zmult_1_r in H.
assert (H1 : (0 < Qnum # (2 * Qden) < Qnum # Qden)%Q ). split.
{ unfold Qlt. simpl. rewrite Zmult_1_r. exact H. }
{ unfold Qlt. rewrite Pos2Z.inj_mul. rewrite Zmult_assoc. simpl.
  apply Z.mul_lt_mono_pos_r. { by []. }
  { setoid_rewrite <- Zmult_1_r at 1. apply Z.mul_lt_mono_pos_l.
    { exact H. } { by []. } } }
destruct H1 as [H1 H2].
destruct (Pos_inv_le_Q _ H1) as [s Hs].
exists s. exact (Qle_lt_trans _ _ _ Hs H2).
Qed.

Lemma Qinv_le_imply : 
forall a b : Q, (0 < a -> 0 < b -> a <= b -> / b <= / a)%Q.
Proof.
destruct a as [na da], b as [nb db]. unfold Qlt, Qle. simpl. 
rewrite !Zmult_1_r. intros. 
assert (H2 : exists p : positive, na = Z.pos p).
{ apply Z2Pos.id in H. exists (Z.to_pos na). symmetry. exact H. }
assert (H3 : exists q : positive, nb = Z.pos q).
{ apply Z2Pos.id in H0. exists (Z.to_pos nb). symmetry. exact H0. }
destruct H2 as [pa H4], H3 as [pb H5]. unfold Qinv. simpl.
rewrite H4. rewrite H5. simpl. rewrite !Pos2Z.inj_mul.
rewrite H4 in H1. rewrite H5 in H1. 
rewrite Zmult_comm. setoid_rewrite Zmult_comm at 2. exact H1.
Qed.

Lemma Qinv_minus (a b : Q) : 
(0 < a -> 0 < b -> / a - / b == (b - a) / (a * b))%Q.
Proof.
destruct a as [na da], b as [nb db]. unfold Qlt. simpl. 
rewrite !Zmult_1_r. intros.
assert (H1 : exists p : positive, na = Z.pos p).
{ apply Z2Pos.id in H. exists (Z.to_pos na). symmetry. exact H. }
assert (H2 : exists q : positive, nb = Z.pos q).
{ apply Z2Pos.id in H0. exists (Z.to_pos nb). symmetry. exact H0. }
destruct H1 as [pa Ha], H2 as [pb Hb].
unfold Qmult. simpl.
assert (H1 : (na * nb = Z.pos(pa * pb))%Z).
{ rewrite Ha. rewrite Hb. symmetry. apply Pos2Z.inj_mul. }
unfold Qdiv. unfold Qinv. 
rewrite H1. rewrite Ha. rewrite Hb. simpl. 
unfold Qminus. unfold Qplus. simpl. 
unfold Qeq. simpl. rewrite !Pos2Z.inj_mul. 
rewrite Pos.mul_comm. setoid_rewrite Pos.mul_comm at 2. ring.
Qed.

Lemma Qmult_lt_le_compat : 
forall x y z t : Q, (0 <= x < y -> 0 < z <= t -> x * z < y * t)%Q.
Proof.
intros. destruct H, H0. rewrite Qlt_minus_iff.
rewrite Qlt_minus_iff in H1. rewrite Qle_minus_iff in H2.
assert (H3 : ( y * t + - (x * z)  == x * (t + - z) + z * (y + - x)
               + (y + - x) * (t + - z) )%Q). { ring. } rewrite H3.
specialize (Qmult_le_0_compat _ _ H H2) as J1.
specialize (Qmult_lt_0_compat _ _ H0 H1) as J2.
apply Qlt_le in H1.
specialize (Qmult_le_0_compat _ _ H1 H2) as J3.
specialize (Qplus_lt_le_compat _ _ _ _ J2 J3) as J4.
rewrite Qplus_0_r in J4.
specialize (Qplus_lt_le_compat _ _ _ _ J4 J1) as J5.
rewrite Qplus_0_r in J5. 
assert (H4 : ( z * (y + - x) + (y + - x) * (t + - z) + x * (t + - z)
           == x * (t + - z) + z * (y + - x) + (y + - x) * (t + - z) )%Q ).
{ ring. } rewrite -H4. exact J5.
Qed.

Lemma Qdistr1 (a b : Q) : 
(- (a * - b) == a * b)%Q.
Proof.
ring.
Qed.

Lemma Qdistr2 (a b c : Q) : 
(- (a * - (b + c)) == a * b + a * c)%Q.
Proof.
ring.
Qed.

Lemma Qinv_opp (q : Q) : 
(/ - q == - / q)%Q.
Proof.
{ intros. destruct q. unfold Qopp, Qinv, Qeq. simpl.
  induction Qnum. { simpl. by []. } { simpl. by []. } { simpl. by []. } }
Qed.

Lemma Iseq_prod_sum {f1 f2 f3 f4 g1 g2 g3 g4 : positive -> Q} : 
( exists m : positive, forall n : positive, (m <= n)%positive ->
  f1 n * f2 n <= g1 n * g2 n ) -> 
( exists m : positive, forall n : positive, (m <= n)%positive ->
  f3 n * f4 n <= g3 n * g4 n ) -> 
( exists m : positive, forall n : positive, (m <= n)%positive ->
  f1 n * f2 n + f3 n * f4 n <= g1 n * g2 n + g3 n * g4 n ).
Proof.
  intros. destruct H as [s Hs], H0 as [t Ht].
  destruct (Pos_max_two s t) as [x [H1 H2]].
  exists x. intros.
  specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H3.
  specialize (Ht _ (Pos.le_trans _ _ _ H2 H)) as H4.
  exact (Qplus_le_compat _ _ _ _ H3 H4).
Qed.

Lemma Iseq_prod_sum1 {f1 f2 f3 g1 g2 g3 g4 : positive -> Q} : 
( exists m : positive, forall n : positive, (m <= n)%positive ->
  f1 n * f2 n <= g1 n * g2 n ) -> 
( exists m : positive, forall n : positive, (m <= n)%positive ->
  f3 n <= g3 n * g4 n ) -> 
( exists m : positive, forall n : positive, (m <= n)%positive ->
  f1 n * f2 n + f3 n <= g1 n * g2 n + g3 n * g4 n ).
Proof.
  intros. destruct H as [s Hs], H0 as [t Ht].
  destruct (Pos_max_two s t) as [x [H1 H2]].
  exists x. intros.
  specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H3.
  specialize (Ht _ (Pos.le_trans _ _ _ H2 H)) as H4.
  exact (Qplus_le_compat _ _ _ _ H3 H4).
Qed.

Lemma Iseq_prod_sum2 {f1 f2 f3 f4 g1 g2 g3 : positive -> Q} : 
( exists m : positive, forall n : positive, (m <= n)%positive ->
  f1 n * f2 n <= g1 n * g2 n ) -> 
( exists m : positive, forall n : positive, (m <= n)%positive ->
  f3 n * f4 n <= g3 n ) -> 
( exists m : positive, forall n : positive, (m <= n)%positive ->
  f1 n * f2 n + f3 n * f4 n<= g1 n * g2 n + g3 n ).
Proof.
  intros. destruct H as [s Hs], H0 as [t Ht].
  destruct (Pos_max_two s t) as [x [H1 H2]].
  exists x. intros.
  specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H3.
  specialize (Ht _ (Pos.le_trans _ _ _ H2 H)) as H4.
  exact (Qplus_le_compat _ _ _ _ H3 H4).
Qed.


(* ----------------------------------------------------------- *)
(*      Define a binary relation and related properties.       *)
(* ----------------------------------------------------------- *)



Definition relation (X : Set) :=
X -> X -> Prop.



Definition reflexive {X : Set} (R : relation X) :=
forall a : X, (R a a).

Definition irreflexive {X : Set} (R : relation X) :=
forall a : X, not (R a a).

Definition symmetric {X : Set} (R : relation X) :=
forall a b : X, (R a b) -> (R b a).

Definition antisymmetric {X : Set} (R : relation X) :=
forall a b : X, (R a b) -> (R b a) -> a = b.

Definition asymmetric {X : Set} (R : relation X) :=
forall a b : X, (R a b) -> not (R b a).

Definition transitive {X : Set} (R : relation X) :=
forall a b c : X, (R a b) -> (R b c) -> (R a c).



Definition strict_order {X : Set} (R : relation X) :=
(irreflexive R) /\ (asymmetric R) /\ (transitive R).

Definition equivalence {X : Set} (R : relation X) :=
(reflexive R) /\ (symmetric R) /\ (transitive R).

Definition compatible_eq_lt {X : Set} (Xlt Xeq : relation X) :=
forall w x y z : X, (Xeq w x) -> (Xeq y z) -> (Xlt w y) -> (Xlt x z).

Definition total_order {X : Set} (Xlt Xeq : relation X) :=
forall x y : X, (Xlt x y) \/ (Xeq x y) \/ (Xlt y x).

Definition without_endpoints {X : Set} (Xlt : relation X) :=
forall x : X, (exists y, Xlt y x) /\ (exists z, Xlt x z).

Definition dense {X : Set} (Xlt : relation X) :=
forall x y : X, (Xlt x y) ->
exists z : X, (Xlt x z) /\ (Xlt z y).







(* ----------------------------------------------------------- *)
(*   Define a dense linearly ordered set without endpoints.    *)
(* ----------------------------------------------------------- *)



Record dlos := mkdlos {
  X : Set;
  Xlt : relation X;
  Xeq : relation X;
  eq : equivalence Xeq;
  st : strict_order Xlt;
  cp : compatible_eq_lt Xlt Xeq;
  to : total_order Xlt Xeq;
  den : dense Xlt;
  we : without_endpoints Xlt;
}.

Axiom function :
forall S : dlos, forall f : (X S) -> bool,
forall p q : X S, (Xeq S) p q -> f p = f q.

Lemma Xlt_not (S : dlos) (x y : X S) :
Xlt S x y -> not (Xlt S y x \/ Xeq S y x).
Proof.
unfold not. intros. destruct H0.
{ assert (H1 : asymmetric (Xlt S)). { apply (st S). }
  apply H1 in H0. unfold not in H0. apply H0 in H. exact H. }
{ assert (H1 : reflexive (Xeq S)). { apply (eq S). }
  specialize (H1 x) as Hx.
  specialize ((cp S) x x y x Hx H0 H) as H2.
  assert (H3 : irreflexive (Xlt S)). { apply (st S). }
  apply H3 in H2. exact H2. }
Qed.



(* ----------------------------------------------------------- *)
(*    Q is a dense linearly ordered set without endpoints.     *)
(* ----------------------------------------------------------- *)


Example Q_equivalence :
equivalence Qeq.
Proof.
unfold equivalence. split; [|split].
{ by []. } { by []. }
{ unfold transitive. apply Qeq_trans. }
Qed.

Example Q_strict_order :
strict_order Qlt.
Proof.
unfold strict_order. split; [|split].
{ unfold irreflexive. apply Qlt_irrefl. }
{ unfold asymmetric. unfold not. intros.
  specialize (Qlt_trans _ _ _ H H0) as H1.
  apply Qlt_irrefl in H1. exact H1. }
{ unfold transitive. apply Qlt_trans. }
Qed.

Example Q_compatible_eq_lt :
compatible_eq_lt Qlt Qeq.
Proof.
unfold compatible_eq_lt. intros.
rewrite -H -H0. exact H1.
Qed.

Example Q_total_order :
total_order Qlt Qeq.
Proof.
unfold total_order. intros.
destruct (Q_dec x y) as [[H|H]|H].
{ left. exact H. }
{ right. right. exact H. }
{ right. left. exact H. }
Qed.

Example Q_dense :
dense Qlt.
Proof.
unfold dense. intros.
exists (x + (y-x)/2).
apply Q_midpoint_lt. exact H.
Qed.

Example Q_without_endpoints :
without_endpoints Qlt.
Proof.
unfold without_endpoints. intros. split.
{ exists (x-1). apply Qminus_1_lt. }
{ exists (x+1). apply Qplus_1_lt. }
Qed.

Definition Q_dlos :=
{|
  X := Q;
  Xlt := Qlt;
  Xeq := Qeq;
  eq := Q_equivalence;
  st := Q_strict_order;
  cp := Q_compatible_eq_lt;
  to := Q_total_order;
  den := Q_dense;
  we := Q_without_endpoints
|}.



(* ----------------------------------------------------------- *)
(*    Define a comparable partition and related properties     *)
(* ----------------------------------------------------------- *)



Definition mono_inc {S : dlos} (f : (X S) -> bool) :=
forall p q : X S, (Xlt S) p q ->
(f p = false /\ f q = false) \/
(f p = false /\ f q = true) \/
(f p = true  /\ f q = true).

Definition not_const {S : dlos} (f : (X S) -> bool) :=
(exists p : X S, (f p) = false) /\
(exists q : X S, (f q) = true).

Definition comparable_partition {S : dlos} (f : (X S) -> bool) :=
(mono_inc f) /\ (not_const f).



Definition not_havemax {S : dlos} (f : (X S) -> bool) :=
forall p : X S, (f p) = false
-> (exists q : X S, (Xlt S) p q /\ (f q) = false).

Definition havemax {S : dlos} (f : (X S) -> bool) :=
(exists x : X S,
 f x = false /\ (forall y : X S, (Xlt S) x y -> f y = true)).

Definition not_havemin {S : dlos} (f : (X S) -> bool) :=
forall q : X S, (f q) = true
-> (exists p : X S, (Xlt S) p q /\ (f p) = true).

Definition havemin {S : dlos} (f : (X S) -> bool) :=
(exists y : X S,
 f y = true /\ (forall x : X S, (Xlt S) x y -> f x = false)).



Definition Dedekind_complete (S : dlos) :=
forall (f : (X S) -> bool),
(comparable_partition f) -> (havemax f) \/ (havemin f).



Definition CondR (f : (X Q_dlos) -> bool) :=
mono_inc f /\ not_const f /\ not_havemax f.



(* ----------------------------------------------------------- *)
(*                       related Lemma.                        *)
(* ----------------------------------------------------------- *)



Lemma havemax_total {S : dlos} (f : (X S) -> bool) :
havemax f <-> not (not_havemax f).
Proof.
unfold not_havemax, havemax.
rewrite not_all_prop. split.
{ intros. destruct H. exists x. rewrite not_imply_equiv.
  rewrite not_or. destruct H. split.
  { rewrite H. by []. }
  { unfold not. intros. destruct H1 as [z [H2 H3]].
    specialize (H0 z H2) as H4. rewrite H3 in H4.
    discriminate. } }
{ intros. destruct H. exists x. rewrite not_imply_equiv in H.
  rewrite not_or in H. destruct H. split.
  { apply not_not_equiv. exact H. }
  { intros. unfold not in H0.
    destruct (bool_dec (f y) true) as [Hy | Hy]. { exact Hy. }
    apply not_true_is_false in Hy. destruct H0.
    exists y. intuition. } }
Qed.

Lemma havemin_total {S : dlos} (f : (X S) -> bool) :
havemin f <-> not (not_havemin f).
Proof.
unfold havemin, not_havemin.
rewrite equiv_not_equiv. rewrite -not_not_equiv.
rewrite not_exists_prop. split.
{ intros. setoid_rewrite not_and in H.
  specialize (H q) as Hq. destruct Hq.
  { rewrite H0 in H1. contradiction. }
  { rewrite not_all_prop in H1. destruct H1.
    exists x. rewrite imply_not_or in H1.
    rewrite -not_not_equiv. rewrite imply_not_or.
    apply or_comm.
    assert (H1 : not (Xlt S x q /\ f x = true)
                 <-> not (Xlt S x q) \/ (f x = false) ).
    { rewrite not_and. setoid_rewrite not_true_iff_false.
      reflexivity. }
    rewrite -H1. apply excluded_middle. } }
{ intros. rewrite not_and. rewrite not_all_prop.
  specialize (H x) as Hx.
  destruct (bool_dec (f x) true) as [Hdec | Hdec]; last first.
  { left. exact Hdec. }
  { right. apply Hx in Hdec. destruct Hdec as [p [H1 H2]].
    exists p. unfold not. intros. apply H0 in H1.
    rewrite H1 in H2. discriminate. } }
Qed.

Lemma mono_inc' {S : dlos} (f : (X S) -> bool) :
(mono_inc f <->
forall p q : X S, (f p = false -> f q = true -> (Xlt S) p q)).
Proof.
split.
{ intros. assert (H2 : total_order (Xlt S) (Xeq S)). { apply S. }
  destruct (H2 p q) as [H3|[H3|H3]]. { exact H3. }
  { specialize (function S f _ _ H3) as H4.
    rewrite H0 H1 in H4. discriminate. }
  { apply H in H3. destruct H3 as [[J1 J2]|[[J1 J2]|[J1 J2]]].
    { rewrite J1 in H1. discriminate. }
    { rewrite J2 in H0. discriminate. }
    { rewrite J2 in H0. discriminate. } } }
{ unfold mono_inc. intros.
  destruct (bool_dec (f p) true) as [Hp | Hp].
  { destruct (bool_dec (f q) true) as [Hq | Hq].
    { right. right. intuition. }
    { apply not_true_is_false in Hq.
      specialize (H q p Hq Hp) as Hqp.
      assert (H1 : asymmetric (Xlt S)). { apply (st S). }
      specialize (H1 _ _ Hqp) as H2. unfold not in H2.
      apply H2 in H0. contradiction. } }
  { apply not_true_is_false in Hp.
    destruct (bool_dec (f q) true) as [Hq | Hq].
    { right. left. intuition. }
    { apply not_true_is_false in Hq. left. intuition. } } }
Qed.

Lemma less_part {S : dlos} (f : (X S) -> bool) (p q : X S) :
mono_inc f -> (Xlt S) p q -> f q = false -> f p = false.
Proof.
intros. apply H in H0.
destruct H0 as [[J1 J2]|[[J1 J2]|[J1 J2]]].
{ exact J1. } { exact J1. }
{ rewrite J2 in H1. discriminate. }
Qed.

Lemma greater_part {S : dlos} (f : (X S) -> bool) (p q : X S) :
mono_inc f -> (Xlt S) p q -> f p = true -> f q = true.
Proof.
intros. apply H in H0.
destruct H0 as [[J1 J2]|[[J1 J2]|[J1 J2]]].
{ rewrite J1 in H1. discriminate. }
{ exact J2. } { exact J2. }
Qed.

(* Classification of a comparable partition of
   a dense linearly ordered set. *)
Lemma classify_comp_part {S : dlos} (f : (X S) -> bool) :
(comparable_partition f) ->
(havemax f /\ not_havemin f) \/
(not_havemax f /\ havemin f) \/
(not_havemax f /\ not_havemin f).
Proof.
intros.
specialize (excluded_middle (havemax f)) as H1.
setoid_rewrite havemax_total in H1 at 2.
rewrite -not_not_equiv in H1.
specialize (excluded_middle (havemin f)) as H2.
setoid_rewrite havemin_total in H2 at 2.
rewrite -not_not_equiv in H2.
destruct H1.
{ destruct H2.
  { unfold havemax in H0. destruct H0 as [x [Hx H2]].
    unfold havemin in H1. destruct H1 as [y [Hy H3]].
    assert (H4 : forall p q : X S,
                 (f p = false -> f q = true -> (Xlt S) p q) ).
    { apply mono_inc'; apply H. }
    specialize (H4 _ _ Hx Hy) as H5.
    assert (H6 : dense (Xlt S)). { apply S. }
    destruct (H6 x y H5) as [z [Hxz Hzy]].
    apply H2 in Hxz. apply H3 in Hzy.
    rewrite Hxz in Hzy. discriminate. }
  { left. intuition. } }
{ destruct H2.
  { right. left. intuition. } { right; right. intuition. } }
Qed.



(* ----------------------------------------------------------- *)
(*     Define a set R and equality and strict order on R,      *)
(*     and some related theorems.                              *)
(* ----------------------------------------------------------- *)



Record R := mkReal {
  f : (X Q_dlos) -> bool;
  Cond : CondR f;
}.

Definition Req (r1 r2 : R) :=
forall q : Q, (f r1) q = (f r2) q.

(* Define strict order on R. *)
Definition Rlt (r1 r2 : R) :=
exists q : Q, (f r1) q = true /\ (f r2) q = false.



Theorem R_equivalence :
equivalence Req.
Proof.
unfold equivalence.
unfold reflexive, symmetric, transitive.
split; [| split].
{ unfold Req. intros. reflexivity. }
{ unfold Req. intros. symmetry. apply H. }
{ unfold Req. intros. rewrite H. rewrite H0. reflexivity. }
Qed.

Theorem R_strict_order :
strict_order Rlt.
Proof.
unfold strict_order.
assert (J1 : irreflexive Rlt).
{ unfold irreflexive. unfold Rlt, not. intros.
  destruct H as [q [H1 H2]].
  rewrite H1 in H2. discriminate. }
assert (J2 : transitive Rlt).
{ unfold transitive, Rlt. intros.
  destruct H as [x [H1 H2]], H0 as [y [H3 H4]].
  assert (H5 : x < y).
  { destruct a, b, c. simpl in H1, H2, H3, H4.
    apply (mono_inc' f1). apply Cond1. apply H2. exact H3. }
  exists y. split; last first. { exact H4. }
  { apply greater_part with x. apply a. apply H5. apply H1. } }
intuition. unfold asymmetric. unfold not. intros.
specialize (J2 _ _ _ H H0) as H1. apply J1 in H1. exact H1.
Qed.

Theorem R_compatible_eq_lt :
compatible_eq_lt Rlt Req.
Proof.
unfold compatible_eq_lt. unfold Req, Rlt. intros.
destruct H1 as [q [H2 H3]]. exists q. split.
{ rewrite -H. exact H2. } { rewrite -H0. exact H3. }
Qed.

Theorem R_total_order :
total_order Rlt Req.
Proof.
unfold total_order. unfold Rlt, Req. intros.
specialize (functions_eq_or_not (f x) (f y)) as [H|H].
{ right. left. exact H. }
{ destruct H as [z H].
  destruct (bool_dec (f y z) true) as [Hy|Hy].
  { rewrite Hy in H. apply not_true_is_false in H.
    right. right. exists z. intuition. }
  { apply not_true_is_false in Hy. rewrite Hy in H.
    apply not_false_is_true in H.
    left. exists z. intuition. } }
Qed.



(* ----------------------------------------------------------- *)
(*         Define an order-prserving map from Q to R           *)
(* ----------------------------------------------------------- *)



(* Qle_bool is a function of type Q -> Q -> bool,
   defined as follows :  
   Qle_bool p q = true, if p <= q.
   Qle_bool p q = false, if q < p. *)

(* Qle_bool_iff is a Lemma that states
   forall x y : Q, Qle_bool x y = true <-> x <= y *)



(* For every q in Q, the function Qle_bool q satisfies CondR. *)
Lemma CondR_Q (q : Q) :
CondR (Qle_bool q).
Proof.
unfold CondR.  
split; [| split].
{ apply mono_inc'. intros. rewrite Qle_bool_iff in H0.
  rewrite Qle_bool_false in H. apply (Qlt_le_trans _ _ _ H H0). }
{ unfold not_const. split.
  { exists (q-1). apply Qle_bool_false. apply Qminus_1_lt. }
  { exists q. apply Qle_bool_iff. apply Qle_refl. } }
{ unfold not_havemax. setoid_rewrite Qle_bool_false.
  intros. exists (p + (q-p)/2). apply Q_midpoint_lt. exact H. }
Qed.



Definition inject_Q (q : Q) : R :=
{| f := (Qle_bool q) ;
   Cond := (CondR_Q q)
|}.



Theorem inject_Q_eq (p q : Q) :
p == q -> Req (inject_Q p) (inject_Q q).
Proof.
unfold inject_Q. unfold Req. simpl. intros.
rewrite H. reflexivity.
Qed.

Theorem inject_Q_order_preserve (p q : Q) :
p < q -> Rlt (inject_Q p) (inject_Q q).
Proof.
unfold inject_Q. unfold Rlt. simpl. intros.
exists (p + (q-p)/2). split.
{ rewrite Qle_bool_iff. apply Qlt_le.
  apply Q_midpoint_lt. exact H. }
{ rewrite Qle_bool_false.
  apply Q_midpoint_lt. exact H. }
Qed.

Lemma inject_Q_order_reverse (p q : Q) :
Rlt (inject_Q p) (inject_Q q) -> p < q.
Proof.
intros.
assert (H1 : asymmetric Rlt). { apply R_strict_order. }
destruct (Q_dec p q) as [[Hdec|Hdec]|Hdec].
{ exact Hdec. }
{ apply inject_Q_order_preserve in Hdec. apply H1 in Hdec.
  unfold not in Hdec. apply Hdec in H. contradiction. }
{ unfold Rlt, inject_Q in H. simpl in H.
  destruct H as [t [H2 H3]]. rewrite Hdec in H2.
  rewrite H3 in H2. discriminate. }
Qed.

Theorem inject_Q_dense (a b : R) :
(Rlt a b) ->
exists q : Q, (Rlt a (inject_Q q)) /\ (Rlt (inject_Q q) b).
Proof.
destruct a, b. unfold Rlt. simpl.
unfold CondR in Cond1.
destruct Cond1 as [_ [_ H]].
intros. destruct H0 as [x [H0 H1]].
destruct (H x H1) as [y [H2 H3]].
exists (x + ((y-x)/2)). split.
{ exists x. split. { exact H0. }
  { rewrite Qle_bool_false.
    apply Q_midpoint_lt. exact H2. } }
{ exists y. split; last first. { exact H3. }
  { rewrite Qle_bool_iff. apply Qlt_le.
    apply Q_midpoint_lt. exact H2. } }
Qed.



(* ----------------------------------------------------------- *)
(*     R is a dense linearly ordered set without endpoints.    *)
(* ----------------------------------------------------------- *)



Theorem R_dense :
dense Rlt.
Proof.
unfold dense. intros.
specialize (inject_Q_dense x y H) as H0.
destruct H0 as [q [H1 H2]].
exists (inject_Q q).
intuition.
Qed.

Theorem R_without_endpoints :
without_endpoints Rlt.
Proof.
unfold without_endpoints. intros.
destruct x. unfold CondR in Cond0.
destruct Cond0 as [mono [nc nh]].
unfold Rlt. simpl. unfold not_const in nc.
destruct nc as [ef et].
destruct ef as [x Hx], et as [y Hy].
split.
{ exists (inject_Q x). exists x. split.
  { unfold inject_Q. simpl.
    apply Qle_bool_iff. apply Qle_refl. }
  { exact Hx. } }
{ exists (inject_Q (y+1)). exists y. split.
  { exact Hy. }
  { unfold inject_Q. simpl.
    apply Qle_bool_false. apply Qplus_1_lt. } }
Qed.



Definition R_dlos :=
{|
  X := R;
  Xlt := Rlt;
  Xeq := Req;
  eq := R_equivalence;
  st := R_strict_order;
  cp := R_compatible_eq_lt;
  to := R_total_order;
  den := R_dense;
  we := R_without_endpoints
|}.



(* ----------------------------------------------------------- *)
(*                    R is Dedekind complete.                  *)
(* ----------------------------------------------------------- *)



Theorem R_Dedekind_complete :
Dedekind_complete R_dlos.
Proof.
unfold Dedekind_complete.
unfold comparable_partition, havemax, havemin.
intro f. intros [H1 [H2 H3]].
assert (H4 : exists h : X Q_dlos -> bool,
             forall q : Q, h q = f(inject_Q q)).
{ exists (fun q : Q => f(inject_Q q)). reflexivity. }
destruct H4 as [h H4].
assert (H5 : comparable_partition h).
{ unfold CondR. repeat split.
  { rewrite mono_inc'. simpl. intros.
    destruct (Q_dec p q) as [[Hdec|Hdec]|Hdec].
    { exact Hdec. }
    { specialize (inject_Q_order_preserve q p Hdec) as H5.
      rewrite mono_inc' in H1.
      simpl in H1. rewrite H4 in H. rewrite H4 in H0.
      specialize (H1 _ _ H H0) as H6.
      assert (H7 : asymmetric Rlt). { apply R_strict_order. }
      apply H7 in H6. unfold not in H6.
      apply H6 in H5. contradiction. }
    { specialize (function Q_dlos h p q Hdec) as H5.
      rewrite H H0 in H5. discriminate. } }
  { simpl. simpl in H2. destruct H2 as [x Hx].
    assert (H5 : exists y : R, Rlt y x).
    { apply R_without_endpoints. }
    destruct H5 as [y Hyx].
    assert (H6 : exists q : Q,
                 (Rlt y (inject_Q q)) /\ (Rlt (inject_Q q) x)).
    { apply inject_Q_dense. exact Hyx. }
    destruct H6 as [q [_ Hqx]].
    exists q. rewrite H4. apply less_part with x.
    exact H1. exact Hqx. exact Hx. }
  { simpl. simpl in H3. destruct H3 as [y Hy].
    assert (H5 : exists x : R, Rlt y x).
    { apply R_without_endpoints. }
    destruct H5 as [x Hyx].
    assert (H6 : exists q : Q,
                 (Rlt y (inject_Q q)) /\ (Rlt (inject_Q q) x)).
    { apply inject_Q_dense. exact Hyx. }
    destruct H6 as [q [Hyq _]].
    exists q. rewrite H4. apply greater_part with y.
    exact H1. exact Hyq. exact Hy. } }
destruct (classify_comp_part h H5) as [[H6 H7]|[[H6 H7]|[H6 H7]]].
{ unfold havemax in H6. simpl in H6. destruct H6 as [x [Hx Hy]].
  left. exists (inject_Q x). split.
  { rewrite -H4. exact Hx. }
  { intros. specialize (inject_Q_dense _ _ H) as [z [Hxz Hzy]].
    specialize (inject_Q_order_reverse _ _ Hxz) as H8.
    apply Hy in H8. rewrite H4 in H8.
    apply greater_part with (inject_Q z).
    exact H1. exact Hzy. exact H8. } }
{ unfold havemin in H7. simpl in H7. destruct H7 as [y [Hy Hx]].
  right. exists (inject_Q y). split.
  { rewrite -H4. exact Hy. }
  { intros. specialize (inject_Q_dense _ _ H) as [z [Hxz Hzy]].
    specialize (inject_Q_order_reverse _ _ Hzy) as H8.
    apply Hx in H8. rewrite H4 in H8.
    apply less_part with (inject_Q z).
    exact H1. exact Hxz. exact H8. } }
{ assert (Hh' : CondR h).
  { unfold CondR. intuition; apply H5. }
  assert (Hh : exists r : R, r = {| f := h; Cond := Hh' |}).
  { exists {| f := h; Cond := Hh' |}. reflexivity. }
  destruct Hh as [m Hm].
  destruct (bool_dec (f m) true) as [H10|H10].
  { right. exists m. split. { exact H10. }
    { intros. specialize (inject_Q_dense _ _ H) as [p [Hxp Hpm]].
      unfold Rlt in Hpm. rewrite Hm in Hpm. simpl in Hpm.
      destruct Hpm as [q [Hpq Hq]]. rewrite Qle_bool_iff in Hpq.
      apply Qle_lt_or_eq in Hpq. destruct Hpq.
      { apply less_part with (inject_Q p).
        apply H1. exact Hxp. rewrite -H4.
        apply less_part with q.
        apply Hh'. exact H0. exact Hq. }
      { apply less_part with (inject_Q p).
        apply H1. exact Hxp. rewrite -H4.
        unfold CondR in H6. destruct H5.
        specialize (function Q_dlos h p q H0) as H11.
        rewrite H11. exact Hq. } } }
  { left. apply not_true_is_false in H10. exists m.
    split. { exact H10. }
    { intros. specialize (inject_Q_dense _ _ H) as [q [Hmq Hqy]].
      rewrite Hm in Hmq. unfold Rlt, inject_Q in Hmq. simpl in Hmq.
      destruct Hmq as [p [Hp Hqp]]. rewrite Qle_bool_false in Hqp.
      apply greater_part with (inject_Q q).
      apply H1. exact Hqy. rewrite -H4.
      apply greater_part with p. apply H5. exact Hqp. exact Hp. } } }
Qed.



(* ----------------------------------------------------------- *)
(*           Define least-upper-bound-property.                *)
(* ----------------------------------------------------------- *)



(* Define an upper bound. *)
Definition ub {S : dlos} (f : (X S) -> bool) (x : X S) :=
forall y : X S, (f y) = false -> Xlt S y x \/ Xeq S y x.

Definition haveub {S : dlos} (f : (X S) -> bool) :=
exists x : X S, (ub f x).

Definition least_upper_bound_property (S : dlos) :=
forall (f : (X S) -> bool), not_const f -> haveub f ->
exists z : X S, (ub f z) /\
(forall x : X S, (ub f x) -> Xlt S z x \/ Xeq S z x).



(* ----------------------------------------------------------- *)
(*  On dense linearly ordered set,                             *)
(*  the least-upper-bound-property implies Dedekind complete.  *)
(* ----------------------------------------------------------- *)



Theorem lubp_imply_DC :
forall S : dlos,
least_upper_bound_property S -> Dedekind_complete S.
Proof.
unfold least_upper_bound_property, Dedekind_complete. intros.
destruct H0 as [mi nc].
specialize (H f0 nc).
unfold not_const in nc. destruct nc as [[p Hp] [q Hq]].
assert (H' : forall x : X S, f0 x = true -> ub f0 x).
{ unfold ub. intros. rewrite mono_inc' in mi.
  specialize (mi _ _ H1 H0) as H2. left; exact H2. }
apply H' in Hq.
assert (H1 : haveub f0). { unfold haveub. exists q. exact Hq. }
destruct (H H1) as [z [Hz1 Hz2]]. unfold ub in Hz1.
destruct (bool_dec (f0 z) true).
{ right. unfold havemin. exists z. split. { exact e. }
  { intros. destruct (bool_dec (f0 x) true) as [H3|H3].
    { apply H' in H3. specialize (Hz2 x H3) as H4.
      apply Xlt_not in H0. unfold not in H0.
      apply H0 in H4. contradiction. }
    { apply not_true_is_false in H3. exact H3. } } }
{ apply not_true_is_false in n. left. unfold havemax.
  exists z. split. { exact n. }
  { intros. destruct (bool_dec (f0 y) true) as [H2|H2].
    { exact H2. }
    { apply not_true_is_false in H2.
      apply Hz1 in H2. apply Xlt_not in H0. unfold not in H0.
      apply H0 in H2. contradiction. } } }
Qed.

Axiom DC_imply_lubp :
forall S : dlos,
Dedekind_complete S -> least_upper_bound_property S.




(* ----------------------------------------------------------- *)
(*                     Define Nested Intervals                 *)
(* ----------------------------------------------------------- *)

Definition compare (f g : positive -> Q) := 
exists m : positive, (forall n : positive, 
(m <= n)%positive -> f n <= g n).

Definition get_closer (f g : positive -> Q) := 
forall m n : positive, (exists p : positive, 
(n <= p)%positive /\ g p - f p < 1 # m).

Definition increasing (f : positive -> Q) := 
exists m : positive, (forall n p : positive, 
(m <= n)%positive -> (n <= p)%positive -> f n <= f p).

Definition decreasing (g : positive -> Q) :=
exists m : positive, (forall n p : positive, 
(m <= n)%positive -> (n <= p)%positive -> g p <= g n).


Record I := mkI { 
  l : positive -> Q;
  r : positive -> Q; 
  comp : compare l r;
  clo : get_closer l r;
  inc : increasing l;
  dec : decreasing r;
}.

Definition Ilt (a b : I) :=
forall m : positive, (exists n : positive, 
(m <= n)%positive /\ (r a) n < (l b) n).

Definition Ieq (a b : I) :=
compare (l b) (r a) /\ compare (l a) (r b).

Lemma not_Ilt_equiv (a b : I) :
not (Ilt a b) <-> compare (l b) (r a).
Proof.
unfold Ilt, compare. rewrite not_all_prop. split.
{ intros [x Hx]. exists x. rewrite not_exists_prop in Hx. intros.
  specialize (Hx n) as H0. rewrite not_and in H0. destruct H0.
  { contradiction. } { apply Qnot_lt_le. exact H0. } }
{ intros [m Hm]. exists m. rewrite not_exists_prop. intros.
  rewrite not_and. specialize (Hm x) as H. 
  apply imply_not_or in H. destruct H. { left. exact H. }
  { right. apply Qle_not_lt. exact H. } }
Qed.

Lemma compare_ext (a : I) :
exists m : positive, (forall n p : positive, 
(m <= n)%positive -> (m <= p)%positive -> (l a) n <= (r a) p).
Proof.
destruct (inc a) as [s Hs], (dec a) as [t Ht], (comp a) as [u Hu].
destruct (Pos_max_three s t u) as [m [H1 [H2 H3]]].
exists m. intros. destruct (Pos_max_two n p) as [q [H4 H5]]. 
assert (H8 : (u <= q)%positive).
{ apply Pos.le_trans with m%positive. exact H3.
  exact (Pos.le_trans _ _ _ H0 H5). } 
specialize (Hs n q (Pos.le_trans _ _ _ H1 H) H4) as H9. 
specialize (Ht p q (Pos.le_trans _ _ _ H2 H0) H5) as H10.
specialize (Hu _ H8) as H11. apply Qle_trans with (l a q).
exact H9. exact (Qle_trans _ _ _ H11 H10).
Qed. 


Theorem I_strict_order :
strict_order Ilt.
Proof.
unfold strict_order.
unfold irreflexive, asymmetric, transitive.
unfold Ilt, not. repeat split.
{ intros. destruct (comp a) as [s Hs]. specialize (H s) as [n [H1 H2]].
  specialize (Hs n H1) as H3. apply Qlt_not_le in H2. contradiction. }
{ intros. destruct (compare_ext a) as [s Hs], (compare_ext b) as [t Ht].
  destruct (Pos_max_two s t) as [x [H1 H2]].
  destruct (H x) as [u [H3 H4]], (H0 x) as [v [H5 H6]].
  specialize (Ht u v (Pos.le_trans _ _ _ H2 H3) 
  (Pos.le_trans _ _ _ H2 H5)) as H7.
  specialize (Hs v u (Pos.le_trans _ _ _ H1 H5)
  (Pos.le_trans _ _ _ H1 H3)) as H8.
  specialize (Qlt_le_trans _ _ _ H4 H7) as H9.
  specialize (Qlt_trans _ _ _ H9 H6) as H10.
  specialize (Qlt_le_trans _ _ _ H10 H8) as H11.
  apply Qlt_irrefl in H11. contradiction. }
{ intros. destruct (dec a) as [s Hs], (inc c) as [t Ht].
  destruct (compare_ext b) as [u Hu].
  destruct (Pos_max_four m s t u) as [x [H1 [H2 [H3 H4]]]].
  destruct (H x) as [y [H5 H6]], (H0 x) as [z [H7 H8]].
  specialize (Hu y z (Pos.le_trans _ _ _ H4 H5) 
  (Pos.le_trans _ _ _ H4 H7)) as H9.
  specialize (Qlt_le_trans _ _ _ H6 H9) as H10.
  specialize (Qlt_trans _ _ _ H10 H8) as H11.
  destruct (Pos_max_two y z) as [w [H12 H13]].
  specialize (Hs y w (Pos.le_trans _ _ _ H2 H5) H12) as H16. 
  specialize (Ht z w (Pos.le_trans _ _ _ H3 H7) H13) as H17.
  specialize (Qle_lt_trans _ _ _ H16 H11) as H18.
  specialize (Qlt_le_trans _ _ _ H18 H17) as H19.
  exists w. split. { exact (Pos_le_trans_four _ _ _ _ H1 H7 H13). }
  { exact H19. } }
Qed.



Lemma Ieq_trans_half (a b c : I) :
not (Ilt a b) -> not (Ilt b c) -> not (Ilt a c).
Proof.
rewrite not_Ilt_equiv. rewrite not_Ilt_equiv.
unfold compare, not, Ilt. intros.
destruct H as [s Hs], H0 as [t Ht].
destruct (dec a) as [u Hu], (inc c) as [v Hv].
destruct (Pos_max_four s t u v) as [x [H2 [H3 [H4 H5]]]].
destruct (H1 x) as [y [H6 H7]].
rewrite Qlt_minus_iff in H7.
destruct (Archimedean _ H7) as [e He].
destruct (clo b e y) as [w [H8 H9]].
specialize (Hs w (Pos_le_trans_four _ _ _ _ H2 H6 H8)) as H10.
specialize (Ht w (Pos_le_trans_four _ _ _ _ H3 H6 H8)) as H11.
assert (H12 : r a w <= r a y).
{ apply Hu. exact (Pos.le_trans _ _ _ H4 H6). exact H8. } 
assert (H13 : l c y <= l c w).
{ apply Hv. exact (Pos.le_trans _ _ _ H5 H6). exact H8. }
specialize (Qlt_trans _ _ _ H9 He) as H14.
specialize (Qplus_le_compat _ _ _ _ H10 H11) as H15.
specialize (Qplus_le_compat _ _ _ _ H12 H13) as H16.
specialize (Qplus_le_compat _ _ _ _ H15 H16) as H17.
specialize (Qplus_lt_le_compat _ _ _ _ H14 H17) as H18.
assert (H19 : r b w - l b w + (l b w + l c w + (r a w + l c y)) 
 == l c y + - r a y + (r a w + r b w + (r a y + l c w))). { ring. }
rewrite H19 in H18. apply Qlt_irrefl in H18. contradiction.
Qed.



Theorem I_equivalence :
equivalence Ieq.
Proof.
unfold equivalence.
unfold reflexive, symmetric, transitive.
assert (Hsym : forall a b : I, Ieq a b -> Ieq b a).
{ intros. unfold Ieq. rewrite and_comm. exact H. }
split; [| split].
{ intros. unfold Ieq. assert (H : compare (l a) (r a)).
  { rewrite -not_Ilt_equiv. assert (H : irreflexive Ilt).
    { apply I_strict_order. } apply H. }
  split; apply H. }
{ apply Hsym. }
{ intros. unfold Ieq. rewrite <- !not_Ilt_equiv. split.
  { apply Ieq_trans_half with b. rewrite not_Ilt_equiv. apply H.
    rewrite not_Ilt_equiv. apply H0. }
  { apply Hsym in H. apply Hsym in H0.
    apply Ieq_trans_half with b. rewrite not_Ilt_equiv. apply H0.
    rewrite not_Ilt_equiv. apply H. } }
Qed.

Theorem I_total_order :
total_order Ilt Ieq.
Proof.
unfold total_order. intros. unfold Ieq. rewrite <- !not_Ilt_equiv.
rewrite -not_or. rewrite [_ \/ (Ilt y x)]or_comm.
rewrite -or_trans. apply excluded_middle.
Qed.

Theorem I_compatible_eq_lt :
compatible_eq_lt Ilt Ieq.
Proof.
unfold compatible_eq_lt.
intros.
destruct ((I_total_order) x z) as [H2|[H2|H2]]. { exact H2. }
{ assert (Hs : symmetric Ieq). { apply I_equivalence. }
  assert (Ht : transitive Ieq). { apply I_equivalence. }
  apply Hs in H0. specialize (Ht _ _ _ H H2) as H3.
  specialize (Ht _ _ _ H3 H0) as H4. unfold Ieq in H4.
  rewrite <- !not_Ilt_equiv in H4. destruct H4.
  unfold not in H4. apply H4 in H1. contradiction. }
{ unfold Ilt in H1, H2. unfold Ieq in H, H0. 
  destruct H as [H _], H0 as [_ H0]. unfold compare in H, H0.
  destruct H as [s Hs], H0 as [t Ht].
  destruct (dec w) as [a Ha], (inc y) as [b Hb].
  destruct (dec z) as [c Hc], (inc x) as [d Hd].
  destruct (Pos_max_six a b c d s t) as [k [H3 [H4 [H5 [H6 [H7 H8]]]]]].
  destruct (H1 k) as [e [H9 H10]], (H2 k) as [f [H11 H12]].
  destruct (Pos_max_two e f) as [j [H13 H14]].
  assert (H15 : l y e <= l y j). 
  { apply Hb. exact (Pos.le_trans _ _ _ H4 H9). intuition. }
  assert (H16 : l y j <= r z j).
  { apply Ht. exact (Pos_le_trans_four _ _ _ _ H8 H9 H13). }
  assert (H17 : r z j <= r z f).
  { apply Hc. exact (Pos.le_trans _ _ _ H5 H11). intuition. }
  assert (H18 : l x f <= l x j).
  { apply Hd. exact (Pos.le_trans _ _ _ H6 H11). intuition. }
  assert (H19 : l x j <= r w j).
  { apply Hs. exact (Pos_le_trans_four _ _ _ _ H7 H9 H13). }
  assert (H20 : r w j <= r w e).
  { apply Ha. exact (Pos.le_trans _ _ _ H3 H9). intuition. }
  specialize (Q_le_trans_four _ _ _ _ H15 H16 H17) as H21.
  specialize (Q_le_trans_four _ _ _ _ H18 H19 H20) as H22.
  specialize (Qlt_le_trans _ _ _ H10 H21) as H23.
  specialize (Qlt_le_trans _ _ _ H12 H22) as H24.
  specialize (Qlt_trans _ _ _ H23 H24) as H25.
  apply Qlt_irrefl in H25. contradiction. }
Qed.






(* ----------------------------------------------------------- *)
(*         const_I is order preserving, and dense in I         *)
(* ----------------------------------------------------------- *)



Definition const (q : Q) : positive -> Q :=
fun => q.

Lemma compare_const (q : Q) :
compare (const q) (const q).
Proof.
unfold const, compare. intros. exists (1%positive).
intros. apply Qle_refl.
Qed.

Lemma get_closer_const (q : Q) :
get_closer (const q) (const q).
Proof.
unfold const, get_closer. intros. exists n%positive. split.
{ apply Pos.le_refl. }
{ unfold Qminus. rewrite Qplus_opp_r. by []. }
Qed.

Lemma increasing_const (q : Q) : 
increasing (const q).
Proof.
unfold increasing, const. exists 1%positive. intros. apply Qle_refl.
Qed.

Lemma decreasing_const (q : Q) : 
decreasing (const q).
Proof.
unfold decreasing, const. exists 1%positive. intros. apply Qle_refl.
Qed.

Definition const_I (q : Q) : I := 
{|
  l := const q;
  r := const q;
  comp := compare_const q;
  clo := get_closer_const q;
  inc := increasing_const q;
  dec := decreasing_const q;
|}.



Theorem const_I_order_preserve (p q : Q) :
p < q -> Ilt (const_I p) (const_I q).
Proof.
unfold Ilt, const_I. simpl. unfold const. intros.
exists m%positive. split. { apply Pos.le_refl. } { exact H. }
Qed.

Theorem const_I_order_reverse (p q : Q) :
Ilt (const_I p) (const_I q) -> p < q.
Proof.
unfold Ilt, const_I, const. simpl. intros.
destruct (H 1%positive) as [_ [_ H0]]. exact H0.
Qed.

Theorem const_I_dense (a b : I) :
(Ilt a b) ->
exists q : Q, (Ilt a (const_I q)) /\ (Ilt (const_I q) b).
Proof.
unfold Ilt, const_I. simpl. unfold const. intros.
destruct (dec a) as [s Hs], (inc b) as [t Ht].
destruct (Pos_max_two s t) as [x [H1 H2]].
destruct (H x) as [y [H3 H4]].
exists ((r a y) + (((l b y) - (r a y))/2)). split.
{ intros. destruct (Pos_max_two m y) as [z [H5 H6]]. 
  exists z. split. { exact H5. }
  { apply Qle_lt_trans with (r a y).
    { apply Hs. exact (Pos.le_trans _ _ _ H1 H3). intuition. }
    { apply Q_midpoint_lt. exact H4. } } }
{ intros. destruct (Pos_max_two m y) as [z [H5 H6]].
  exists z. split. { exact H5. }
  { apply Qlt_le_trans with (l b y); first last.
    { apply Ht. exact (Pos.le_trans _ _ _ H2 H3). intuition. }
    { apply Q_midpoint_lt. exact H4. } } }
Qed.



Theorem I_dense :
dense Ilt.
Proof.
unfold dense. intros. 
specialize (const_I_dense _ _ H) as [q [H1 H2]].
exists (const_I q). intuition.
Qed.



Definition translation (t : Q) (f : positive -> Q) :=
fun q => f(q) + t.

Lemma compare_translation (t : Q) (a : I) :
compare (translation t (l a)) (translation t (r a)).
Proof.
unfold compare, translation. destruct (comp a) as [m Hm].
exists m. intros. rewrite Qplus_le_l. apply Hm. exact H.
Qed.

Lemma get_closer_translation (t : Q) (a : I) :
get_closer (translation t (l a)) (translation t (r a)).
Proof.
unfold get_closer, translation. intros.
destruct (clo a m n) as [x Hx]. exists x. split. { apply Hx. }
{ assert (H : r a x + t - (l a x + t) == r a x - l a x). { ring. }
  rewrite H. apply Hx. }
Qed.

Lemma increasing_translation (t : Q) (a : I) : 
increasing (translation t (l a)).
Proof.
unfold increasing, translation. destruct (inc a) as [m Hm]. 
exists m. intros. apply Qplus_le_l. apply Hm. exact H. exact H0.
Qed.

Lemma decreasing_translation (t : Q) (a : I) : 
decreasing (translation t (r a)).
Proof. 
unfold decreasing, translation. destruct (dec a) as [m Hm].
exists m. intros. apply Qplus_le_l. apply Hm. exact H. exact H0.
Qed.

Definition translation_I (t : Q) (a : I) : I:=
{|
  l := translation t (l a);
  r := translation t (r a);
  comp := compare_translation t a;
  clo := get_closer_translation t a;
  inc := increasing_translation t a;
  dec := decreasing_translation t a;
|}.



Lemma translation_gt (t : Q) (a : I) :
0 < t -> Ilt a (translation_I t a).
Proof.
unfold Ilt, translation_I. simpl. unfold translation. intros.
destruct (Archimedean t H) as [s Hs].
destruct (clo a s m) as [x [H1 H2]].
exists x. split. { exact H1. } 
{ specialize (Qlt_trans _ _ _ H2 Hs) as H3. 
  rewrite -Qlt_plus_transpose. exact H3. }
Qed.

Lemma translation_lt (t : Q) (a : I) :
t < 0 -> Ilt (translation_I t a) a.
Proof.
unfold Ilt, translation_I. simpl. unfold translation. intros.
apply Qlt_minus_iff in H. rewrite Qplus_0_l in H.
destruct (Archimedean (-t) H) as [s Hs].
destruct (clo a s m) as [x [H1 H2]].
exists x. split. { exact H1. }
{ specialize (Qlt_trans _ _ _ H2 Hs) as H3.
  apply Qlt_minus_iff in H3. apply Qlt_minus_iff.
  assert (H4 : l a x + - (r a x + t) == - t + - (r a x - l a x)). { ring. }
  rewrite H4. exact H3. }
Qed.

Theorem I_without_endpoints :
without_endpoints Ilt.
Proof.
unfold without_endpoints. intros. split.
{ exists (translation_I (-1) x). apply translation_lt. by []. }
{ exists (translation_I 1 x). apply translation_gt. by []. }
Qed.



(* ----------------------------------------------------------- *)
(*     I is a dense linearly ordered set without endpoints.    *)
(* ----------------------------------------------------------- *)



Definition I_dlos :=
{|
  X := I;
  Xlt := Ilt;
  Xeq := Ieq;
  eq := I_equivalence;
  st := I_strict_order;
  cp := I_compatible_eq_lt;
  to := I_total_order;
  den := I_dense;
  we := I_without_endpoints
|}.

Declare Scope I_scope.
Open Scope I_scope. 

Notation "x < y" := (Ilt x y) : I_scope.
Notation "x == y" := (Ieq x y) : I_scope.
Notation "1" := (const_I 1) : I_scope.
Notation "0" := (const_I 0) : I_scope.

(* ----------------------------------------------------------- *)
(*                    I is Dedekind complete.                  *)
(* ----------------------------------------------------------- *)



Theorem I_Dedekind_complete :
Dedekind_complete I_dlos.
Proof.
unfold Dedekind_complete.
unfold comparable_partition, havemax, havemin.
intro f. intros [H1 [H2 H3]].
assert (H4 : exists h : X Q_dlos -> bool,
             forall q : Q, h q = f(const_I q)).
{ exists (fun q : Q => f(const_I q)). reflexivity. }
destruct H4 as [h H4].
assert (H5 : comparable_partition h).
{ repeat split.
  { rewrite mono_inc'. simpl. intros.
    destruct (Q_dec p q) as [[Hdec|Hdec]|Hdec].
    { exact Hdec. }
    { specialize (const_I_order_preserve q p Hdec) as H5.
      rewrite mono_inc' in H1.
      simpl in H1. rewrite H4 in H. rewrite H4 in H0.
      specialize (H1 _ _ H H0) as H6.
      assert (H7 : asymmetric Ilt). { apply I_strict_order. }
      apply H7 in H6. unfold not in H6.
      apply H6 in H5. contradiction. }
    { specialize (function Q_dlos h p q Hdec) as H5.
      rewrite H H0 in H5. discriminate. } }
  { simpl. simpl in H2. destruct H2 as [x Hx].
    assert (H5 : exists y : I, Ilt y x).
    { apply I_without_endpoints. }
    destruct H5 as [y Hyx].
    assert (H6 : exists q : Q,
                 (Ilt y (const_I q)) /\ (Ilt (const_I q) x)).
    { apply const_I_dense. exact Hyx. }
    destruct H6 as [q [_ Hqx]].
    exists q. rewrite H4. apply less_part with x.
    exact H1. exact Hqx. exact Hx. }
  { simpl. simpl in H3. destruct H3 as [y Hy].
    assert (H5 : exists x : I, Ilt y x).
    { apply I_without_endpoints. }
    destruct H5 as [x Hyx].
    assert (H6 : exists q : Q,
                 (Ilt y (const_I q)) /\ (Ilt (const_I q) x)).
    { apply const_I_dense. exact Hyx. }
    destruct H6 as [q [Hyq _]].
    exists q. rewrite H4. apply greater_part with y.
    exact H1. exact Hyq. exact Hy. } }
destruct (classify_comp_part h H5) as [[H6 H7]|[[H6 H7]|[H6 H7]]].
{ unfold havemax in H6. simpl in H6. destruct H6 as [x [Hx Hy]].
  left. exists (const_I x). split.
  { rewrite -H4. exact Hx. }
  { intros. specialize (const_I_dense _ _ H) as [z [Hxz Hzy]].
    specialize (const_I_order_reverse _ _ Hxz) as H8.
    apply Hy in H8. rewrite H4 in H8.
    apply greater_part with (const_I z).
    exact H1. exact Hzy. exact H8. } }
{ unfold havemin in H7. simpl in H7. destruct H7 as [y [Hy Hx]].
  right. exists (const_I y). split.
  { rewrite -H4. exact Hy. }
  { intros. specialize (const_I_dense _ _ H) as [z [Hxz Hzy]].
    specialize (const_I_order_reverse _ _ Hzy) as H8.
    apply Hx in H8. rewrite H4 in H8.
    apply less_part with (const_I z).
    exact H1. exact Hxz. exact H8. } }
Admitted. 



 

(* ----------------------------------------------------------- *)
(*                      Define addition on I,                  *)
(*             and show that (I, +) is an abelian group.       *)
(* ----------------------------------------------------------- *)




Definition seq_plus (f g : positive -> Q) :=
fun n : positive => (f n) + (g n).

Lemma compare_plus (a b : I) :
compare (seq_plus (l a) (l b)) (seq_plus (r a) (r b)).
Proof.
unfold compare, seq_plus. 
destruct (comp a) as [s Hs], (comp b) as [t Ht].
destruct (Pos_max_two s t) as [x [H1 H2]].
exists x. intros.
specialize (Hs n (Pos.le_trans _ _ _ H1 H)) as H3.
specialize (Ht n (Pos.le_trans _ _ _ H2 H)) as H4.
exact (Qplus_le_compat _ _ _ _ H3 H4).
Qed.

Lemma get_closer_ext (a : I) : 
forall m n : positive, (exists p : positive, 
(n <= p)%positive /\ (r a p - l a p < 1 # m)%Q /\
(forall q s : positive, (p <= q)%positive -> (q <= s)%positive 
 -> (r a s - l a s <= r a q - l a q)%Q)).
Proof.
intros. destruct (inc a) as [s Hs], (dec a) as [t Ht].
destruct (Pos_max_three n s t) as [x [H1 [H2 H3]]].
destruct (clo a m x) as [y [H4 H5]].
exists y. repeat split. { exact (Pos.le_trans _ _ _ H1 H4). }
{ exact H5. }
{ intros q u. intros.
  assert (H6 : r a u <= r a q).
  { apply Ht. exact (Pos_le_trans_four _ _ _ _ H3 H4 H). exact H0.  }
  assert (H7 : l a q <= l a u).
  { apply Hs. exact (Pos_le_trans_four _ _ _ _ H2 H4 H). exact H0. }
  apply Qle_minus_iff. apply Qle_minus_iff in H6, H7.
  specialize (Qplus_le_compat _ _ _ _ H6 H7) as H8.
  rewrite Qplus_0_r in H8. 
  assert (H9 : (r a q - l a q + - (r a u - l a u) 
  == r a q + - r a u + (l a u + - l a q))%Q ). { ring. }
  rewrite H9. exact H8. }
Qed.

Lemma get_closer_plus (a b : I) : 
get_closer (seq_plus (l a) (l b)) (seq_plus (r a) (r b)).
Proof.
unfold get_closer, seq_plus. intros.
destruct (get_closer_ext a m n) as [w [H1 [H2 H3]]].
destruct (get_closer_ext b m n) as [x [J1 [J2 J3]]].
destruct (Pos_max_two w x) as [y [J4 J5]].
destruct (clo a (2*m)%positive y) as [s [H4 H5]].
destruct (clo b (2*m)%positive y) as [t [H6 H7]].
destruct (Pos_max_two s t) as [z [H8 H9]].
exists z. split. 
{ apply Pos.le_trans with y%positive.
  exact (Pos.le_trans _ _ _ J1 J5). exact (Pos.le_trans _ _ _ H4 H8). }
{ assert (H10 : ((1 # (2 * m)%positive) + (1 # (2 * m)%positive) 
            == 1 # m%positive)%Q ).
  { rewrite Qinv_plus_distr. simpl. unfold Qeq. simpl. by []. }
  assert (H11 : (r a z - l a z <= r a s - l a s)%Q). 
  { apply H3. exact (Pos.le_trans _ _ _ J4 H4). exact H8. }
  assert (H12 : (r b z - l b z <= r b t - l b t)%Q).
  { apply J3. exact (Pos.le_trans _ _ _ J5 H6). exact H9. }
  specialize (Qle_lt_trans _ _ _ H11 H5) as H13.
  specialize (Qle_lt_trans _ _ _ H12 H7) as H14.
  assert (H15 : (r a z + r b z - (l a z + l b z)
  == (r a z - l a z) + (r b z - l b z))%Q). { ring. }
  rewrite H15. rewrite -H10. 
  exact (Qplus_lt_compat _ _ _ _ H13 H14). }
Qed.

Lemma increasing_plus (a b : I) : 
increasing (seq_plus (l a) (l b)).
Proof.
unfold increasing, seq_plus.
destruct (inc a) as [s Hs], (inc b) as [t Ht].
destruct (Pos_max_two s t) as [x [H1 H2]].
exists x. intros.
specialize (Hs _ _ (Pos.le_trans _ _ _ H1 H) H0) as H3.
specialize (Ht _ _ (Pos.le_trans _ _ _ H2 H) H0) as H4.
exact (Qplus_le_compat _ _ _ _ H3 H4).
Qed.

Lemma decreasing_plus (a b : I) : 
decreasing (seq_plus (r a) (r b)).
Proof.
unfold decreasing, seq_plus.
destruct (dec a) as [s Hs], (dec b) as [t Ht].
destruct (Pos_max_two s t) as [x [H1 H2]].
exists x. intros. 
specialize (Hs _ _ (Pos.le_trans _ _ _ H1 H) H0) as H3.
specialize (Ht _ _ (Pos.le_trans _ _ _ H2 H) H0) as H4.
exact (Qplus_le_compat _ _ _ _ H3 H4).
Qed.

Definition Iplus (a b : I) : I :=
{|
  l := seq_plus (l a) (l b);
  r := seq_plus (r a) (r b);
  comp := compare_plus a b;
  clo := get_closer_plus a b;
  inc := increasing_plus a b;
  dec := decreasing_plus a b;
|}.



Notation "x + y" := (Iplus x y) : I_scope.




Theorem Iplus_Ieq_compatible : 
forall a b c d : I, a == b -> c == d -> a + c == b + d.
Proof.
assert (J : forall a b c d : I, compare (l b) (r a) -> compare (l d) (r c)
            -> compare (seq_plus (l b) (l d)) (seq_plus (r a) (r c))).
{ unfold compare, seq_plus. intros.
  destruct H as [s Hs], H0 as [t Ht]. 
  destruct (Pos_max_two s t) as [x [H1 H2]]. exists x. intros.
  specialize (Hs n (Pos.le_trans _ _ _ H1 H)) as H3.
  specialize (Ht n (Pos.le_trans _ _ _ H2 H)) as H4.
  exact (Qplus_le_compat _ _ _ _ H3 H4). }
unfold Iplus, Ieq. simpl. intros. split.
{ apply J. apply H. apply H0. }
{ apply J. apply H. apply H0. }
Qed.



Theorem Iplus_comm : 
forall a b : I, a + b == b + a.
Proof.
intros.
unfold Iplus, Ieq. simpl. unfold compare, seq_plus. 
assert (H : exists m : positive, forall n : positive, 
       (m <= n)%positive -> l b n + l a n <= r a n + r b n).
{ destruct (comp a) as [s Hs], (comp b) as [t Ht].
  destruct (Pos_max_two s t) as [x [H1 H2]]. exists x. intros.
  specialize (Hs n (Pos.le_trans _ _ _ H1 H)) as H3.
  specialize (Ht n (Pos.le_trans _ _ _ H2 H)) as H4.
  setoid_rewrite Qplus_comm at 1.
  exact (Qplus_le_compat _ _ _ _ H3 H4). }
split. { exact H. }
{ destruct H. exists x. intros. setoid_rewrite Qplus_comm.
  apply H. exact H0. }
Qed.

Theorem Iplus_assoc :
forall a b c : I, (a + b) + c == a + (b + c).
Proof.
unfold Iplus, Ieq. simpl. unfold compare, seq_plus. intros.
assert (H : exists m : positive, forall n : positive,
   (m <= n)%positive -> l a n + (l b n + l c n) <= r a n + r b n + r c n).
{ destruct (comp a) as [s Hs], (comp b) as [t Ht], (comp c) as [u Hu].
  destruct (Pos_max_three s t u) as [x [H1 [H2 H3]]]. exists x. intros.
  specialize (Hs n (Pos.le_trans _ _ _ H1 H)) as H4.
  specialize (Ht n (Pos.le_trans _ _ _ H2 H)) as H5.
  specialize (Hu n (Pos.le_trans _ _ _ H3 H)) as H6.
  setoid_rewrite Qplus_assoc. 
  specialize (Qplus_le_compat _ _ _ _ H4 H5) as H7.
  exact (Qplus_le_compat _ _ _ _ H7 H6). }
split. { exact H. }
{ destruct H. exists x. intros. rewrite Qplus_assoc. 
  setoid_rewrite <- Qplus_assoc at 1. apply H. exact H0. }
Qed.




Theorem Iplus_0_r :
forall a : I, a + 0 == a.
Proof.
intros. unfold const_I, Ieq. simpl. 
unfold compare, seq_plus, const. 
destruct (comp a) as [s Hs]. split.
{ exists s. intros. rewrite Qplus_0_r. exact (Hs _ H). }
{ exists s. intros. rewrite Qplus_0_r. exact (Hs _ H). } 
Qed.



Definition seq_opp (f : positive -> Q) := 
fun n : positive => - (f n).

Lemma compare_opp (a : I) : 
compare (seq_opp (r a)) (seq_opp (l a)).
Proof.
unfold compare, seq_opp. destruct (comp a) as [s Hs].
exists s. intros. apply Qopp_le_compat. apply Hs. exact H.
Qed.

Lemma get_closer_opp (a : I) : 
get_closer (seq_opp (r a)) (seq_opp (l a)).
Proof.
unfold get_closer, seq_opp. intros. 
destruct (clo a m n) as [s [H1 H2]]. 
exists s. split. { apply H1. }
{ assert (H3 : (- l a s - - r a s == r a s - l a s)%Q). { ring. }
  rewrite H3. exact H2. }
Qed.

Lemma increasing_opp (a : I) : 
increasing (seq_opp (r a)).
Proof.
unfold increasing, seq_opp. destruct (dec a) as [s Hs].
exists s. intros. apply Qopp_le_compat. apply Hs. exact H. exact H0.
Qed.

Lemma decreasing_opp (a : I) : 
decreasing (seq_opp (l a)).
unfold decreasing, seq_opp. destruct (inc a) as [s Hs].
exists s. intros. apply Qopp_le_compat. apply Hs. exact H. exact H0.
Qed.

Definition Iopp (a : I) : I :=  
{|
  l := seq_opp (r a);
  r := seq_opp (l a); 
  comp := compare_opp a;
  clo := get_closer_opp a;
  inc := increasing_opp a;
  dec := decreasing_opp a;
|}.



Notation "- x" := (Iopp x) : I_scope.



Theorem Iplus_opp_r :
forall a : I, a + (- a) == 0.
Proof.
intros. unfold const_I, Ieq. simpl. 
unfold compare, const, seq_plus. unfold seq_opp.
assert (H : (exists m : positive,
   forall n : positive, (m <= n)%positive -> 0 <= r a n + - l a n)).
{ destruct (comp a) as [s Hs]. exists s. intros.
  specialize (Hs _ H) as H1. apply Qle_minus_iff in H1. exact H1. }
split. { exact H. }
{ destruct H. exists x. intros. apply Qle_minus_iff. rewrite Qplus_0_l. 
  assert (H1 : (- (l a n + - r a n) == r a n + - l a n)%Q). { ring. }
  rewrite H1. exact (H _ H0). }
Qed.





(* ----------------------------------------------------------- *)
(*            Addition and order on I are compatible           *)
(* ----------------------------------------------------------- *)





Theorem Iplus_order_compatible : 
forall a b c, a < b -> a + c < b + c.
Proof. 
unfold Ilt, Iplus. simpl. unfold seq_plus. intros.
destruct (dec a) as [s Hs], (inc b) as [t Ht].
destruct (Pos_max_three m s t) as [x [H1 [H2 H3]]].
destruct (H x) as [y [H4 H5]].
apply Qlt_minus_iff in H5.
destruct (Archimedean _ H5) as [w Hw].
destruct (clo c w y) as [z [H6 H7]].
exists z. split. { exact (Pos_le_trans_four _ _ _ _ H1 H4 H6). }
{ specialize (Qlt_trans _ _ _ H7 Hw) as H8.
  specialize (Hs y z (Pos.le_trans _ _ _ H2 H4) H6) as H9.
  specialize (Ht y z (Pos.le_trans _ _ _ H3 H4) H6) as H10.
  specialize (Qplus_le_compat _ _ _ _ H9 H10) as H11.
  specialize (Qplus_lt_le_compat _ _ _ _ H8 H11) as H12.
  apply Qlt_minus_iff in H12. apply Qlt_minus_iff.
  assert (H13 : (l b z + l c z + - (r a z + r c z) ==
  l b y + - r a y + (r a y + l b z) + - (r c z - l c z + (r a z + l b y)))%Q).
  { ring. } rewrite <- H13 in H12. exact H12. }
Qed.

Theorem Iplus_order_compatible_l : 
forall a b c : I, a < b -> c + a < c + b.
Proof.
intros. specialize (Iplus_order_compatible _ _ c H) as H0.
specialize (Iplus_comm a c) as H1. specialize (Iplus_comm b c) as H2.
exact (I_compatible_eq_lt _ _ _ _ H1 H2 H0).
Qed.



(* ----------------------------------------------------------- *)
(*     Some necessary lemmas to define multiplication on P.    *)
(* ----------------------------------------------------------- *)



Lemma Ieq_refl : 
forall a : I, a == a.
Proof.
apply I_equivalence.
Qed.

Lemma Ieq_sym : 
forall a b : I, a == b -> b == a.
Proof.
apply I_equivalence.
Qed.

Lemma Ieq_trans : 
forall a b c : I, a == b -> b == c -> a == c.
Proof.
apply I_equivalence. 
Qed.

Lemma Ilt_irrefl : 
forall a : I, not (a < a).
Proof. 
apply I_strict_order.
Qed.

Lemma Ilt_asym : 
forall a b : I, a < b -> not (b < a).
Proof.
apply I_strict_order.
Qed.

Lemma Ilt_trans : 
forall a b c : I, a < b -> b < c -> a < c.
Proof.
apply I_strict_order.
Qed. 



Lemma Ineg_pos (a : I) :
a < 0 -> 0 < - a.
Proof.
unfold Ilt, const_I. simpl. unfold const, seq_opp. intros.
destruct (H m) as [n [H1 H2]].
exists n. intuition. apply Qopp_lt_compat in H2. exact H2.
Qed.

Lemma Ipos_neg (a : I) : 
0 < a -> - a < 0.
Proof.
unfold Ilt, const_I, const; simpl. unfold seq_opp. intros.
destruct (H m) as [s [H1 H2]]. exists s. intuition.
assert (H0 : (0 = -0)%Q). { by []. } 
rewrite H0. apply Qopp_lt_compat. exact H2.
Qed.

Lemma Iopp_opp (a : I) : 
- (- a) == a.
Proof.
destruct a as [l r comp clo inc dec]. unfold Iopp, Ieq. simpl.
unfold compare, seq_opp. setoid_rewrite Qopp_opp. split.
{ exact comp. } { exact comp. }
Qed.

Lemma I0_opp (a : I) : 
a == 0 -> - a == 0.
Proof.
unfold Ieq, const_I, const. simpl. unfold compare, seq_opp.
intros [[s Hs] [t Ht]]. assert (H : (0 = -0)%Q). { by []. } split.
{ exists t. intros. rewrite H. apply Qopp_le_compat. apply Ht. apply H0. }
{ exists s. intros. rewrite H. apply Qopp_le_compat. apply Hs. apply H0. }
Qed.

Lemma I0_refl : 
0 == 0.
Proof. 
apply Ieq_refl.
Qed.

Lemma Iopp_eq (a b : I) : 
a == b -> - a == - b.
Proof.
unfold Ieq. unfold compare. intros [[s Hs] [t Ht]].
unfold Iopp. simpl. split.
{ exists t. intros. apply Qopp_le_compat. exact (Ht _ H). }
{ exists s. intros. apply Qopp_le_compat. exact (Hs _ H). }
Qed.



Lemma Ipos_iff (a : I) : 
0 < a <-> exists m : positive, 
(forall n : positive, (m <= n)%positive -> (0 < l a n)%Q).
Proof.
split.
{ unfold const_I, Ilt. simpl. unfold const. intros.
  destruct (inc a) as [s Hs]. destruct (H s) as [t [H1 H2]].
  exists t. intros. apply Qlt_le_trans with (l a t). { exact H2. }
  { apply Hs. exact H1. exact H0. } }
{ intros [s Hs]. unfold const_I, Ilt, const. simpl. intros.
  destruct (Pos_max_two s m) as [x [H1 H2]]. exists x. intuition. }
Qed.

Lemma Ipos_imply (a : I) : 
0 < a -> exists m : positive, 
(forall n : positive, (m <= n)%positive -> (0 < r a n)%Q).
Proof.
intros. destruct (comp a) as [s Hs]. rewrite Ipos_iff in H.
destruct H as [t Ht]. destruct (Pos_max_two s t) as [x [H1 H2]].
exists x. intros.
specialize (Hs n (Pos.le_trans _ _ _ H1 H)) as H3.
specialize (Ht n (Pos.le_trans _ _ _ H2 H)) as H4.
exact (Qlt_le_trans _ _ _ H4 H3).
Qed.

Lemma Ineg_iff (a : I) : 
a < 0 <-> exists m : positive, 
(forall n : positive, (m <= n)%positive -> (r a n < 0)%Q).
Proof.
split.
{ unfold const_I, Ilt. simpl. unfold const. intros.
  destruct (dec a) as [s Hs]. destruct (H s) as [t [H1 H2]].
  exists t. intros. apply Qle_lt_trans with (r a t). 
  { exact (Hs _ _ H1 H0). } { exact H2. } }
{ intros [s Hs]. unfold const_I, Ilt, const. simpl. intros.
  destruct (Pos_max_two s m) as [x [H1 H2]]. exists x. intuition. }
Qed.

Lemma Ineg_imply (a : I) : 
a < 0 -> exists m : positive, 
(forall n : positive, (m <= n)%positive -> (l a n < 0)%Q).
Proof.
intros. destruct (comp a) as [s Hs]. rewrite Ineg_iff in H.
destruct H as [t Ht]. destruct (Pos_max_two s t) as [x [H1 H2]].
exists x. intros.
specialize (Hs n (Pos.le_trans _ _ _ H1 H)) as H3.
specialize (Ht n (Pos.le_trans _ _ _ H2 H)) as H4.
exact (Qle_lt_trans _ _ _ H3 H4).
Qed.

Lemma positive_bound (a : I) : 
exists q : Q, exists m : positive, (0 < q)%Q /\ (forall n : positive, 
(m <= n)%positive -> (r a n + l a n <= q)%Q).
Proof.
destruct (comp a) as [s Hs], (dec a) as [t Ht].
destruct (Pos_max_two s t) as [x [H1 H2]].
assert (H3 : exists q : Q, ((r a x) + (r a x) <= q /\ 1 <= q)%Q).
{ destruct (Qlt_le_dec ((r a x) + (r a x)) 1) as [H3|H3].
  { exists 1%Q. intuition. } { exists (r a x + r a x)%Q. intuition. } }
destruct H3 as [q Hq]. exists q, x. split. 
{ apply Qlt_le_trans with 1%Q. by []. apply Hq. }
{ intros. specialize (Hs n (Pos.le_trans _ _ _ H1 H)) as H3.
  apply Qle_trans with ((r a n) + (r a n))%Q.
  { apply Qplus_le_r. exact H3. } 
  { specialize (Ht _ _ H2 H) as H4. 
    specialize (Qplus_le_compat _ _ _ _ H4 H4) as H5.
    apply Qle_trans with (r a x + r a x)%Q. { exact H5. } { apply Hq. } } }
Qed.

Lemma Iplus_bound (a : I) : 
0 < a -> (exists q : Q, exists m : positive, 
(forall n : positive, (m <= n)%positive -> (0 < r a n + l a n < q)%Q ) ).
Proof.
rewrite !Ipos_iff. intros. destruct H as [m Hm].
destruct (positive_bound a) as [u [s [H1 H2]]].
destruct (comp a) as [t Ht].
destruct (Pos_max_three m s t) as [x [H3 [H4 H5]]].
exists (u+1)%Q, x. intros. split.
{ specialize (Hm _ (Pos.le_trans _ _ _ H3 H)) as H6.
  specialize (Ht _ (Pos.le_trans _ _ _ H5 H)) as H7.
  specialize (Qlt_le_trans _ _ _ H6 H7) as H8.
  setoid_rewrite <- Qplus_0_r at 1.
  exact (Qplus_lt_compat _ _ _ _ H8 H6). }
{ apply Qle_lt_trans with u%Q.
  { apply H2. exact (Pos.le_trans _ _ _ H4 H). } 
  { setoid_rewrite <- Qplus_0_r at 1. apply Qplus_lt_r. by []. } }
Qed.

Lemma Iproduct_bound (a b : I) : 
0 < a -> 0 < b -> 
(forall m : positive, (exists n : positive, 
 forall p : positive, (n <= p)%positive ->
 ((r b p - l b p) * (r a p + l a p) < 1 # m)%Q )).
Proof.
intros.
destruct (Iplus_bound a H) as [q [u H1]].
destruct (comp b) as [s Hs].
destruct (Pos_inv_lt_Q (Qinv q)) as [x Hx]; first last.
destruct (Pos_max_two u s) as [y [H2 H3]].
destruct (get_closer_ext b (m*x) y) as [v [H4 [H5 H6]]].
exists v. intros.
{ specialize (H6 v p (Pos.le_refl v) H7) as H8.
  specialize (Qle_lt_trans _ _ _ H8 H5) as H9.
  specialize (H1 p (Pos_le_trans_four _ _ _ _ H2 H4 H7)) as H10.
  assert (H' : (0 < q)%Q).
  { destruct H10. exact (Qlt_trans _ _ _ H10 H11). }
  assert (H11 : (0 <= r b p - l b p)%Q).
  { rewrite -Qle_minus_iff. 
    exact (Hs _ (Pos_le_trans_four _ _ _ _ H3 H4 H7)). }
  assert (H12 : (0 <= r b p - l b p < 1 # m * x)%Q). { intuition. }
  assert (H13 : ((r b p - l b p) * (r a p + l a p) < 
                 (1 # (m * x)) * q)%Q).
  { apply Qmult_lt_compat_nonneg. apply H12. split.
    { apply Qlt_le. apply H10. } { apply H10. } }
  apply Qlt_trans with ((1 # (m * x)) * q)%Q. { apply H13. }
  { setoid_rewrite Qmult_frac_l at 2. setoid_rewrite <- Qmult_assoc.
    assert (H14 : (0 < (1 # x) * q)%Q).
    { apply Qmult_lt_0_compat. by []. apply H'. }
    assert (H15 : (not (q == 0))%Q).
    { unfold not, Qeq. simpl. rewrite Zmult_1_r. intros.
      unfold Qlt in H'. simpl in H'. setoid_rewrite Zmult_1_r in H'.
      setoid_rewrite H15 in H'. discriminate H'. }
    specialize (Qmult_inv_r _ H15) as H16. rewrite Qmult_comm in H16.
    assert (H17 : (1 # m == (1 # m) * 1)%Q). { ring. }
    setoid_rewrite H17 at 2. rewrite Qmult_comm. 
    rewrite [(1 # m) * 1]Qmult_comm. apply Qmult_lt_compat_r. { by []. }
    { rewrite -H16. apply Qmult_lt_compat_r. { exact H'. }
      { exact Hx. } } } }
{ specialize (H1 u (Pos.le_refl u)) as H2. destruct H2 as [H2 H3].
  specialize (Qlt_trans _ _ _ H2 H3) as H4. 
  exact (Qinv_lt_0_compat q H4). }
Qed.

Lemma IPos_lower_bound (a : I) : 
0 < a -> exists q : Q, exists m : positive, ((0 < q)%Q /\
forall n : positive, (m <= n)%positive -> q <= (l a n)).
Proof.
rewrite Ipos_iff. intros. destruct H as [s Hs], (inc a) as [t Ht].
destruct (Pos_max_two s t) as [x [H1 H2]].
specialize (Hs _ H1) as H3. exists (l a x), x.
split. { exact H3. }
{ intros. exact (Ht x n H2 H). }
Qed.

Lemma Ieq_lt_0 (a b : I) : 
a == b -> 
(0 < a -> 0 < b) /\ (a == 0 -> b == 0) /\ (a < 0 -> b < 0).
Proof.
intros. assert (H0 : 0 == 0). { apply Ieq_refl. }  split; [| split].
{ exact (I_compatible_eq_lt _ _ _ _ H0 H). }
{ intros. apply Ieq_sym in H. exact (Ieq_trans _ _ _ H H1). }
{ exact (I_compatible_eq_lt _ _ _ _ H H0). }
Qed.

Lemma Iopp_plus (a b : I) : 
- (a + b) == (- a) + (- b).
Proof.
unfold Iopp, Iplus, Ieq. simpl. unfold compare, seq_plus, seq_opp.
setoid_rewrite <- Qopp_plus. destruct (comp (a+b)) as [s Hs].
unfold Iplus, seq_plus in Hs. simpl in Hs.
split; exists s; intros; apply Qopp_le_compat; exact (Hs _ H).
Qed.

Lemma I_1_nlt_0 : 
not (1 < 0).
Proof.
rewrite not_Ilt_equiv. unfold compare, const_I. simpl. unfold const.
exists 1%positive. intros. by [].
Qed.

Lemma I_1_neq_0 : 
not (1 == 0).
Proof.
unfold not, Ieq. unfold compare, const_I. simpl. unfold const.
intros [[_ _] [s H]]. specialize (H s (Pos.le_refl s)) as H1.
contradiction.
Qed.

Lemma Ipos_mult_inv_r (a : I) :  
0 < a -> 
(exists m : positive,
   forall n : positive, (m <= n)%positive -> 1 <= r a n * / l a n) /\
(exists m : positive,
   forall n : positive, (m <= n)%positive -> l a n * / r a n <= 1).
Proof. 
intros. rewrite Ipos_iff in H. destruct H as [s Hs], (comp a) as [t Ht]. 
destruct (Pos_max_two s t) as [u [H1 H2]]. split.
{ exists u. intros. specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H3.
  apply (Qmult_lt_0_le_reg_r _ _ _ H3). rewrite Qmult_1_l.
  rewrite -Qmult_assoc. assert (H4 : (/ l a n * l a n == 1)%Q).
  { rewrite Qmult_comm. apply Qmult_inv_r. unfold not. intros.
    rewrite H0 in H3. discriminate. } rewrite H4. rewrite Qmult_1_r.
  exact (Ht _ (Pos.le_trans _ _ _ H2 H)). }
{ exists u. intros. specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H3.
  specialize (Ht _ (Pos.le_trans _ _ _ H2 H)) as H4.
  specialize (Qlt_le_trans _ _ _ H3 H4) as H5.
  apply (Qmult_lt_0_le_reg_r _ _ _ H5). rewrite Qmult_1_l.
  rewrite -Qmult_assoc. assert (H6 : (/ r a n * r a n == 1)%Q).
  { rewrite Qmult_comm. apply Qmult_inv_r. unfold not. intros.
    rewrite H0 in H5. discriminate. } rewrite H6. rewrite Qmult_1_r.
  exact H4. }
Qed.

Lemma Ipos_plus (a b : I) : 
0 < a -> 0 < b -> 0 < a + b.
Proof.
intros. specialize (Iplus_order_compatible _ _ b H) as H1.
specialize (Iplus_0_r b) as H2. specialize (Iplus_comm 0 b) as H3.
specialize (Ieq_trans _ _ _ H3 H2) as H4.
specialize (Ieq_refl (a + b)) as H5.
specialize (I_compatible_eq_lt _ _ _ _ H4 H5 H1) as H6.
exact (Ilt_trans _ _ _ H0 H6).
Qed.

Lemma Ineg_plus (a b : I) : 
a < 0 -> b < 0 -> a + b < 0.
Proof.
intros. specialize (Iplus_order_compatible _ _ b H) as H1.
specialize (Iplus_0_r b) as H2. specialize (Iplus_comm 0 b) as H3.
specialize (Ieq_trans _ _ _ H3 H2) as H4.
specialize (Ieq_refl (a + b)) as H5.
specialize (I_compatible_eq_lt _ _ _ _ H5 H4 H1) as H6.
exact (Ilt_trans _ _ _ H6 H0).
Qed.

Lemma Icont1 (a : I) : 
0 == a -> 0 < a -> False.
Proof.
intros. apply Ieq_sym in H.
specialize (I_compatible_eq_lt _ _ _ _ I0_refl H H0) as H1.
apply Ilt_irrefl in H1. contradiction.
Qed.

Lemma Iseq_pos_mult1 (a b : I) : 
0 < a -> exists m : positive, forall n : positive, (m <= n)%positive ->
l a n * l b n <= l a n * r b n.
Proof.
intros. rewrite Ipos_iff in H. destruct H as [s Hs], (comp b) as [t Ht].
destruct (Pos_max_two s t) as [x [H1 H2]]. exists x. intros.
specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H3.
specialize (Ht _ (Pos.le_trans _ _ _ H2 H)) as H4.
rewrite Qmult_comm. rewrite [l a n * _]Qmult_comm.
apply Qmult_le_compat_r. exact H4. apply Qlt_le. exact H3.
Qed.

Lemma Iseq_pos_mult2 (a b : I) : 
0 < a -> exists m : positive, forall n : positive, (m <= n)%positive ->
r a n * l b n <= r a n * r b n.
Proof.
intros. apply Ipos_imply in H. destruct H as [s Hs], (comp b) as [t Ht].
destruct (Pos_max_two s t) as [x [H1 H2]]. exists x. intros.
specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H3.
specialize (Ht _ (Pos.le_trans _ _ _ H2 H)) as H4.
rewrite Qmult_comm. rewrite [r a n * _]Qmult_comm.
apply Qmult_le_compat_r. exact H4. apply Qlt_le. exact H3.
Qed.

Lemma comp' (a : I) : 
0 < a -> exists m : positive, forall n : positive, (m <= n)%positive ->
0 <= l a n <= r a n.
Proof.
intros. destruct (comp a) as [s Hs]. rewrite Ipos_iff in H.
destruct H as [t Ht]. destruct (Pos_max_two s t) as [x [H1 H2]].
exists x. intros. split. 
{ apply Qlt_le. exact (Ht _ (Pos.le_trans _ _ _ H2 H)). }
{ exact (Hs _ (Pos.le_trans _ _ _ H1 H)). }
Qed.

Lemma Ieq0_imply_l (a : I) : 
a == 0 -> exists m : positive, forall n : positive, (m <= n)%positive ->
l a n <= 0.
Proof.
unfold Ieq. unfold compare, const_I. simpl. unfold const. intros. apply H.
Qed.

Lemma Ieq0_imply_r (a : I) : 
a == 0 -> exists m : positive, forall n : positive, (m <= n)%positive ->
0 <= r a n.
Proof.
unfold Ieq. unfold compare, const_I. simpl. unfold const. intros. apply H.
Qed.



(* ----------------------------------------------------------- *)
(*                Define multiplication on I, and              *)
(*                show that (I, + , x) is a field.             *)
(* ----------------------------------------------------------- *)




Definition seq_mult (f g : positive -> Q) :=
fun n : positive => (f n) * (g n).



Lemma pos_compare_mult (a b : I) :
0 < a -> 0 < b -> compare (seq_mult (l a) (l b)) (seq_mult (r a) (r b)).
Proof.
rewrite !Ipos_iff. unfold const_I, Ilt, compare, seq_mult, const. simpl. 
intros. destruct (comp a) as [s Hs], (comp b) as [t Ht].
destruct H as [u Hu], H0 as [v Hv].
destruct (Pos_max_four u v s t) as [x [H1 [H2 [H3 H4]]]].
exists x. intros. apply Qmult_le_compat_nonneg.
{ split.
  { apply Qlt_le. apply Hu. exact (Pos.le_trans _ _ _ H1 H). }
  { apply Hs. exact (Pos.le_trans _ _ _ H3 H). } }
{ split.
  { apply Qlt_le. apply Hv. exact (Pos.le_trans _ _ _ H2 H). }
  { apply Ht. exact (Pos.le_trans _ _ _ H4 H). } }
Qed.

Lemma pos_get_closer_mult (a b : I) : 
0 < a -> 0 < b -> get_closer (seq_mult (l a) (l b)) (seq_mult (r a) (r b)).
Proof.
intros. 
assert (H' := H). assert (H0' := H0).
rewrite Ipos_iff in H. rewrite Ipos_iff in H0.
unfold const_I, Ilt, get_closer, seq_mult, const. intros.
destruct (Iproduct_bound a b H' H0' m) as [w Hw].
destruct (Iproduct_bound b a H0' H' m) as [x Hx].
destruct (Pos_max_three n w x) as [y [J1 [J2 J3]]].
assert (H3 : forall a b : Q, (a + a < b + b -> a < b)%Q).
{ intros. destruct (Qlt_le_dec a0 b0). { exact q. }
  { specialize (Qplus_le_compat _ _ _ _ q q) as H4. 
    specialize (Qplus_lt_le_compat _ _ _ _ H1 H4) as H5.
    setoid_rewrite Qplus_comm in H5 at 1. apply Qlt_irrefl in H5.
    contradiction. } }
exists y. split. { exact J1. }
{ apply H3. assert (H5 : 
  (r a y * r b y - l a y * l b y + (r a y * r b y - l a y * l b y) == 
  (r a y - l a y) * (r b y + l b y) + (r b y - l b y) * (r a y + l a y))%Q).
  { ring. } rewrite H5.
  specialize (Hx y J3) as H6. specialize (Hw y J2) as H7. 
  exact (Qplus_lt_compat _ _ _ _ H6 H7). }
Qed.

Lemma pos_increasing_mult (a b : I) :
0 < a -> 0 < b -> increasing (seq_mult (l a) (l b)).
Proof.
rewrite !Ipos_iff. unfold increasing, seq_mult. intros.
destruct H as [s Hs], H0 as [t Ht].
destruct (inc a) as [u Hu], (inc b) as [v Hv].
destruct (Pos_max_four s t u v) as [x [H1 [H2 [H3 H4]]]].
exists x. intros.
specialize (Hu n p (Pos.le_trans _ _ _ H3 H) H0) as J1.
specialize (Hv n p (Pos.le_trans _ _ _ H4 H) H0) as J2.
specialize (Hs n (Pos.le_trans _ _ _ H1 H)) as J3.
specialize (Ht n (Pos.le_trans _ _ _ H2 H)) as J4.
apply Qmult_le_compat_nonneg.
{ split. apply Qlt_le. exact J3. exact J1. }
{ split. apply Qlt_le. exact J4. exact J2. }
Qed.

Lemma pos_decreasing_mult (a b : I) : 
0 < a -> 0 < b -> decreasing (seq_mult (r a) (r b)).
Proof.
intros. apply Ipos_imply in H. apply Ipos_imply in H0.
unfold decreasing, seq_mult. intros.
destruct H as [s Hs], H0 as [t Ht].
destruct (dec a) as [u Hu], (dec b) as [v Hv].
destruct (Pos_max_four s t u v) as [x [H1 [H2 [H3 H4]]]].
exists x. intros.
specialize (Hu n p (Pos.le_trans _ _ _ H3 H) H0) as J1.
specialize (Hv n p (Pos.le_trans _ _ _ H4 H) H0) as J2.
specialize (Hs p (Pos_le_trans_four _ _ _ _ H1 H H0)) as J3.
specialize (Ht p (Pos_le_trans_four _ _ _ _ H2 H H0)) as J4.
apply Qmult_le_compat_nonneg.
{ split. apply Qlt_le. exact J3. exact J1. }
{ split. apply Qlt_le. exact J4. exact J2. }
Qed.

Lemma pos_compare_mult' (a b : I) : 
0 < a -> 0 < b -> exists m : positive, forall n : positive, 
(m <= n)%positive -> (l a n * l b n <= r a n * r b n)%Q.
Proof.
intros. specialize (pos_compare_mult _ _ H H0) as H1.
unfold compare, seq_mult in H1. exact H1.
Qed.

Lemma Iseq_pos_mult3 (a b : I) : 
0 < a -> b < 0 -> exists m : positive, 
forall n : positive, (m <= n)%positive ->
r a n * l b n <= l a n * r b n.
Proof.
intros. apply Ineg_pos in H0. 
destruct (pos_compare_mult _ _ H H0) as [s Hs]. 
unfold Iopp in Hs; simpl in Hs. unfold seq_opp in Hs.
exists s. intros. specialize (Hs _ H1) as H2.
apply Qle_minus_iff. apply Qle_minus_iff in H2.
assert (H3 : (r a n * - l b n + - (l a n * - r b n)
  == l a n * r b n + - (r a n * l b n) )%Q ). { ring. }
rewrite -H3. exact H2.
Qed.


(* Because we already prove Lemma I_total_order, i.e., 
   forall a b : I, a < b \/ a == b \/ b < a, 
   the following decidable axiom is acceptable. *)
Axiom I_dec : 
forall a : I, ({0 < a} + {a < 0}) + {a == 0}.


Lemma Ilt0 (a : I) : 
a < 0 -> exists p, I_dec a = inleft (right p).
Proof.
intros. destruct (I_dec a) as [[Ha|Ha]|Ha].
{ apply Ilt_asym in H. unfold not in H. assert (Ha' := Ha).
  apply H in Ha'. contradiction. }
{ exists Ha. reflexivity. }
{ specialize (I_compatible_eq_lt _ _ _ _ Ha I0_refl H) as H1.
  apply Ilt_irrefl in H1. contradiction. }
Qed.

Lemma Igt0 (a : I) : 
0 < a -> exists p, I_dec a = inleft (left p).
Proof. 
intros. destruct (I_dec a) as [[Ha|Ha]|Ha].
{ exists Ha. reflexivity. }
{ specialize (Ilt_trans _ _ _ H Ha) as H0. 
  apply Ilt_irrefl in H0. contradiction. }
{ specialize (I_compatible_eq_lt _ _ _ _ I0_refl Ha H) as H1.
  apply Ilt_irrefl in H1. contradiction. }
Qed.

Lemma Ieq0 (a : I) : 
a == 0 -> exists p, I_dec a = inright p.
Proof.
intros. destruct (I_dec a) as [[Ha|Ha]|Ha].
{ specialize (I_compatible_eq_lt _ _ _ _ I0_refl H Ha) as H1.
  apply Ilt_irrefl in H1. contradiction. }
{ specialize (I_compatible_eq_lt _ _ _ _ H I0_refl Ha) as H1.
  apply Ilt_irrefl in H1. contradiction. }
{ exists Ha. reflexivity. }
Qed.

Ltac simp_dec :=
repeat (match goal with
 | H : ?a < 0  |- context [I_dec ?a] => destruct (Ilt0 _ H) as [p ->] ; clear p
 | H : 0 < ?a  |- context [I_dec ?a] => destruct (Igt0 _ H) as [p ->] ; clear p
 | H : ?a == 0 |- context [I_dec ?a] => destruct (Ieq0 _ H) as [p ->] ; clear p
end) ; simpl.


Lemma I_seq_mult (a b c d : I) : 
0 < a -> 0 < b -> 0 < c -> 0 < d
-> compare (l a) (r b) -> compare (l c) (r d) 
-> compare (seq_mult (l a) (l c)) (seq_mult (r b) (r d)).
Proof.
intros e f g h. unfold compare, seq_mult. intros.
destruct H as [s Hs], H0 as [t Ht]. 
rewrite Ipos_iff in e. rewrite Ipos_iff in g.
destruct e as [u Hu], g as [v Hv].
destruct (Pos_max_four s t u v) as [x [H2 [H3 [H4 H5]]]].
exists x. intros. apply Qmult_le_compat_nonneg.
{ split. { apply Qlt_le. exact (Hu _ (Pos.le_trans _ _ _ H4 H)). }
  { exact (Hs _ (Pos.le_trans _ _ _ H2 H)). } }
{ split. { apply Qlt_le. exact (Hv _ (Pos.le_trans _ _ _ H5 H)). }
  { exact (Ht _ (Pos.le_trans _ _ _ H3 H)). } }
Qed.



Definition I_seq_mult_l (a b : I) := 
match (I_dec a) with 
 | inleft (left H) => 
   match (I_dec b) with 
    | inleft (left H) => seq_mult (l a) (l b)
    | inleft (right H) => seq_opp (seq_mult (r a) (r (- b)))
    | inright H => const 0
   end
 | inleft (right H) => 
   match (I_dec b) with 
    | inleft (left H) => seq_opp (seq_mult (r (- a)) (r b)) 
    | inleft (right H) => seq_mult (l (- a)) (l (- b))
    | inright H => const 0
   end 
 | inright H => const 0
end.

Definition I_seq_mult_r (a b : I) := 
match (I_dec a) with 
 | inleft (left H) => 
   match (I_dec b) with 
    | inleft (left H) => seq_mult (r a) (r b)
    | inleft (right H) => seq_opp (seq_mult (l a) (l (- b)))
    | inright H => const 0
   end
 | inleft (right H) => 
   match (I_dec b) with 
    | inleft (left H) => seq_opp (seq_mult (l (- a)) (l b)) 
    | inleft (right H) => seq_mult (r (- a)) (r (- b))
    | inright H => const 0
   end 
 | inright H => const 0
end.



Lemma I_compare_mult (a b : I) : 
compare (I_seq_mult_l a b) (I_seq_mult_r a b).
Proof.
assert (H : exists m : positive,
  forall n : positive, (m <= n)%positive -> const 0 n <= const 0 n).
{ exists 1%positive. intros. unfold const. by []. }
unfold compare, I_seq_mult_l, I_seq_mult_r.
destruct (I_dec a) as [[Ha|Ha]|Ha], (I_dec b) as [[Hb|Hb]|Hb]; try apply H.
{ exact (pos_compare_mult _ _ Ha Hb). }
{ unfold seq_opp, seq_mult. apply Ineg_pos in Hb. 
  specialize (pos_compare_mult _ _ Ha Hb) as H1.
  unfold compare in H1. destruct H1 as [m Hm]. exists m. intros.
  apply Qopp_le_compat. exact (Hm n H0). }
{ unfold seq_opp, seq_mult. apply Ineg_pos in Ha.
  specialize (pos_compare_mult _ _ Ha Hb) as H1.
  unfold compare in H1. destruct H1 as [m Hm]. exists m. intros.
  apply Qopp_le_compat. exact (Hm n H0). }
{ apply Ineg_pos in Ha, Hb. exact (pos_compare_mult _ _ Ha Hb). }
Qed.

Lemma I_get_closer_mult (a b : I) :
get_closer (I_seq_mult_l a b) (I_seq_mult_r a b).
Proof.
assert (H : forall m n : positive, exists p : positive, 
       (n <= p)%positive /\ (const 0 p - const 0 p < 1 # m)%Q ).
{ unfold const. intros. exists n%positive. intuition. } 
unfold get_closer, I_seq_mult_l, I_seq_mult_r. 
destruct (I_dec a) as [[Ha|Ha]|Ha], (I_dec b) as [[Hb|Hb]|Hb]; try apply H.
{ exact (pos_get_closer_mult _ _ Ha Hb). }
{ apply Ineg_pos in Hb. unfold seq_opp, seq_mult.
  unfold Qminus. setoid_rewrite Qopp_opp. setoid_rewrite Qplus_comm.
  exact (pos_get_closer_mult _ _ Ha Hb). }
{ apply Ineg_pos in Ha. unfold seq_opp, seq_mult.
  unfold Qminus. setoid_rewrite Qopp_opp. setoid_rewrite Qplus_comm.
  exact (pos_get_closer_mult _ _ Ha Hb). }
{ apply Ineg_pos in Ha, Hb. unfold seq_opp, seq_mult.
  exact (pos_get_closer_mult _ _ Ha Hb). }
Qed.

Lemma I_increasing_mult (a b : I) :
increasing (I_seq_mult_l a b).
Proof.
assert (H : exists m : positive, forall n p : positive,
          (m <= n)%positive -> (n <= p)%positive -> const 0 n <= const 0 p ).
{ exists 1%positive. unfold const. intros. by []. }
unfold increasing, I_seq_mult_l.
destruct (I_dec a) as [[Ha|Ha]|Ha], (I_dec b) as [[Hb|Hb]|Hb]; try apply H.
{ exact (pos_increasing_mult _ _ Ha Hb). }
{ unfold seq_opp, seq_mult. apply Ineg_pos in Hb.
  destruct (pos_decreasing_mult _ _ Ha Hb) as [m Hm].
  exists m. intros. apply Qopp_le_compat. exact (Hm _ _ H0 H1). }
{ apply Ineg_pos in Ha. unfold seq_opp, seq_mult.
  destruct (pos_decreasing_mult _ _ Ha Hb) as [m Hm].
  exists m. intros. apply Qopp_le_compat. exact (Hm _ _ H0 H1). }
{ apply Ineg_pos in Ha, Hb. exact (pos_increasing_mult _ _ Ha Hb). }
Qed.

Lemma I_decreasing_mult (a b : I) :
decreasing (I_seq_mult_r a b).
Proof.
assert (H : exists m : positive, forall n p : positive,
          (m <= n)%positive -> (n <= p)%positive -> const 0 n <= const 0 p ).
{ exists 1%positive. unfold const. intros. by []. }
unfold decreasing, I_seq_mult_r. 
destruct (I_dec a) as [[Ha|Ha]|Ha], (I_dec b) as [[Hb|Hb]|Hb]; try apply H.
{ exact (pos_decreasing_mult _ _ Ha Hb). }
{ unfold seq_opp, seq_mult. apply Ineg_pos in Hb.
  destruct (pos_increasing_mult _ _ Ha Hb) as [m Hm].
  exists m. intros. apply Qopp_le_compat. exact (Hm _ _ H0 H1). }
{ apply Ineg_pos in Ha. unfold seq_opp, seq_mult.
  destruct (pos_increasing_mult _ _ Ha Hb) as [m Hm].
  exists m. intros. apply Qopp_le_compat. exact (Hm _ _ H0 H1). }
{ apply Ineg_pos in Ha, Hb. exact (pos_decreasing_mult _ _ Ha Hb). }
Qed.

Definition Imult (a b : I) : I :=
{|
  l := I_seq_mult_l a b ;
  r := I_seq_mult_r a b ;
  comp := I_compare_mult a b ;
  clo := I_get_closer_mult a b ;
  inc := I_increasing_mult a b ;
  dec := I_decreasing_mult a b ;
|}.

Notation "x *_I y " := (Imult x y) (at level 60, right associativity).
 
Theorem Ieq_mult_compatible : 
forall a b c d : I, a == b -> c == d -> a *_I c == b *_I d.
Proof.
assert (J1 : forall a b c d : I, 0 < a -> 0 < b -> 0 < c -> 0 < d -> 
  a == b -> c == d -> (exists m : positive, forall n : positive, 
  (m <= n)%positive -> l b n * l d n <= r a n * r c n) ).
{ unfold Ieq. unfold compare. intros.
  destruct H3 as [[s Hs] _], H4 as [[t Ht] _].
  rewrite Ipos_iff in H0. rewrite Ipos_iff in H2.
  destruct H0 as [u Hu], H2 as [v Hv].
  specialize (Pos_max_four s t u v) as [x [H2 [H3 [H4 H5]]]].
  exists x. intros. apply Qmult_le_compat_nonneg.
  { split. { apply Qlt_le. exact (Hu _ (Pos.le_trans _ _ _ H4 H0)). }
    { exact (Hs _ (Pos.le_trans _ _ _ H2 H0)). } }
  { split. { apply Qlt_le. exact (Hv _ (Pos.le_trans _ _ _ H5 H0)). }
    { exact (Ht _ (Pos.le_trans _ _ _ H3 H0)). } } }
assert (J2 : forall a b c d : I, 0 < a -> 0 < b -> 0 < c -> 0 < d -> 
  a == b -> c == d -> (exists m : positive, forall n : positive, 
  (m <= n)%positive -> l b n * l d n <= r a n * r c n) /\ 
    (exists m : positive, forall n : positive, (m <= n)%positive 
    -> l a n * l c n <= r b n * r d n)).
{ intros a b c d Ha Hb Hc Hd H H0. split. 
  { exact (J1 _ _ _ _ Ha Hb Hc Hd H H0). }
  { apply Ieq_sym in H, H0. exact (J1 _ _ _ _ Hb Ha Hd Hc H H0). } }
assert (J3 : (exists m : positive, forall n : positive, 
  (m <= n)%positive -> const 0 n <= const 0 n) /\
  (exists m : positive, forall n : positive, 
  (m <= n)%positive -> const 0 n <= const 0 n) ).
{ split; exists 1%positive; intros; unfold const; by []. }
assert (K1 : forall a b c d : Q, (a * (- b) <= c * (- d) -> c * d <= a * b)%Q).
{ intros. apply Qle_minus_iff in H. apply Qle_minus_iff. 
  assert (H1 : (c * - d + - (a * - b) == a * b + - (c * d))%Q ). { ring. }
  rewrite -H1. exact H. }
assert (K2 : forall a b : Q, (- (- a * b) == a * b)%Q). { intros. ring. }
intros. 
destruct (Ieq_lt_0 _ _ H) as [Ga [Ea La]], (Ieq_lt_0 _ _ H0) as [Gc [Ec Lc]].
unfold Imult, Ieq. simpl. unfold I_seq_mult_l, I_seq_mult_r.
unfold seq_mult, seq_opp, compare. unfold Iopp, seq_opp. simpl.
destruct (I_dec a) as [[Ha|Ha]|Ha], (I_dec c) as [[Hc|Hc]|Hc].
{ specialize (Ga Ha) as Hb. specialize (Gc Hc) as Hd. 
  destruct (Igt0 _ Hb) as [? ->], (Igt0 _ Hd) as [? ->]. 
  exact (J2 _ _ _ _ Ha Hb Hc Hd H H0). }
{ specialize (Ga Ha) as Hb. specialize (Lc Hc) as Hd.
  destruct (Igt0 _ Hb) as [? ->], (Ilt0 _ Hd) as [? ->].
  setoid_rewrite Qdistr1. apply Ineg_pos in Hc, Hd. apply Iopp_eq in H0.
  destruct (J2 _ _ _ _ Ha Hb Hc Hd H H0) as [[s Hs] [t Ht]]. 
  unfold Iopp, seq_opp in Hs, Ht; simpl in Hs, Ht. split.
  { exists t. intros. specialize (Ht _ H1) as H2. exact (K1 _ _ _ _ H2). }
  { exists s. intros. specialize (Hs _ H1) as H2. exact (K1 _ _ _ _ H2). } }
{ specialize (Ga Ha) as Hb. specialize (Ec Hc) as Hd.
  destruct (Igt0 _ Hb) as [? ->], (Ieq0 _ Hd) as [? ->]. exact J3. }
{ specialize (La Ha) as Hb. specialize (Gc Hc) as Hd.
  destruct (Ilt0 _ Hb) as [? ->], (Igt0 _ Hd) as [? ->].
  setoid_rewrite K2. apply Ineg_pos in Ha, Hb. apply Iopp_eq in H.
  destruct (J2 _ _ _ _ Hc Hd Ha Hb H0 H) as [[s Hs] [t Ht]].
  unfold Iopp, seq_opp in Hs, Ht; simpl in Hs, Ht. split.
  { exists t. intros. specialize (Ht _ H1) as H2. rewrite Qmult_comm. 
    rewrite [r a n *_]Qmult_comm. exact (K1 _ _ _ _ H2). }
  { exists s. intros. specialize (Hs _ H1) as H2. rewrite Qmult_comm.
    rewrite [r b n *_]Qmult_comm. exact (K1 _ _ _ _ H2). } }
{ specialize (La Ha) as Hb. specialize (Lc Hc) as Hd.
  destruct (Ilt0 _ Hb) as [? ->], (Ilt0 _ Hd) as [? ->].
  apply Ineg_pos in Ha, Hb, Hc, Hd. apply Iopp_eq in H, H0.
  exact (J2 _ _ _ _ Ha Hb Hc Hd H H0). }
{ specialize (La Ha) as Hb. specialize (Ec Hc) as Hd.
  destruct (Ilt0 _ Hb) as [? ->], (Ieq0 _ Hd) as [? ->]. exact J3. }
{ specialize (Ea Ha) as Hb. destruct (Ieq0 _ Hb) as [? ->]. exact J3. }
{ specialize (Ea Ha) as Hb. destruct (Ieq0 _ Hb) as [? ->]. exact J3. }
{ specialize (Ea Ha) as Hb. destruct (Ieq0 _ Hb) as [? ->]. exact J3. }
Qed.


Theorem Imult_comm : 
forall a b : I, a *_I b == b *_I a.
Proof.
assert (J : (exists m : positive,
   forall n : positive, (m <= n)%positive -> const 0 n <= const 0 n) /\
  (exists m : positive,
   forall n : positive, (m <= n)%positive -> const 0 n <= const 0 n) ).
{ split; exists 1%positive; intros; by []. }
intros. unfold Imult, Ieq. simpl. 
unfold compare, I_seq_mult_l, I_seq_mult_r, seq_mult, seq_opp.
destruct (I_dec a) as [[Ha|Ha]|Ha], (I_dec b) as [[Hb|Hb]|Hb]; try apply J.
{ specialize (I_seq_mult _ _ _ _ Ha Ha Hb Hb (comp a) (comp b) ) as H.
  unfold compare, seq_mult in H. destruct H as [t Ht]. split.
  { exists t. intros. rewrite Qmult_comm. exact (Ht _ H). }
  { exists t. intros. rewrite [r b n * _]Qmult_comm. exact (Ht _ H). } }
{ apply Ineg_pos in Hb.
  specialize (I_seq_mult _ _ _ _ Ha Ha Hb Hb (comp a) (comp (- b))) as H.
  unfold compare, seq_mult in H. destruct H as [t Ht]. split.
  { exists t. intros. apply Qopp_le_compat.
    rewrite [_ * r a n]Qmult_comm. exact (Ht _ H). }
  { exists t. intros. apply Qopp_le_compat.
    rewrite Qmult_comm. exact (Ht _ H). } }
{ apply Ineg_pos in Ha.
  specialize (I_seq_mult _ _ _ _ Ha Ha Hb Hb (comp (- a)) (comp b)) as H.
  unfold compare, seq_mult in H. destruct H as [t Ht]. split.
  { exists t. intros. apply Qopp_le_compat.
    rewrite [r b n * _]Qmult_comm. exact (Ht _ H). }
  { exists t. intros. apply Qopp_le_compat.
    rewrite Qmult_comm. exact (Ht _ H). } }
{ apply Ineg_pos in Ha, Hb.
  specialize (I_seq_mult _ _ _ _ Ha Ha Hb Hb (comp (- a)) (comp (- b))) as H.
  unfold compare, seq_mult in H. destruct H as [t Ht]. split.
  { exists t. intros. rewrite Qmult_comm. exact (Ht _ H). }
  { exists t. intros. 
    rewrite [r (- b) n * _]Qmult_comm. exact (Ht _ H). } }
Qed.



Lemma Imult_opp (a b : I) : 
a *_I b == - (a *_I (- b)).
Proof.
assert (H' : (exists m : positive,
   forall n : positive, (m <= n)%positive -> - const 0 n <= const 0 n) /\
   (exists m : positive,
   forall n : positive, (m <= n)%positive -> const 0 n <= - const 0 n) ).
{ unfold const. split; exists 1%positive; intros; by []. }
unfold Imult, Ieq. simpl. unfold I_seq_mult_l, I_seq_mult_r.
unfold seq_mult, seq_opp, compare.
destruct (I_dec a) as [[Ha|Ha]|Ha], (I_dec b) as [[Hb|Hb]|Hb]; try apply H'.
{ assert (Hb' := Hb). apply Ipos_neg in Hb'. destruct (Ilt0 _ Hb') as [? ->].
  apply Ineg_pos in Hb'. setoid_rewrite Qopp_opp. 
  specialize (Iopp_opp b) as H. unfold Ieq, compare in H. 
  destruct H as [Hs Ht]. split.
  { exact (I_seq_mult _ _ _ _ Ha Ha Hb' Hb (comp a) Ht). }
  { exact (I_seq_mult _ _ _ _ Ha Ha Hb Hb' (comp a) Hs). } }
{ assert (Hb' := Hb). apply Ineg_pos in Hb'. destruct (Igt0 _ Hb') as [? ->].
  specialize (I_seq_mult _ _ _ _ Ha Ha Hb' Hb' (comp a) (comp (- b))) as H.
  unfold compare in H. destruct H as [m Hm]. 
  split; exists m; intros; apply Qopp_le_compat; exact (Hm _ H). }
{ apply I0_opp in Hb. destruct (Ieq0 _ Hb) as [? ->]. apply H'. }
{ assert (Hb' := Hb). apply Ipos_neg in Hb'. destruct (Ilt0 _ Hb') as [? ->].
  setoid_rewrite Qopp_opp. apply Ineg_pos in Ha. 
  specialize (I_seq_mult _ _ _ _ Ha Ha Hb Hb (comp (- a)) (comp b)) as H.
  unfold compare, seq_mult in H. destruct H as [m Hm]. 
  split; exists m; intros; apply Qopp_le_compat; exact (Hm _ H). }
{ assert (Hb' := Hb). apply Ineg_pos in Hb'. destruct (Igt0 _ Hb') as [? ->].
  setoid_rewrite Qopp_opp. apply Ineg_pos in Ha. split; 
  exact (I_seq_mult _ _ _ _ Ha Ha Hb' Hb' (comp (- a)) (comp (- b))). }
{ apply I0_opp in Hb. destruct (Ieq0 _ Hb) as [? ->]. apply H'. }
Qed.

Lemma Imult_opp_r (a b : I) : 
a *_I (- b) == - (a *_I b).
Proof.
specialize (Imult_opp a (- b)) as H. specialize (Iopp_opp b) as H1.
specialize (Ieq_mult_compatible _ _ _ _ (Ieq_refl a) H1) as H2.
apply Iopp_eq in H2. exact (Ieq_trans _ _ _ H H2).
Qed.

Lemma Imult_opp_l (a b : I) : 
(- a) *_I b == - (a *_I b).
Proof.
specialize (Imult_comm (- a) b) as H1.
specialize (Imult_opp_r b a) as H2.
specialize (Ieq_trans _ _ _ H1 H2) as H3.
specialize (Imult_comm b a) as H4. apply Iopp_eq in H4.
exact (Ieq_trans _ _ _ H3 H4).
Qed.

Lemma Imult_opp_all (a b : I) : 
a *_I b == (- a) *_I (- b).
Proof.
specialize (Imult_opp a b) as H1.
specialize (Imult_opp_l a (- b)) as H2. apply Ieq_sym in H2.
exact (Ieq_trans _ _ _ H1 H2).
Qed.

Lemma Imult_0_l (a : I) : 
0 *_I a == 0.
Proof.
intros. unfold Imult, Ieq. simpl. unfold compare.
unfold I_seq_mult_l, I_seq_mult_r. destruct (Ieq0 _ I0_refl) as [? ->].
unfold const. split; exists 1%positive; intros; by [].
Qed.

Lemma Imult_0_l' (a b : I) : 
a == 0 -> a *_I b == 0.
Proof.
intros. specialize (Imult_0_l b) as H1. apply Ieq_sym in H.
specialize (Ieq_refl b) as H2. 
specialize (Ieq_mult_compatible _ _ _ _ H H2) as H3. 
apply Ieq_sym in H3. exact (Ieq_trans _ _ _ H3 H1).
Qed.

Lemma Imult_0_r' (a b : I) : 
b == 0 -> a *_I b == 0.
Proof.
intros. specialize (Imult_0_l' b a H) as H0. 
specialize (Imult_comm a b) as H1.
exact (Ieq_trans _ _ _ H1 H0).
Qed.

Lemma Ipp (a b : I) : 
0 < a -> 0 < b -> 0 < a *_I b.
Proof.
intros. unfold Imult, Ilt. simpl. unfold I_seq_mult_l. 
destruct (Igt0 a H) as [? ->], (Igt0 b H0) as [? ->].
unfold const, seq_mult. intros.
rewrite Ipos_iff in H. rewrite Ipos_iff in H0. 
destruct H as [s Hs], H0 as [t Ht]. 
destruct (Pos_max_three m s t) as [u [H1 [H2 H3]]]. exists u. split.
{ exact H1. } 
{ specialize (Hs _ H2) as H4. specialize (Ht _ H3) as H5.
  exact (Qmult_lt_0_compat _ _ H4 H5). }
Qed.

Lemma Ipn (a b : I) : 
0 < a -> b < 0 -> a *_I b < 0.
Proof.
intros. apply Ineg_pos in H0. specialize (Ipp _ _ H H0) as H1.
specialize (Imult_opp_r a b) as H2.
specialize (I_compatible_eq_lt _ _ _ _ I0_refl H2 H1) as H3.
apply Ipos_neg in H3. specialize (Iopp_opp (a *_I b)) as H4.
exact (I_compatible_eq_lt _ _ _ _ H4 I0_refl H3).
Qed.

Lemma Inp (a b : I) : 
a < 0 -> 0 < b -> a *_I b < 0.
intros. specialize (Ipn _ _ H0 H) as H1. 
specialize (Imult_comm b a) as H2.
exact (I_compatible_eq_lt _ _ _ _ H2 I0_refl H1).
Qed.

Lemma Inn (a b : I) : 
a < 0 -> b < 0 -> 0 < a *_I b.
Proof.
intros. apply Ineg_pos in H, H0. specialize (Ipp _ _ H H0) as H1.
specialize (Imult_opp_all a b) as H2. apply Ieq_sym in H2.
exact (I_compatible_eq_lt _ _ _ _ I0_refl H2 H1).
Qed.

Theorem Imult_assoc_prep : 
forall a b c : I, 0 < a -> (a *_I b) *_I c == a *_I (b *_I c).
Proof.
assert (J0 : (exists m : positive,
   forall n : positive, (m <= n)%positive -> const 0 n <= const 0 n) /\
 (exists m : positive,
   forall n : positive, (m <= n)%positive -> const 0 n <= const 0 n) ).
{ split; exists 1%positive; intros; by []. }
assert (J1 : forall a b c : I, 0 < a -> 0 < b -> 0 < c -> 
 exists m : positive, forall n : positive, (m <= n)%positive 
  -> l a n * (l b n * l c n) <= r a n * r b n * r c n).
{ intros. setoid_rewrite Qmult_assoc. specialize (Ipp _ _ H H0) as H2.
  specialize (pos_compare_mult _ _ H2 H1) as H3. 
  unfold compare, seq_mult in H3. unfold Imult in H3. simpl in H3.
  unfold I_seq_mult_l, I_seq_mult_r in H3. simpl in H3.
  destruct (Igt0 _ H) as [? ->] in H3. destruct (Igt0 _ H0) as [? ->] in H3. 
  unfold seq_mult in H3. exact H3. }
assert (J2 : forall a b c : I, 0 < a -> 0 < b -> 0 < c -> 
 (exists m : positive, forall n : positive, (m <= n)%positive 
  -> l a n * (l b n * l c n) <= r a n * r b n * r c n) /\ 
 (exists m : positive, forall n : positive, (m <= n)%positive 
  -> l a n * l b n * l c n <= r a n * (r b n * r c n)) ).
{ intros. split. { exact (J1 _ _ _ H H0 H1). }
  { setoid_rewrite Qmult_assoc. setoid_rewrite <- Qmult_assoc at 1.
    exact (J1 _ _ _ H H0 H1). } }
intros a b c Ha. unfold Ieq, compare. unfold Imult at 1. 
unfold I_seq_mult_l, I_seq_mult_r. simpl.
unfold I_seq_mult_l, I_seq_mult_r. simpl. 
destruct (I_dec b) as [[Hb|Hb]|Hb], (I_dec c) as [[Hc|Hc]|Hc].
{ specialize (Ipp _ _ Ha Hb) as Hab. specialize (Ipp _ _ Hb Hc) as Hbc.
  simp_dec. unfold I_seq_mult_l, I_seq_mult_r. simp_dec. unfold seq_mult.
  exact (J2 _ _ _ Ha Hb Hc). }
{ specialize (Ipp _ _ Ha Hb) as Hab. specialize (Ipn _ _ Hb Hc) as Hbc.
  simp_dec. unfold I_seq_mult_l, I_seq_mult_r. simp_dec. 
  unfold seq_mult, seq_opp. setoid_rewrite Qopp_opp. apply Ineg_pos in Hc.
  destruct (J2 _ _ _ Ha Hb Hc) as [[s Hs] [t Ht]].
  unfold Iopp in Hs, Ht. simpl in Hs, Ht. unfold seq_opp in Hs, Ht.
  split. { exists t. intros. apply Qopp_le_compat. exact (Ht _ H). }
  { exists s. intros. apply Qopp_le_compat. exact (Hs _ H). } }
{ simp_dec. specialize (Imult_0_r' b c Hc) as Hbc. simp_dec.
  specialize (Ipp _ _ Ha Hb) as Hab. simp_dec. exact J0. }
{ specialize (Ipn _ _ Ha Hb) as Hab. specialize (Inp _ _ Hb Hc) as Hbc.
  simp_dec. unfold I_seq_mult_l, I_seq_mult_r. simp_dec.
  unfold seq_mult, seq_opp. setoid_rewrite Qopp_opp. apply Ineg_pos in Hb.
  destruct (J2 _ _ _ Ha Hb Hc) as [[s Hs] [t Ht]].
  unfold Iopp in Hs, Ht. simpl in Hs, Ht. unfold seq_opp in Hs, Ht.
  split. { exists t. intros. apply Qopp_le_compat. exact (Ht _ H). }
  { exists s. intros. apply Qopp_le_compat. exact (Hs _ H). } }
{ specialize (Ipn _ _ Ha Hb) as Hab. specialize (Inn _ _ Hb Hc) as Hbc.
  simp_dec. unfold I_seq_mult_l, I_seq_mult_r. simp_dec.
  apply Ineg_pos in Hb, Hc. unfold seq_mult, seq_opp. 
  setoid_rewrite Qopp_opp. exact (J2 _ _ _ Ha Hb Hc). }
{ specialize (Ipn _ _ Ha Hb) as Hab. specialize (Imult_0_r' b c Hc) as Hbc.
  simp_dec. exact J0. }
{ specialize (Imult_0_r' a b Hb) as Hab;
  specialize (Imult_0_l' b c Hb) as Hbc; simp_dec; exact J0. } 
{ specialize (Imult_0_r' a b Hb) as Hab;
  specialize (Imult_0_l' b c Hb) as Hbc; simp_dec; exact J0. } 
{ specialize (Imult_0_r' a b Hb) as Hab;
  specialize (Imult_0_l' b c Hb) as Hbc; simp_dec; exact J0. }
Qed.

Theorem Imult_assoc : 
forall a b c : I, (a *_I b) *_I c == a *_I (b *_I c).
Proof.
intros. destruct (I_dec a) as [[Ha|Ha]|Ha].
{ exact (Imult_assoc_prep _ _ _ Ha). }
{ specialize (Imult_opp_all a b) as H1.
  specialize (Ieq_mult_compatible _ _ _ _ H1 (Ieq_refl c)) as H2.
  apply Ineg_pos in Ha.
  specialize (Imult_assoc_prep (- a) (- b) c Ha) as H3.
  specialize (Ieq_trans _ _ _ H2 H3) as H4.
  specialize (Imult_opp_l b c) as H5.
  specialize (Ieq_mult_compatible _ _ _ _ (Ieq_refl (- a)) H5) as H6.
  specialize (Ieq_trans _ _ _ H4 H6) as H7.
  specialize (Imult_opp_all a (b *_I c)) as H8. apply Ieq_sym in H8.
  exact (Ieq_trans _ _ _ H7 H8). }
{ specialize (Imult_0_l' a b Ha) as H1.
  specialize (Imult_0_l' _ c H1) as H2.
  specialize (Imult_0_l' a (b *_I c) Ha) as H3. apply Ieq_sym in H3.
  exact (Ieq_trans _ _ _ H2 H3). }
Qed.



Theorem Imult_1_r : 
forall a : I, a *_I 1 == a.
Proof.
assert (J : forall b : I, b == 0 -> 
(exists m : positive, forall n : positive, (m <= n)%positive -> l b n <= 0) /\
(exists m : positive, forall n : positive, (m <= n)%positive -> 0 <= r b n) ).
{ unfold Ieq. unfold compare, const_I. simpl. unfold const. intuition. }
intros. unfold Imult, Ieq. simpl.
unfold compare, I_seq_mult_r, I_seq_mult_l, seq_mult. simpl. unfold const.
destruct (I_dec a) as [[Ha|Ha]|Ha], (I_dec 1) as [[H1|H1]|H1].
{ destruct (comp a) as [t Ht]. split.
  { exists t. intros. rewrite Qmult_1_r. exact (Ht _ H). }
  { exists t. intros. rewrite Qmult_1_r. exact (Ht _ H). } }
{ apply I_1_nlt_0 in H1. contradiction. }
{ apply I_1_neq_0 in H1. contradiction. }
{ destruct (comp a) as [t Ht]. split.
  { exists t. intros. unfold seq_opp. rewrite Qmult_1_r.
    rewrite Qopp_opp. exact (Ht _ H). }
  { exists t. intros. unfold seq_opp. rewrite Qmult_1_r.
    rewrite Qopp_opp. exact (Ht _ H). } }
{ apply I_1_nlt_0 in H1. contradiction. }
{ apply I_1_neq_0 in H1. contradiction. }
{ exact (J a Ha). } { exact (J a Ha). } { exact (J a Ha). }
Qed.




Definition seq_inv (f : positive -> Q) := 
fun n : positive => / (f n).



Lemma pos_compare_inv (a : I) : 
0 < a -> compare (seq_inv (r a)) (seq_inv (l a)).
Proof. 
rewrite Ipos_iff. unfold compare, seq_inv. intros [s Hs].
destruct (comp a) as [t Ht]. destruct (Pos_max_two s t) as [x [H1 H2]].
exists x. intros.
specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H3.
specialize (Ht _ (Pos.le_trans _ _ _ H2 H)) as H4.
specialize (Qlt_le_trans _ _ _ H3 H4) as H5.
exact (Qinv_le_imply _ _ H3 H5 H4).
Qed.

Lemma pos_get_closer_inv (a : I) : 
0 < a -> get_closer (seq_inv (r a)) (seq_inv (l a)).
Proof.
intros. destruct (IPos_lower_bound a H) as [q [u [Hq Hu]]].
rewrite Ipos_iff in H. unfold get_closer, seq_inv. intros.
destruct H as [s Hs]. destruct (comp a) as [t Ht].
destruct (Pos_max_four u s t n) as [x [H1 [H2 [H3 H4]]]].
assert (H0 : (0 < q * q * (1 # m))%Q).
{ apply Qmult_lt_0_compat; last first. { by []. }
  { apply Qmult_lt_0_compat. exact Hq. exact Hq. } }
destruct (Pos_inv_lt_Q (q*q*(1#m)) H0) as [v Hv].
destruct (clo a v x) as [y [H5 H6]].
exists y. split. { exact (Pos.le_trans _ _ _ H4 H5). }
{ specialize (Hu y (Pos.le_trans _ _ _ H1 H5)) as H7.
  specialize (Hs y (Pos.le_trans _ _ _ H2 H5)) as H8.
  specialize (Ht y (Pos.le_trans _ _ _ H3 H5)) as H9.
  specialize (Qlt_le_trans _ _ _ H8 H9) as H10.
  specialize (Qinv_lt_0_compat _ H8) as H11.
  specialize (Qinv_lt_0_compat _ H10) as H12.
  assert (H13 : ( (/ l a y - / r a y) == 
                  (r a y - l a y) / (l a y * r a y) )%Q ).
  { exact (Qinv_minus _ _ H8 H10). }
  rewrite H13. unfold Qdiv.
  specialize (Qlt_trans _ _ _ H6 Hv) as H14.
  assert (H15 : ( / (l a y * r a y) <= / (q * q) )%Q ).
  { apply Qinv_le_imply. exact (Qmult_lt_0_compat _ _ Hq Hq).
    exact (Qmult_lt_0_compat _ _ H8 H10). 
    apply Qmult_le_compat_nonneg.
    { split. apply Qlt_le. exact Hq. exact H7. }
    { split. apply Qlt_le. exact Hq. exact (Qle_trans _ _ _ H7 H9). } }
  assert (H16 : ( ( q * q * (1 # m) ) * ( / (q * q) ) == 1 # m )%Q).
  { unfold Qlt in Hq. simpl in Hq. rewrite Zmult_1_r in Hq.
    assert (H16 : exists p : positive, Qnum q = Z.pos p).
    { apply Z2Pos.id in Hq. exists (Z.to_pos (Qnum q)). symmetry. exact Hq. }
    destruct H16 as [p Hp]. unfold Qinv, Qeq. simpl. rewrite Hp. simpl.
    rewrite !Pos2Z.inj_mul. ring. }
  rewrite -H16. apply Qmult_lt_le_compat.
  { split. rewrite Qle_minus_iff in H9. exact H9. exact H14. }
  { split. rewrite Qinv_mult_distr. exact (Qmult_lt_0_compat _ _ H11 H12).
    exact H15.  } }
Qed.

Lemma pos_increasing_inv (a : I) : 
0 < a -> increasing (seq_inv (r a)).
Proof.
unfold increasing, seq_inv. intros. assert (H0 := H).
apply Ipos_imply in H. rewrite Ipos_iff in H0.
destruct H as [s Hs], (dec a) as [t Ht], H0 as [u Hu].
destruct (comp a) as [v Hv].
destruct (Pos_max_four s t u v) as [x [H1 [H2 [H3 H4]]]].
exists x. intros. 
specialize (Hu n (Pos.le_trans _ _ _ H3 H)) as H5.
specialize (Hv n (Pos.le_trans _ _ _ H4 H)) as H6.
specialize (Hu p (Pos_le_trans_four _ _ _ _ H3 H H0)) as H7.
specialize (Hv p (Pos_le_trans_four _ _ _ _ H4 H H0)) as H8.
specialize (Qlt_le_trans _ _ _ H5 H6) as H9.
specialize (Qlt_le_trans _ _ _ H7 H8) as H10.
specialize (Ht n p (Pos.le_trans _ _ _ H2 H) H0) as H11.
apply Qinv_le_imply. exact H10. exact H9. exact H11.
Qed.

Lemma pos_decreasing_inv (a : I) : 
0 < a -> decreasing (seq_inv (l a)).
Proof.
unfold decreasing, seq_inv. intros. rewrite Ipos_iff in H.
destruct H as [s Hs], (inc a) as [t Ht].
destruct (Pos_max_two s t) as [x [H1 H2]].
exists x. intros.
specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H3.
specialize (Ht n p (Pos.le_trans _ _ _ H2 H) H0) as H4.
apply Qinv_le_imply. { exact H3. } 
{ exact (Qlt_le_trans _ _ _ H3 H4). } { exact H4. }
Qed.


Lemma neg_compare_inv (a : I) : 
a < 0 -> compare (seq_inv (r a)) (seq_inv (l a)).
Proof.
intros. apply Ineg_pos in H. unfold compare, seq_inv.
specialize (pos_compare_inv _ H) as H1.
unfold compare, seq_inv in H1. unfold Iopp in H1. simpl in H1.
destruct H1 as [t Ht]. exists t. intros. specialize (Ht _ H0) as H1.
unfold seq_opp in H1. 
rewrite !Qinv_opp in H1. apply Qopp_le_compat in H1.
rewrite !Qopp_opp in H1. exact H1.
Qed.


Lemma neg_get_closer_inv (a : I) : 
a < 0 -> get_closer (seq_inv (r a)) (seq_inv (l a)).
Proof.
intros. apply Ineg_pos in H. unfold get_closer, seq_inv.
specialize (pos_get_closer_inv _ H) as H1.
unfold get_closer, seq_inv in H1. unfold Iopp in H1. simpl in H1.
unfold seq_opp in H1. intros. destruct (H1 m n) as [q [H2 H3]].
exists q. rewrite !Qinv_opp in H3. unfold Qminus in H3.
rewrite Qopp_opp in H3. rewrite Qplus_comm in H3. intuition.
Qed.

Lemma neg_increasing_inv (a : I) : 
a < 0 -> increasing (seq_inv (r a)).
Proof.
intros. apply Ineg_pos in H. unfold increasing, seq_inv.
specialize (pos_decreasing_inv _ H) as H1.
unfold decreasing, seq_inv in H1. destruct H1 as [t Ht].
exists t. intros. specialize (Ht _ _ H0 H1) as H2.
rewrite !Qinv_opp in H2. apply Qopp_le_compat in H2.
rewrite !Qopp_opp in H2. exact H2.
Qed.

Lemma neg_decreasing_inv (a : I) : 
a < 0 -> decreasing (seq_inv (l a)).
Proof.
intros. apply Ineg_pos in H. unfold decreasing, seq_inv.
specialize (pos_increasing_inv _ H) as H1.
unfold increasing, seq_inv in H1. destruct H1 as [t Ht].
exists t. intros. specialize (Ht _ _ H0 H1) as H2.
rewrite !Qinv_opp in H2. apply Qopp_le_compat in H2.
rewrite !Qopp_opp in H2. exact H2.
Qed.



Definition Iinv (a : I) : I := 
match (I_dec a) with 
 | inleft (left H) => 
   {| 
      l := seq_inv (r a) ; 
      r := seq_inv (l a) ; 
      comp := (pos_compare_inv a H) ;
      clo := (pos_get_closer_inv a H) ; 
      inc := (pos_increasing_inv a H) ; 
      dec := (pos_decreasing_inv a H) ; 
   |}
 | inleft (right H) => 
   {| 
      l := seq_inv (r a) ; 
      r := seq_inv (l a) ; 
      comp := (neg_compare_inv a H) ;
      clo := (neg_get_closer_inv a H) ; 
      inc := (neg_increasing_inv a H) ; 
      dec := (neg_decreasing_inv a H) ; 
   |}
 | inright H => const_I 0
end.
(* We define Iinv 0 := 0, this is, the inverse of 0 equals 0. 
   Since we want to check that non-zero element of I 
   has multiplicative inverse, this definition does not make a problem. *)


Notation " / a" := (Iinv a).

Lemma Ipos_inv_pos (a : I) : 
0 < a -> 0 < / a.
Proof.
intros. unfold Iinv. destruct (Igt0 a H) as [? ->].
unfold Ilt. simpl. unfold const, seq_inv. intros. apply Ipos_imply in H. 
destruct H as [s Hs]. destruct (Pos_max_two s m) as [t [H1 H2]].
exists t. split; intuition. specialize (Hs _ H1) as H3.
apply Qinv_lt_0_compat. exact H3.
Qed.

Lemma Ineg_inv_neg (a : I) : 
a < 0 -> / a < 0.
Proof.
intros. unfold Iinv. destruct (Ilt0 a H) as [? ->]. unfold Ilt. simpl.
unfold const, seq_inv. intros. apply Ineg_imply in H.
destruct H as [s Hs]. destruct (Pos_max_two s m) as [t [H1 H2]].
exists t. split; intuition. specialize (Hs _ H1) as H3.
apply Qlt_minus_iff in H3. rewrite Qplus_0_l in H3.
apply Qlt_minus_iff. rewrite Qplus_0_l. rewrite -Qinv_opp. 
apply Qinv_lt_0_compat. exact H3.
Qed.


Theorem Imult_inv_r : 
forall a : I, not (a == 0) -> a *_I (/ a) == 1.
Proof.
unfold not. intros. unfold Imult, Ieq. simpl. 
unfold compare, const. unfold I_seq_mult_r, I_seq_mult_l.
destruct (I_dec a) as [[Ha|Ha]|Ha]; unfold const, seq_mult.
{ specialize (Ipos_inv_pos a Ha) as Ha'. destruct (Igt0 _ Ha') as [? ->].
  unfold Iinv. simpl. destruct (Igt0 _ Ha) as [? ->]. simpl.
  unfold seq_inv. exact (Ipos_mult_inv_r _ Ha). }
{ specialize (Ineg_inv_neg a Ha) as Ha'. destruct (Ilt0 _ Ha') as [? ->].
  unfold Iinv. simpl. destruct (Ilt0 _ Ha) as [? ->]. simpl.
  unfold seq_inv, seq_opp. apply Ineg_pos in Ha.
  specialize (Ipos_mult_inv_r _ Ha) as H0. 
  unfold Iopp in H0. simpl in H0. unfold seq_opp in H0.
  destruct H0 as [[s Hs] [t Ht]]. split.
  { exists s. intros. rewrite -Qinv_opp. exact (Hs _ H0). }
  { exists t. intros. rewrite -Qinv_opp. exact (Ht _ H0). } }
{ apply H in Ha. contradiction. }
Qed.


Lemma Imult_plus_distr_r_prep : 
forall a b c : I, 0 < a -> a *_I (b + c) == (a *_I b) + (a *_I c).
Proof.
assert (J1 : (exists m : positive, forall n : positive,
    (m <= n)%positive -> const 0 n + const 0 n <= const 0 n) /\
  (exists m : positive, forall n : positive,
    (m <= n)%positive -> const 0 n <= const 0 n + const 0 n) ).
{ split; exists 1%positive; intros; by []. }
assert (J2 : forall a b c : I, 0 < a -> 0 < b -> c < 0 -> b + c == 0 -> 
 (exists m : positive, forall n : positive, (m <= n)%positive -> 
   l a n * l b n + r a n * l c n <= const 0 n) /\
 (exists m : positive, forall n : positive, (m <= n)%positive -> 
   const 0 n <= r a n * r b n + l a n * r c n) ).
{ intros a b c Ha Hb Hc Hd. 
  destruct (comp' _ Ha) as [s Hs], (comp' _ Hb) as [t Ht]. split.
  { destruct (Ieq0_imply_l _ Hd) as [u Hu]. unfold Iplus in Hu. simpl in Hu.
    unfold seq_plus in Hu. destruct (Pos_max_three s t u) as [v [H1 [H2 H3]]].
    exists v. intros. specialize (Ht _ (Pos.le_trans _ _ _ H2 H)) as H4.
    specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H5.
    specialize (Hu _ (Pos.le_trans _ _ _ H3 H)) as H6.
    assert (H7 : (l a n * l b n <= r a n * l b n)%Q).
    { destruct H4, H5. exact (Qmult_le_compat_r _ _ _ H7 H0). } 
    assert (H8 : ( l a n * l b n + r a n * l c n <= 
                   r a n * l b n + r a n * l c n )%Q ).
    { apply Qplus_le_l. exact H7. }
    rewrite -Qmult_plus_distr_r in H8.
    assert (H9 : (r a n * (l b n + l c n) <= r a n * 0)%Q ).
    { destruct H5. specialize (Qle_trans _ _ _ H0 H5) as H9.
      rewrite Qmult_comm. rewrite [_ * 0]Qmult_comm. apply Qmult_le_compat_r.
      exact H6. exact H9. }
    rewrite Qmult_0_r in H9. exact (Qle_trans _ _ _ H8 H9). }
  { destruct (Ieq0_imply_r _ Hd) as [u Hu]. unfold Iplus in Hu. simpl in Hu.
    unfold seq_plus in Hu. destruct (Pos_max_three s t u) as [v [H1 [H2 H3]]].
    exists v. intros. specialize (Ht _ (Pos.le_trans _ _ _ H2 H)) as H4.
    specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H5.
    specialize (Hu _ (Pos.le_trans _ _ _ H3 H)) as H6.
    assert (H7 : (l a n * r b n <= r a n * r b n)%Q).
    { destruct H4, H5. specialize (Qle_trans _ _ _ H0 H4) as H8.
      exact (Qmult_le_compat_r _ _ _ H7 H8). } 
    assert (H8 : ( l a n * r b n + l a n * r c n <= 
                   r a n * r b n + l a n * r c n )%Q ).
    { apply Qplus_le_l. exact H7. }
    rewrite -Qmult_plus_distr_r in H8.
    assert (H9 : (l a n * 0 <= l a n * (r b n + r c n))%Q ).
    { destruct H5. specialize (Qle_trans _ _ _ H0 H5) as H9.
      rewrite Qmult_comm. rewrite [l a n * _]Qmult_comm. 
      apply Qmult_le_compat_r; try intuition. }
    rewrite Qmult_0_r in H9. exact (Qle_trans _ _ _ H9 H8). } }
assert (J3 : forall a b : I, 0 < a -> b == 0 -> 0 < a + b).
{ intros. assert (H1 : 0 + b < a + b). 
  { exact (Iplus_order_compatible _ _ b H). }
  specialize (Iplus_comm b 0) as H2.
  assert (H3 : b + 0 == b). { apply Iplus_0_r. }
  specialize (Ieq_trans _ _ _ H3 H0) as H4. apply Ieq_sym in H4.
  specialize (Ieq_trans _ _ _ H4 H2) as H5. apply Ieq_sym in H5.
  exact (I_compatible_eq_lt _ _ _ _ H5 (Ieq_refl (a+b)) H1). }
assert (J4 : forall a b : I, a < 0 -> b == 0 -> a + b < 0).
{ intros. assert (H1 : a + b < 0 + b). 
  { exact (Iplus_order_compatible _ _ b H). }
  specialize (Iplus_comm b 0) as H2.
  assert (H3 : b + 0 == b). { apply Iplus_0_r. }
  specialize (Ieq_trans _ _ _ H3 H0) as H4. apply Ieq_sym in H4.
  specialize (Ieq_trans _ _ _ H4 H2) as H5. apply Ieq_sym in H5.
  exact (I_compatible_eq_lt _ _ _ _ (Ieq_refl (a+b)) H5 H1). }
assert (J5 : forall a b c : I, 0 < a -> 0 < b -> c == 0 -> 0 < b + c -> 
 (exists m : positive, forall n : positive, (m <= n)%positive ->
   l a n * l b n + const 0 n <= r a n * r b n + r a n * r c n) /\
 (exists m : positive, forall n : positive, (m <= n)%positive ->
   l a n * l b n + l a n * l c n <= r a n * r b n + const 0 n) ).
{ intros a b c Ha Hb Hc Hd.
  assert (H1 : exists m : positive, forall n : positive, (m <= n)%positive ->
               const 0 n <= r a n * r c n).
  { unfold const. apply Ipos_imply in Ha. destruct Ha as [s Hs].
    destruct (Ieq0_imply_r _ Hc) as [t Ht].
    destruct (Pos_max_two s t) as [u [H1 H2]].
    exists u. intros. specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H3.
    specialize (Ht _ (Pos.le_trans _ _ _ H2 H)) as H4.
    apply Qlt_le in H3. exact (Qmult_le_0_compat _ _ H3 H4). }
  assert (H2 : exists m : positive, forall n : positive, (m <= n)%positive ->
               l a n * l c n <= const 0 n).
  { unfold const. destruct (Ieq0_imply_l _ Hc) as [t Ht].
    rewrite Ipos_iff in Ha. destruct Ha as [s Hs].
    destruct (Pos_max_two s t) as [u [H2 H3]].
    exists u. intros. specialize (Hs _ (Pos.le_trans _ _ _ H2 H)) as H4.
    specialize (Ht _ (Pos.le_trans _ _ _ H3 H)) as H5.
    apply Qlt_le in H4. apply Qle_minus_iff. apply Qle_minus_iff in H5.
    rewrite Qplus_0_l in H5. rewrite Qplus_0_l. 
    assert (H6 : (- (l a n * l c n) == (l a n) * (- l c n) )%Q ). { ring. }
    rewrite H6. exact (Qmult_le_0_compat _ _ H4 H5). }
  split. { exact (Iseq_prod_sum1 (pos_compare_mult' _ _ Ha Hb) H1). }
  { exact (Iseq_prod_sum2 (pos_compare_mult' _ _ Ha Hb) H2). } } 
assert (J6 : forall a b c : I,  0 < a -> b < 0 -> c == 0 -> b + c < 0 -> 
 (exists m : positive, forall n : positive, (m <= n)%positive ->
   r a n * l b n + const 0 n <= l a n * r b n + l a n * r c n) /\
 (exists m : positive, forall n : positive, (m <= n)%positive ->
   r a n * l b n + r a n * l c n <= l a n * r b n + const 0 n) ).
{ intros a b c Ha Hb Hc Hd.
  assert (H1 : exists m : positive, forall n : positive, (m <= n)%positive ->
               const 0 n <= l a n * r c n).
  { unfold const. rewrite Ipos_iff in Ha. destruct Ha as [s Hs].
    destruct (Ieq0_imply_r _ Hc) as [t Ht].
    destruct (Pos_max_two s t) as [u [H1 H2]].
    exists u. intros. specialize (Hs _ (Pos.le_trans _ _ _ H1 H)) as H3.
    specialize (Ht _ (Pos.le_trans _ _ _ H2 H)) as H4.
    apply Qlt_le in H3. exact (Qmult_le_0_compat _ _ H3 H4). }
  assert (H2 : exists m : positive, forall n : positive, (m <= n)%positive ->
               r a n * l c n <= const 0 n).
  { unfold const. destruct (Ieq0_imply_l _ Hc) as [t Ht].
    apply Ipos_imply in Ha. destruct Ha as [s Hs].
    destruct (Pos_max_two s t) as [u [H2 H3]].
    exists u. intros. specialize (Hs _ (Pos.le_trans _ _ _ H2 H)) as H4.
    specialize (Ht _ (Pos.le_trans _ _ _ H3 H)) as H5.
    apply Qlt_le in H4. apply Qle_minus_iff. apply Qle_minus_iff in H5.
    rewrite Qplus_0_l in H5. rewrite Qplus_0_l. 
    assert (H6 : (- (r a n * l c n) == (r a n) * (- l c n) )%Q ). { ring. }
    rewrite H6. exact (Qmult_le_0_compat _ _ H4 H5). }
  split. { exact (Iseq_prod_sum1 (Iseq_pos_mult3 _ _ Ha Hb) H1). }
  { exact (Iseq_prod_sum2 (Iseq_pos_mult3 _ _ Ha Hb) H2). } }
intros a b c Ha. unfold Imult, Ieq. simpl. unfold compare.
unfold I_seq_mult_l, I_seq_mult_r, seq_plus, seq_mult.
destruct (Igt0 a Ha) as [? ->].
destruct (I_dec b) as [[Hb|Hb]|Hb], (I_dec c) as [[Hc|Hc]|Hc], 
         (I_dec (b + c)) as [[Hd|Hd]|Hd]; 
try apply J1; unfold Iplus; unfold seq_plus, seq_opp; 
try setoid_rewrite Qmult_plus_distr_l; 
try setoid_rewrite Qmult_plus_distr_r; 
try setoid_rewrite Qdistr1; try setoid_rewrite Qdistr2; 
try setoid_rewrite Qmult_plus_distr_l; 
try setoid_rewrite Qmult_plus_distr_r.
{ split; exact (Iseq_prod_sum (pos_compare_mult' _ _ Ha Hb)
                              (pos_compare_mult' _ _ Ha Hc)). }
{ specialize (Ipos_plus _ _ Hb Hc) as H. 
  specialize (Ilt_trans _ _ _ H Hd) as H1. apply Ilt_irrefl in H1.
  contradiction. }
{ specialize (Ipos_plus _ _ Hb Hc) as H.
  apply Ieq_sym in Hd. specialize (Icont1 _ Hd H) as H1. contradiction. }
{ specialize (pos_compare_mult _ _ Ha Hb) as H. split.
  { exact (Iseq_prod_sum H (Iseq_pos_mult2 _ _ Ha)). }
  { exact (Iseq_prod_sum H (Iseq_pos_mult1 _ _ Ha)). } }
{ specialize (Iseq_pos_mult3 _ _ Ha Hc) as H. split. 
  { exact (Iseq_prod_sum (Iseq_pos_mult1 _ _ Ha) H). }
  { exact (Iseq_prod_sum (Iseq_pos_mult2 _ _ Ha) H). } }
{ exact (J2 _ _ _ Ha Hb Hc Hd). }
{ exact (J5 _ _ _ Ha Hb Hc Hd). }
{ specialize (J3 _ _ Hb Hc) as H1. specialize (Ilt_trans _ _ _ Hd H1) as H2.
  apply Ilt_irrefl in H2. contradiction. }
{ specialize (J3 _ _ Hb Hc) as H1. apply Ieq_sym in Hd.
  specialize (Icont1 _ Hd H1) as H2. contradiction. }
{ specialize (pos_compare_mult _ _ Ha Hc) as H. split.
  { exact (Iseq_prod_sum (Iseq_pos_mult2 _ _ Ha) H). }
  { exact (Iseq_prod_sum (Iseq_pos_mult1 _ _ Ha) H). } }
{ specialize (Iseq_pos_mult3 _ _ Ha Hb) as H. split. 
  { exact (Iseq_prod_sum H (Iseq_pos_mult1 _ _ Ha)). }
  { exact (Iseq_prod_sum H (Iseq_pos_mult2 _ _ Ha)). } }
{ specialize (Ieq_sym c b) as H1. specialize (Iplus_comm c b) as H2.
  specialize (Ieq_trans _ _ _ H2 Hd) as H3. setoid_rewrite Qplus_comm.
  exact (J2 _ _ _ Ha Hc Hb H3). }
{ specialize (Ineg_plus _ _ Hb Hc) as H1. 
  specialize (Ilt_trans _ _ _ H1 Hd) as H2. apply Ilt_irrefl in H2.
  contradiction. }
{ split; exact (Iseq_prod_sum (Iseq_pos_mult3 _ _ Ha Hb) 
                              (Iseq_pos_mult3 _ _ Ha Hc)). }
{ specialize (Ineg_plus _ _ Hb Hc) as H1. apply Ineg_pos in H1.
  apply I0_opp in Hd. apply Ieq_sym in Hd.
  specialize (Icont1 _ Hd H1) as H2. contradiction. }
{ specialize (J4 _ _ Hb Hc) as H1. specialize (Ilt_trans _ _ _ Hd H1) as H2.
  apply Ilt_irrefl in H2. contradiction. }
{ exact (J6 _ _ _ Ha Hb Hc Hd). }
{ specialize (J4 _ _ Hb Hc) as H1. apply Ineg_pos in H1.
  apply I0_opp in Hd. apply Ieq_sym in Hd. 
  specialize (Icont1 _ Hd H1) as H2. contradiction. }
{ setoid_rewrite Qplus_comm. specialize (Iplus_comm b c) as H1.
  specialize (I_compatible_eq_lt _ _ _ _ (I0_refl) H1 Hd) as H2.
  exact (J5 _ _ _ Ha Hc Hb H2). }
{ specialize (J3 _ _ Hc Hb) as H1. specialize (Ilt_trans _ _ _ Hd H1) as H2.
  specialize (Iplus_comm b c) as H3. 
  specialize (I_compatible_eq_lt _ _ _ _ H3 (Ieq_refl (c+b)) H2) as H4.
  apply Ilt_irrefl in H4. contradiction. }
{ specialize (J3 _ _ Hc Hb) as H1. specialize (Iplus_comm c b) as H2.
  specialize (Ieq_trans _ _ _ H2 Hd) as H3. apply Ieq_sym in H3.
  specialize (Icont1 _ H3 H1) as H4. contradiction. }
{ specialize (J4 _ _ Hc Hb) as H1. specialize (Ilt_trans _ _ _ H1 Hd) as H2.
  specialize (Iplus_comm b c) as H3. 
  specialize (I_compatible_eq_lt _ _ _ _ (Ieq_refl (c+b)) H3 H2) as H4.
  apply Ilt_irrefl in H4. contradiction. }
{ setoid_rewrite Qplus_comm. specialize (Iplus_comm b c) as H1.
  specialize (I_compatible_eq_lt _ _ _ _ H1 (I0_refl) Hd) as H2.
  exact (J6 _ _ _ Ha Hc Hb H2). }
{ specialize (J4 _ _ Hc Hb) as H1. specialize (Iplus_comm c b) as H2.
  specialize (Ieq_trans _ _ _ H2 Hd) as H3. apply Ineg_pos in H1.
  apply I0_opp in H3. apply Ieq_sym in H3. 
  specialize (Icont1 _ H3 H1) as H4. contradiction. }
{ specialize (Iplus_Ieq_compatible _ _ _ _ Hb Hc) as H1.
  assert (H2 : 0 + 0 == 0). { apply Iplus_0_r. }
  specialize (Ieq_trans _ _ _ H1 H2) as H3. apply Ieq_sym in H3.
  specialize (Icont1 _ H3 Hd) as H4. contradiction. }
{ specialize (Iplus_Ieq_compatible _ _ _ _ Hb Hc) as H1.
  assert (H2 : 0 + 0 == 0). { apply Iplus_0_r. }
  specialize (Ieq_trans _ _ _ H1 H2) as H3. apply Ineg_pos in Hd.
  apply I0_opp in H3. apply Ieq_sym in H3.
  specialize (Icont1 _ H3 Hd) as H4. contradiction. }
Qed.



Theorem Imult_plus_distr_r : 
forall a b c : I, a *_I (b + c) == (a *_I b) + (a *_I c).
Proof.
intros. destruct (I_dec a) as [[Ha|Ha]|Ha].
{ exact (Imult_plus_distr_r_prep _ _ _ Ha). }
{ specialize (Imult_opp_all a (b + c)) as H.
  specialize (Iopp_plus b c) as H1.
  specialize (Ieq_mult_compatible _ _ _ _ (Ieq_refl (- a)) H1) as H2.
  specialize (Ieq_trans _ _ _ H H2) as H3. apply Ineg_pos in Ha.
  specialize (Imult_plus_distr_r_prep (- a) (- b) (- c) Ha) as H4.
  specialize (Ieq_trans _ _ _ H3 H4) as H5.
  specialize (Imult_opp_all a b) as H6. apply Ieq_sym in H6.
  specialize (Imult_opp_all a c) as H7. apply Ieq_sym in H7.
  specialize (Iplus_Ieq_compatible _ _ _ _ H6 H7) as H8.
  exact (Ieq_trans _ _ _ H5 H8). }
{ specialize (Imult_0_l' a (b+c) Ha) as H1.
  specialize (Imult_0_l' a b Ha) as H2.
  specialize (Imult_0_l' a c Ha) as H3.
  specialize (Iplus_Ieq_compatible _ _ _ _ H2 H3) as H4.
  assert (H5 : 0 + 0 == 0). { apply Iplus_0_r. }
  specialize (Ieq_trans _ _ _ H4 H5) as H6. apply Ieq_sym in H6.
  exact (Ieq_trans _ _ _ H1 H6). }
Qed.

(* And above, we show two Lemmas :

Iplus_order_compatible : forall a b c : I, a < b -> a + c < b + c. 
Ipp : forall a b : I, 0 < a -> 0 < b -> 0 < a *_I b.

With this two Lemmas, we conclude that (I, +, *_I) is an ordered field. *)


