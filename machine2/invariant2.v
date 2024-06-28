(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

Require Export DistributedReferenceCounting.machine2.machine.
Require Export DistributedReferenceCounting.machine2.cardinal.
Require Export DistributedReferenceCounting.machine2.comm.

Unset Standard Proposition Elimination Names.

Section ROOTED.

Variable s0 : Site.

Definition rooted_fun (s1 s2 : Site) (m : Message) :=
  match m with
  | copy => if eq_site_dec s1 s0 then 1%Z else 0%Z
  | dec => if eq_site_dec s2 s0 then 1%Z else 0%Z
  | inc_dec s3 =>
      if eq_site_dec s3 s0
      then
       if eq_site_dec s2 owner then 1%Z else 0%Z
      else 0%Z
  end.

Definition rooted (s1 s2 : Site) (q : queue Message) :=
  reduce Message (rooted_fun s1 s2) q.


Definition sigma_rooted (bm : Bag_of_message) :=
  sigma2_table Site LS LS (queue Message) rooted bm.

End ROOTED.

Section ROOTED1.



Lemma sigma_rooted_post_message :
 forall (m : Message) (s0 s1 s2 : Site) (b : Bag_of_message),
 s0 <> owner ->
 sigma_rooted s0 (Post_message Message m b s1 s2) =
 (sigma_rooted s0 b + rooted_fun s0 s1 s2 m)%Z.
Proof. (* This proof was automatically repaired. *)
  unfold sigma_rooted in |- *.
  unfold Post_message in |- *.
  unfold change_queue in |- *.
  intros.
  rewrite sigma_table2_change.
  simpl in |- *.
  auto with *.
  apply finite_site.
  apply finite_site.
Qed.


Lemma rooted_first_out :
 forall (s0 s1 s2 : Site) (q : queue Message) (m : Message),
 first Message q = value Message m ->
 rooted s0 s1 s2 (first_out Message q) =
 (rooted s0 s1 s2 q - rooted_fun s0 s1 s2 m)%Z.
Proof.
  intros.
  unfold rooted in |- *.
  apply reduce_first_out.
  auto.
Qed.

Lemma sigma_rooted_collect_message :
 forall (m : Message) (s0 s1 s2 : Site) (b : Bag_of_message),
 first Message (b s1 s2) = value Message m ->
 s0 <> owner ->
 sigma_rooted s0 (Collect_message Message b s1 s2) =
 (sigma_rooted s0 b - rooted_fun s0 s1 s2 m)%Z.
Proof. (* This proof was automatically repaired. *)
  unfold sigma_rooted, Collect_message, change_queue in |- *.
  intros.
  rewrite sigma_table2_change.
  rewrite (rooted_first_out s0 s1 s2 (b s1 s2) m).
  simpl in |- *.
  auto with *.
  auto.
  apply finite_site.
  apply finite_site.
Qed.

Lemma rooted_fun_positive_or_null :
 forall (s0 x y : Site) (a : Message), (rooted_fun s0 x y a >= 0)%Z.
Proof. (* This proof was automatically repaired. *)
  intros.
  unfold rooted_fun in |- *.
  elim a.
  case (eq_site_dec y s0).
  intro; auto with *.
  intro; auto with *.
  intro.
  case (eq_site_dec s s0).
  case (eq_site_dec y owner).
  intros; auto with *.
  intros; auto with *.
  intros; auto with *.
  case (eq_site_dec x s0).
  intros; auto with *.
  intros; auto with *.
Qed.

Lemma rooted_positive_or_null :
 forall (s0 x y : Site) (q : queue Message), (rooted s0 x y q >= 0)%Z.
Proof.
  intros.
  unfold rooted in |- *.
  apply reduce_positive_or_null.
  intro.
  apply rooted_fun_positive_or_null.
Qed.


End ROOTED1.

Section INVARIANT2.

Lemma invariant2_init :
 forall s0 : Site, st config_init s0 = sigma_rooted s0 (bm config_init).
Proof.
  intros.
  simpl in |- *.
  unfold send_init, sigma_rooted, bag_init in |- *.
  unfold sigma2_table in |- *.
  unfold sigma_table in |- *.
  unfold Z_id in |- *.
  unfold rooted in |- *.
  simpl in |- *.
  rewrite sigma_null.
  rewrite sigma_null.
  auto.
Qed.

Lemma invariant2_ind :
 forall s0 : Site,
 s0 <> owner ->
 forall (c : Config) (t : class_trans c),
 legal c ->
 st c s0 = sigma_rooted s0 (bm c) ->
 st (transition c t) s0 = sigma_rooted s0 (bm (transition c t)).
Proof. (* This proof was automatically repaired. *)
  simple induction t.

  (* 1 *)

  intros; simpl in |- *.
  rewrite sigma_rooted_post_message.
  unfold Inc_send_table in |- *.
  unfold rooted_fun in |- *.
  case (eq_site_dec s1 s0).
  intro; rewrite e.
  unfold update_table in |- *; rewrite here.
  auto with *.
  intro; unfold update_table in |- *; rewrite elsewhere.
  auto with *.
  auto.
  auto.

  (* 2 *)
  
  intros; simpl in |- *.
  rewrite sigma_rooted_collect_message with (m := dec).
  unfold Dec_send_table in |- *.
  unfold rooted_fun in |- *.
  case (eq_site_dec s2 s0).
  intro; rewrite e0.
  unfold update_table in |- *; rewrite here.
  auto with *.
  intros; unfold update_table in |- *; rewrite elsewhere.
  auto with *.
  auto.
  auto.
  auto.

  (* 3 *)
  
  intros; simpl in |- *.
  rewrite sigma_rooted_post_message.
  rewrite sigma_rooted_collect_message with (m := inc_dec s3).
  unfold Inc_send_table, rooted_fun in |- *.
  unfold update_table in |- *; rewrite elsewhere.
  case (eq_site_dec s3 s0).
  case (eq_site_dec owner owner).
  intros; auto with *.
  intro; elim n.
  auto.
  intros; auto with *.
  auto.
  auto.
  auto.
  auto.

  (* 4 *)
  
  intros; simpl in |- *.
  rewrite sigma_rooted_post_message.
  rewrite sigma_rooted_collect_message with (m := copy).
  unfold rooted_fun in |- *.
  case (eq_site_dec s1 s0).
  intro; auto with *.
  intro; auto with *.
  auto.
  auto.
  auto.


  (* 5 *)
  
  intros; simpl in |- *.
  rewrite sigma_rooted_collect_message with (m := copy).
  unfold rooted_fun in |- *.
  rewrite case_ineq.
  auto with *.
  auto.
  auto.
  auto.

  (* 6 *)
  
  intros; simpl in |- *.
  rewrite sigma_rooted_post_message.
  rewrite sigma_rooted_collect_message with (m := copy).
  unfold rooted_fun in |- *.
  case (eq_site_dec s1 s0).
  rewrite case_eq.
  intro; auto with *.
  intros; auto with *.
  auto.
  auto.
  auto.

  (* 7 *)
  
  intros; simpl in |- *.
  rewrite sigma_rooted_post_message.
  unfold rooted_fun in |- *.
  rewrite case_ineq.
  auto with *.  
  auto.
  auto.
Qed.


Lemma invariant2 :
 forall (c0 : Config) (s0 : Site),
 legal c0 -> s0 <> owner -> st c0 s0 = sigma_rooted s0 (bm c0).

Proof.
  intros.
  elim H.
  apply invariant2_init.
  intros.
  apply invariant2_ind.
  auto.
  auto.
  auto.
Qed.


Lemma positive_st :
 forall (c : Config) (s0 s5 : Site),
 s0 <> owner ->
 legal c -> In_queue Message (inc_dec s0) (bm c s5 owner) -> (st c s0 > 0)%Z.
Proof. (* This proof was automatically repaired. *)
  intros c s0 s5 H HA.
  rewrite invariant2.
  unfold sigma_rooted in |- *.
  intros.
  apply sigma2_strictly_positive with (x := s5) (y := owner).
  auto.
  exact eq_site_dec.
  
  apply in_s_LS.
  apply in_s_LS.
  intros.
  unfold rooted in |- *.
  intros.
  simpl in |- *.
  intros.
  simpl in |- *.
  apply reduce_positive_or_null.
  intro.
  apply rooted_fun_positive_or_null.
  
  generalize H0.
  elim (bm c s5 owner).
  simpl in |- *; intuition.
  
  intros.
  generalize H2.
  case d.
  simpl in |- *.
  intros.
  elim H3.
  intro; discriminate.
  
  intro.
  generalize (H1 H4).
  intro.
  case (eq_site_dec owner s0).
  intros; auto with *.
  
  intros; auto with *.
  
  simpl in |- *.
  intros.
  case (eq_site_dec s s0).
  intro.
  case (eq_site_dec owner owner).
  intro.
  generalize (rooted_positive_or_null s0 s5 owner q).
  intro.
  auto with *.
  
  intro.
  elim n; auto.
  
  intro.
  elim H3.
  intro; elim n.
  inversion H4.
  auto.
  
  intro.
  generalize (H1 H4).
  intro.
  auto with *.
  
  simpl in |- *.
  intro.
  elim H3.
  intro; discriminate.
  
  intro.
  generalize (H1 H4).
  intro.
  case (eq_site_dec s5 s0).
  intro; auto with *.
  
  intro; auto with *.
  
  auto.
  
  auto.
Qed.






End INVARIANT2.
