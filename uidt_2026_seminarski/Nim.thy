theory Nim
  imports Main "HOL.Bit_Operations"
begin

unbundle bit_operations_syntax

(* We prove that in the game Nim whenever the position has a nonzero "Nim sum"
   the player whose turn it is has a winning strategy. *)

type_synonym piles = "nat list"
type_synonym player = "bool"

(* A state is represented using the pile sizes and whose turn it is *)
record state = 
  piles :: piles
  turn :: player

(* A move uses a zero-based pile index and states how many tokens to remove from that pile *)
record move = 
  ind :: nat
  amount :: nat

(* A move is valid when the pile exists and the requested positive amount is
   no greater than that pile's current size. *)
definition valid_move :: "move \<Rightarrow> piles \<Rightarrow> bool" where
  "valid_move m ps =
     (ind m < length ps \<and>
      amount m \<ge> 1 \<and>
      amount m \<le> ps ! ind m)"

(* A valid move updates only the selected pile an invalid move returns None. *)
definition apply_move_to_piles :: "move \<Rightarrow> piles \<Rightarrow> piles option" where
  "apply_move_to_piles m ps =
     (if valid_move m ps
      then Some (ps[ind m := ps ! ind m - amount m])
      else None)"

(* Applying a valid move removes the given number of stones from the given pile 
and passes the turn to the other player. *)
definition apply_move :: "move \<Rightarrow> state \<Rightarrow> state option" where
  "apply_move m s =
     map_option (\<lambda>ps'. s\<lparr> piles := ps', turn := \<not> turn s \<rparr>)
       (apply_move_to_piles m (piles s))"

(* In the given state s the given player p has a winning strategy iff:
    - It is p's turn and p can make some move m that leads to a state s' 
      where p still has a winning strategy
    - It is the other player's turn and all moves the other player can make
      lead to a state s' where p still has a winning strategy. Note that in the case when no valid 
      moves exist for the other player the implication:
      (\<forall>m s'. apply_move m s = Some s' \<longrightarrow> has_winning_strategy s' p) holds vacuously 
      as the antecedent can not be satisfied. That is, if the other player has no valid moves p wins.
*)
inductive has_winning_strategy :: "state \<Rightarrow> player \<Rightarrow> bool" where
my_turn:
    "turn s = p \<Longrightarrow>
     apply_move m s = Some s' \<Longrightarrow>
     has_winning_strategy s' p \<Longrightarrow>
     has_winning_strategy s p"
| opponent_turn:
    "turn s \<noteq> p \<Longrightarrow>
     (\<forall>m s'. apply_move m s = Some s' \<longrightarrow> has_winning_strategy s' p) \<Longrightarrow>
     has_winning_strategy s p"

(* The "Nim sum" is defined as the bitwise XOR of all pile sizes. *)
primrec nim_sum :: "piles \<Rightarrow> nat" where
  "nim_sum [] = 0"
| "nim_sum (x # xs) = x XOR nim_sum xs"

(* k is the highest set bit of a positive number n: 
   k is the highest bit such that the bit at position k is set and
   all other positions j > k are not set *)
definition is_max_set_bit :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"is_max_set_bit n k \<longleftrightarrow> (n > 0) \<and> (bit n k) \<and> (\<forall>j>k. \<not>bit n j)"

lemma positive_number_has_some_bit_set:
  fixes n::nat
  assumes "n > 0"
  shows "\<exists>k. bit n k"
proof (rule ccontr)
  assume "\<not>(\<exists>k. bit n k)"
  then have all_zero: "\<forall>k. \<not>bit n k"
    by simp
  have "n=0" 
  proof(rule bit_eqI)
    fix k
    from all_zero have "bit n k = False"
      by simp
    also have "bit 0 k = False"
      by simp
    finally show "bit n k = bit 0 k"
      by simp
  qed
  with assms show False
    by simp
qed

lemma all_positive_number_bounded_above_by_pow2:
  fixes n::nat
  assumes "n > 0"
  shows "\<exists>p. 2^p > n"
  by (metis less_exp)

lemma positive_number_has_bound_on_set_bits:
  fixes n::nat
  assumes "n > 0"
  shows "\<exists>b. \<forall>b'>b. \<not>bit n b'"
  using all_positive_number_bounded_above_by_pow2
proof -
  obtain p where p_def: "2^p > n"
    by (metis all_positive_number_bounded_above_by_pow2 assms)
  then have "\<forall>p'>p. \<not>bit n p'"
  proof clarify
    fix p' :: nat
    assume larger_p': "p' > p"
    assume bit_p': "bit n p'"
    have larger_pow: "(2::nat)^p' \<ge> 2^p"
      using larger_p' by simp
    have n_lt_pow_p': "n \<le> 2^p'"
      using larger_pow p_def
      by linarith
    then have "\<not>bit n p'"
      using bit_nat_def larger_pow order.strict_trans2 p_def by fastforce
    then show False
      using bit_p' by simp       
  qed
  then show ?thesis using p_def
    by auto
qed

lemma max_set_bit_exists:
  fixes n::nat
  assumes "n > 0"
  shows "\<exists>b. is_max_set_bit n b"
  using positive_number_has_bound_on_set_bits is_max_set_bit_def positive_number_has_some_bit_set
proof -
  obtain b where b_def: "bit n b"
    using positive_number_has_some_bit_set assms by auto
  obtain bound where bound_def: "\<forall>b'>bound. \<not>bit n b'" 
    using positive_number_has_bound_on_set_bits assms by auto
  let ?S = "{k. bit n k}"
  have nonempty: "?S \<noteq> {}" using b_def by auto
  have finite_S: "finite ?S"
  proof (rule finite_subset[of ?S "{..bound}"])
    show "?S \<subseteq> {..bound}"
    proof
      fix k
      assume "k \<in> ?S"
      then have bit_k: "bit n k" by simp
      have "k \<le> bound"
        using bit_k bound_def linorder_le_less_linear by auto
      then show "k \<in> {..bound}" by simp
    qed
    show "finite {..bound}" by simp
  qed
  show ?thesis
    by (metis assms finite_S infinite_growing is_max_set_bit_def mem_Collect_eq
        nonempty)
qed

section \<open>Basic nim-sum facts\<close>

lemma nim_sum_append [simp]:
  "nim_sum (xs @ ys) = nim_sum xs XOR nim_sum ys"
  by (induction xs) (simp_all add: xor.assoc)

lemma nim_sum_update:
  assumes "i < length xs"
  shows "nim_sum (xs[i := x]) = nim_sum xs XOR xs ! i XOR x"
proof -
  let ?lx = "take i xs"
  let ?rx = "drop (Suc i) xs"

  have "nim_sum xs XOR xs ! i XOR x = nim_sum ?lx XOR xs ! i XOR nim_sum ?rx XOR xs ! i XOR x"
    by (metis assms id_take_nth_drop nim_sum.simps(2) nim_sum_append xor.commute xor.left_commute)
  also have "\<dots> = nim_sum ?lx XOR 0 XOR nim_sum ?rx XOR x"
    by (metis calculation xor.commute xor_self_eq xor.left_commute)
  also have "\<dots> = nim_sum ?lx XOR x XOR nim_sum ?rx"
    by (simp add: xor.commute)
  also have "\<dots> = nim_sum (?lx @ x # ?rx)"
    by simp
  finally show ?thesis
    by (simp add: assms upd_conv_take_nth_drop)
qed


lemma nim_sum_after_move:
  assumes move: "apply_move_to_piles m ps = Some ps'"
  shows
    "nim_sum ps' =
     nim_sum ps XOR ps ! ind m XOR (ps ! ind m - amount m)"
  using nim_sum_update
  by (metis apply_move_to_piles_def assms option.discI option.inject valid_move_def)

lemma nim_sum_assign_xor_zero:
  assumes i_lt: "i < length ps"
  shows "nim_sum (ps[i := ps ! i XOR nim_sum ps]) = 0"
  using nim_sum_update[OF i_lt, of "ps ! i XOR nim_sum ps"]
  by (simp add: xor.commute xor.left_commute)


section \<open>Bit lemmas\<close>

lemma less_from_highest_differing_bit:
  fixes a b :: nat
  assumes lower_at_k: "\<not> bit a k"
  assumes higher_at_k: "bit b k"
  assumes same_above: "\<forall>j>k. bit a j = bit b j"
  shows "a < b"
proof -
  have high_eq: "drop_bit (Suc k) a = drop_bit (Suc k) b"
  proof (rule bit_eqI)
    fix i
    show "bit (drop_bit (Suc k) a) i = bit (drop_bit (Suc k) b) i"
      using same_above
      by (simp add: bit_simps)
  qed
  have a_low: "take_bit (Suc k) a = take_bit k a"
    using lower_at_k 
    by (simp add: take_bit_Suc_from_most)

  have b_low: "take_bit (Suc k) b = (2::nat)^k + take_bit k b"
    using higher_at_k
    by (simp add: take_bit_Suc_from_most)
  
  have low_lt: "take_bit (Suc k) a < take_bit (Suc k) b"
    using a_low b_low
    by (simp add: trans_less_add1)
  have a_decomp:
    "a = push_bit (Suc k) (drop_bit (Suc k) a) + take_bit (Suc k) a"
    by (metis bits_ident)

  have b_decomp:
    "b = push_bit (Suc k) (drop_bit (Suc k) b) + take_bit (Suc k) b"
    by (metis bits_ident)

  have "push_bit (Suc k) (drop_bit (Suc k) a) + take_bit (Suc k) a
      < push_bit (Suc k) (drop_bit (Suc k) b) + take_bit (Suc k) b"
    using high_eq low_lt
    by simp

  then show ?thesis
    using a_decomp b_decomp
    by simp
qed

lemma highest_bit_xor_reduces:
  fixes a b :: nat
  assumes bit_a: "bit a k"
  assumes bit_b: "bit b k"
  assumes all_higher_bits_in_b_zero: "\<forall>j>k. \<not> bit b j"
  shows "a XOR b < a"
proof (rule less_from_highest_differing_bit[where k = k])
  show "\<not> bit (a XOR b) k"
    by (simp add: bit_a bit_b bit_xor_iff)

  show "bit a k"
    using bit_a .

  show "\<forall>j>k. bit (a XOR b) j = bit a j"
    using all_higher_bits_in_b_zero
    by (simp add: bit_xor_iff)
qed

lemma fold_xor_no_bit:
  assumes "\<forall>x \<in> set ps. \<not> bit x k"
  assumes acc_zero: "\<not> bit acc k"
  shows "\<not> bit (fold xor ps acc) k"
  using assms
proof (induction ps arbitrary: acc)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)

  have x_zero: "\<not> bit x k"
    using Cons.prems by simp

  have xs_zero: "\<forall>y \<in> set xs. \<not> bit y k"
    using Cons.prems by simp

  have acc'_zero: "\<not> bit (x XOR acc) k"
    using x_zero Cons.prems
    by (simp add: bit_xor_iff)

  show ?case
    using Cons.IH[OF xs_zero acc'_zero]
    by simp
qed

lemma nim_sum_bit_imp_pile_bit:
  assumes "bit (nim_sum ps) k"
  shows "\<exists>i < length ps. bit (ps ! i) k"
proof (rule ccontr)
  assume "\<not> (\<exists>i < length ps. bit (ps ! i) k)"

  then have no_bit: "\<forall>x \<in> set ps. \<not> bit x k"
    by (metis in_set_conv_nth)

  have "\<not> bit (nim_sum ps) k"
    using no_bit
  proof (induction ps)
    case Nil
    then show ?case by simp
  next
    case (Cons a ps)
    have a_zero: "\<not> bit a k" using no_bit
      by (simp add: Cons.prems)
    have ps_set_zero: "\<forall>x \<in> set ps. \<not> bit x k" 
      using Cons.prems by auto
    then have ps_zero: "\<not> bit (nim_sum ps) k"
      using Cons.IH by simp
    then show ?case using a_zero
      unfolding nim_sum_def
      by (simp add: bit_xor_iff)
  qed
  then show False
    using assms
    by contradiction
qed

lemma max_set_bit_above_zero:
  assumes "is_max_set_bit n k"
  shows "\<forall>j>k. \<not> bit n j"
  using is_max_set_bit_def assms by auto

section \<open>Existence of a zeroing move\<close>

lemma nonzero_nim_sum_has_assignment_zero:
  assumes nonzero: "nim_sum ps \<noteq> 0"
  shows "\<exists>i y. i < length ps \<and> y < ps ! i \<and> nim_sum (ps[i := y]) = 0"
proof -
  have nim_sum_ge_0: "nim_sum ps > 0" using assms by simp
  obtain k where k_def: "is_max_set_bit (nim_sum ps) k"
    using max_set_bit_exists[OF nim_sum_ge_0]
    by blast

  have bit_sum_k: "bit (nim_sum ps) k"
    using k_def is_max_set_bit_def
    by simp
    

  obtain i where i_good: "i < length ps \<and> bit (ps ! i) k"
    using nim_sum_bit_imp_pile_bit[OF bit_sum_k]
    by blast

  have higher_bits_sum_zero: "\<forall>j>k. \<not> bit (nim_sum ps) j"
    using max_set_bit_above_zero[OF k_def] .

  let ?y = "nim_sum ps XOR ps ! i"

  have bit_pile_i_k: "bit (ps ! i) k"
    using i_good
    by simp

  have y_less: "?y < ps ! i"
    using highest_bit_xor_reduces
      [OF bit_pile_i_k bit_sum_k higher_bits_sum_zero]
    by (simp add: xor.commute)

  have i_lt: "i < length ps"
    using i_good
    by blast

  have zero_after_update: "nim_sum (ps[i := ?y]) = 0"
    using nim_sum_assign_xor_zero[OF i_lt]
    by (simp add: xor.commute)

  show ?thesis
    using i_lt y_less zero_after_update
    by blast
qed

lemma nonzero_nim_sum_has_move_zero:
  assumes nonzero: "nim_sum ps \<noteq> 0"
  shows "\<exists>m ps'. apply_move_to_piles m ps = Some ps' \<and> nim_sum ps' = 0"
proof -
  obtain i y where
    i_lt: "i < length ps" and
    y_lt: "y < ps ! i" and
    zero: "nim_sum (ps[i := y]) = 0"
    using nonzero_nim_sum_has_assignment_zero[OF nonzero]
    by blast

  let ?m = "\<lparr> ind = i, amount = ps ! i - y \<rparr>"
  let ?ps' = "ps[i := y]"

  have valid: "valid_move ?m ps"
    using i_lt y_lt
    unfolding valid_move_def
    by simp

  have move: "apply_move_to_piles ?m ps = Some ?ps'"
    using valid y_lt
    unfolding apply_move_to_piles_def valid_move_def
    by simp

  show ?thesis
    using move zero
    by blast
qed

section \<open>Zero nim-sum positions are stable against winning moves\<close>

lemma zero_nim_sum_after_move_nonzero:
  assumes zero: "nim_sum ps = 0"
  assumes move: "apply_move_to_piles m ps = Some ps'"
  shows "nim_sum ps' \<noteq> 0"
proof -
  from move have valid: "valid_move m ps"
    unfolding apply_move_to_piles_def
    by (simp split: if_splits)

  then have amount_positive: "amount m > 0"
    unfolding valid_move_def
    by simp

  let ?xi = "ps ! ind m"
  let ?yi = "?xi - amount m"

  have xor_xi_yi: "nim_sum ps' = ?xi XOR ?yi"
    using nim_sum_after_move[OF move] zero
    by simp

  have "?xi \<noteq> ?yi"
    using amount_positive valid
    unfolding valid_move_def
    by force

  then have "?xi XOR ?yi \<noteq> 0"
    by (metis xor.assoc xor.right_neutral xor_self_eq)

  with xor_xi_yi show ?thesis
    by simp
qed


section \<open>Measure decreases after a valid move\<close>

lemma apply_move_reduces_piles_sum:
  assumes "apply_move_to_piles m ps = Some ps'"
  shows "sum_list ps' < sum_list ps"
  using assms
  unfolding apply_move_to_piles_def valid_move_def
  using sum_list_update
  by (smt (verit, best)
      One_nat_def
      add_diff_cancel_left'
      cancel_comm_monoid_add_class.diff_cancel
      diff_le_self
      elem_le_sum_list
      le_eq_less_or_eq
      not_less_eq
      option.discI
      option.inject
      order_less_le_trans
      ordered_cancel_comm_monoid_diff_class.diff_diff_right)


section \<open>Winning strategy theorem\<close>

theorem nonzero_nim_sum_has_winning_strategy:
  assumes nim_sum_not_zero: "nim_sum (piles s) \<noteq> 0"
  shows "has_winning_strategy s (turn s)"
  using nim_sum_not_zero
proof (induction s rule: measure_induct_rule[where f = "\<lambda>s. sum_list (piles s)"])
  case (less s)

  obtain m ps' where
    optimal_move_valid: "apply_move_to_piles m (piles s) = Some ps'" and
    after_move_nim_sum_zero: "nim_sum ps' = 0"
    using nonzero_nim_sum_has_move_zero[OF less.prems]
    by blast

  let ?s' = "s\<lparr>piles := ps', turn := \<not> turn s\<rparr>"

  have move_state: "apply_move m s = Some ?s'"
    using optimal_move_valid
    unfolding apply_move_def
    by simp

  show ?case
  proof (rule has_winning_strategy.my_turn)
    show "turn s = turn s"
      by simp

    show "apply_move m s = Some ?s'"
      using move_state .

    show "has_winning_strategy ?s' (turn s)"
    proof (rule has_winning_strategy.opponent_turn)
      show "turn ?s' \<noteq> turn s"
        by simp

      show "\<forall>m' s''.
        apply_move m' ?s' = Some s'' \<longrightarrow>
        has_winning_strategy s'' (turn s)"
      proof clarify
        fix m' :: move
        fix s'' :: state
        assume opp_move: "apply_move m' ?s' = Some s''"

        have opp_move_piles:
          "apply_move_to_piles m' ps' = Some (piles s'')"
          using opp_move
          unfolding apply_move_def
          by (auto split: option.splits)

        have nonzero_after_opp: "nim_sum (piles s'') \<noteq> 0"
          using zero_nim_sum_after_move_nonzero
            [OF after_move_nim_sum_zero opp_move_piles]
          by simp

        have turn_after_opp: "turn s'' = turn s"
          using opp_move
          unfolding apply_move_def
          by auto

        have smaller: "sum_list (piles s'') < sum_list (piles s)"
          using apply_move_reduces_piles_sum
          by (meson opp_move_piles optimal_move_valid order_less_trans)

        have win_s'': "has_winning_strategy s'' (turn s'')"
          using less.IH[OF smaller nonzero_after_opp]
          by simp

        show "has_winning_strategy s'' (turn s)"
          using win_s'' turn_after_opp
          by simp
      qed
    qed
  qed
qed

end