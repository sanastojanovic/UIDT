theory mi19425_Uros_Ljubisavljevic
  imports Main
begin

text\<open> Algebra A4 -- https://www.imo-official.org/problems/IMO2010SL.pdf \<close>

\<comment>\<open> Sequence definiton \<close>
fun seqX :: "nat \<Rightarrow> int" where
"seqX n = ( if (n = 0) then 0
            else if (n = 1) then 1
            else if (n mod 2 = 0) then (-seqX (n div 2))
            else ((-1)^((n + 3) div 2)) * (seqX ((n + 1) div 2)))"

\<comment>\<open> S_n definition \<close>
primrec sumFst :: "nat \<Rightarrow> int" where
"sumFst 0 = 0" |
"sumFst (Suc n) = seqX (Suc n) + sumFst n"

definition sumFstS :: "nat \<Rightarrow> int" where
"sumFstS n = (\<Sum>i::nat=0..n. seqX i)"

lemma sumFst_eq_sumFstS:
  fixes n :: nat
  shows "sumFst n = sumFstS n"
proof(induction n)
  case 0
  then show ?case using sumFstS_def by simp
next
  case (Suc n)
  then show ?case
  proof-
    have "sumFst (Suc n) = sumFst n + seqX (Suc n)" by simp
    also have "\<dots> = sumFstS n + seqX (Suc n)" using Suc by simp
    also have "\<dots> = sumFstS (Suc n)" using sumFstS_def by simp
    finally show ?thesis .
  qed
qed

\<comment>\<open> ======== Observations: ======= \<close>

\<comment>\<open> Observation (1) \<close>
lemma eq1_1:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "seqX (4*k-3) = seqX (2*k-1)"
proof-
  have "odd (4*k-3)" using assms by auto
  then have "seqX (4*k-3) = ((-1)^(((4*k-3) + 3) div 2)) * (seqX (((4*k-3) + 1) div 2))" using seqX.simps 
    by (metis (no_types, lifting) add_self_div_2 even_iff_mod_2_eq_zero even_zero minus_one_mult_self
        nat_1_add_1 neg_one_even_power numeral_Bit0 numeral_plus_numeral odd_even_add semiring_norm(4))
  also have "\<dots> = ((-1)^(2*k)) * (seqX ((2*k-1)))"
    by (smt (verit, del_insts) ab_semigroup_add_class.add_ac(1) add.commute add_diff_cancel_left' 
        add_self_div_2 assms distrib_left_numeral less_eqE mult.commute mult.left_commute mult_2 
        nat_1_add_1 numeral_Bit0 numeral_Bit1)
  also have "\<dots> = seqX (2*k-1)" by simp
  finally show ?thesis .
qed

lemma eq1_2:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "-seqX (4*k-2) = seqX (2*k-1)"
proof-
  have "-seqX (4*k-2) = -seqX (2*(2*k-1))" using assms
    by (simp add: right_diff_distrib')
  also have "\<dots> = -(-seqX (2*k-1))" using seqX.simps by simp
  also have "\<dots> = seqX (2*k-1)" by simp
  finally show ?thesis .
qed

lemma eq1_2_1:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "-seqX (4*k-2) = seqX (4*k-3)" "seqX (4*k-2) = -seqX (4*k-3)"
  using eq1_1 eq1_2 assms apply simp
  by (smt (verit, del_insts) assms eq1_1 eq1_2)

lemma eq2_1:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "seqX (4*k-1) = seqX (4*k)"
proof-
  have "odd (4*k-1)" using assms by auto
  then have "seqX (4*k-1) = ((-1)^(((4*k-1) + 3) div 2)) * (seqX (((4*k-1) + 1) div 2))" using seqX.simps
    by (metis (no_types, lifting) add_self_div_2 even_iff_mod_2_eq_zero even_zero minus_one_mult_self
        nat_1_add_1 neg_one_even_power numeral_Bit0 numeral_plus_numeral odd_even_add semiring_norm(4))
  also have "\<dots> = ((-1)^((4*k + 2) div 2)) * (seqX ((4*k) div 2))" by simp
  also have "\<dots> = ((-1)^(2*k + 1)) * (seqX (2*k))" by simp
  also have "\<dots> = -seqX (2*k)" by simp
  also have "\<dots> = seqX (4*k)" by simp
  finally show ?thesis .
qed

lemma eq2_2:
  fixes k :: nat
  assumes "k > 0"
  shows "-seqX (2*k) = seqX (4*k)"
  by simp
  
lemma eq2_3:
  fixes k :: nat
  assumes "k > 0"
  shows "-seqX (2*k) = seqX (k)"
  by simp


(* obs (2) helpers *)
lemma sum4SetSplit:
  shows "sum seqX {n..n+3} = seqX (n) + seqX (n+1) + seqX (n+2) + seqX (n+3)"
proof-
  have "sum seqX {n..n+3} = seqX (n) + sum seqX {(n + 1)..(n + 3)}"
    by (simp add: atLeastSucAtMost_greaterThanAtMost sum.head)
  also have "\<dots> =  seqX (n) + seqX (n+1) + seqX (n+2) + seqX (n+3)"
    by (simp add: numeral_Bit1)
  finally show ?thesis .
qed

lemma sum4SetSplit':
  assumes "i \<ge> 1"
  shows "sum seqX {4 * i - 3..4 * i} = seqX (4 * i - 3) + seqX (4 * i - 2) + seqX (4 * i - 1) + seqX (4 * i)"
  using assms sum4SetSplit[of "4*i-3"]
  by (smt (z3) add.assoc add.commute diff_add_inverse2 distrib_left_numeral le_add_diff_inverse 
      mult.commute mult_2_right numeral_Bit0 numeral_Bit1 numerals(1))

\<comment>\<open> Observation (2) \<close>
lemma S4k_eq_2Sk:
  fixes n k :: nat
  assumes "n = 4*k" "k \<ge> 1"
  shows "sumFst n = 2 * sumFst (n div 4)"
proof-
  have "n mod 4 = 0" using assms by simp
  have "n \<ge> 4" using assms by simp
  have "sumFst n = sum seqX {1..4*k}" using sumFst.simps
    by (simp add: sum.atLeast_Suc_atMost sumFstS_def sumFst_eq_sumFstS assms)
  also have "\<dots> = sum (\<lambda>i. sum seqX {4*i-3..4*i}) {1..k}" using assms(2)
  proof(induction k rule: nat_induct_at_least)
    case base
    then show ?case by simp
  next
    case (Suc k)
    then show ?case
    proof-
      have "sum seqX {1..4 * Suc k} = sum seqX {1..4*k} + sum seqX {4*k+1..4*Suc k}" 
        by (metis Suc_eq_plus1 Suc_eq_plus1_left add_mult_distrib2 le_add1 sum.ub_add_nat)
      also have "\<dots> =  (\<Sum>i = 1..Suc k. sum seqX {4 * i - 3..4 * i})" using sum4SetSplit'[of "Suc k"] Suc by simp
      finally show "sum seqX {1..4 * Suc k} = (\<Sum>i = 1..Suc k. sum seqX {4 * i - 3..4 * i})" .
    qed
  qed
  also have "\<dots> = (\<Sum>i::nat=1..(n div 4). (seqX (4*i-3)) + (-seqX (4*i-3)) + (seqX (4*i-1)) + (seqX (4*i)))"
    using eq1_2_1 assms sum4SetSplit' by simp
  also have "\<dots> = (\<Sum>i::nat=1..(n div 4). (seqX (4*i-1)) + (seqX (4*i)))" by simp
  also have "\<dots> = (\<Sum>i::nat=1..(n div 4). (seqX (4*i)) + (seqX (4*i)))" using eq2_1 by simp
  also have "\<dots> = (\<Sum>i::nat=1..(n div 4). 2*(seqX i))" using eq2_2 eq2_3 by simp
  also have "\<dots> = 2 * (\<Sum>i::nat=1..(n div 4). (seqX i))" by (simp add: sum_distrib_left)
  also have "\<dots> = 2 * sumFst (n div 4)" by (simp add: sum.atLeast_Suc_atMost sumFstS_def sumFst_eq_sumFstS)
  finally show ?thesis .
qed


\<comment>\<open> Observation (3) \<close>
lemma S4kp2_eq_S4k:
  fixes n k :: nat
  assumes "n = 4*k" "k \<ge> 1"
  shows "sumFst (n+2) = sumFst n"
proof-
  have "sumFst (n+2) = sumFst n + seqX (4*k+1) + seqX (4*k+2)" using assms by simp
  also have "\<dots> = sumFst n + seqX (4*(k+1)-3) + seqX (4*(k+1)-2)" by simp
  also have "\<dots> = sumFst n + seqX (4*(k+1)-3) + (-seqX (4*(k+1)-3))" 
    using eq1_2_1 le_add2 by presburger
  also have "\<dots> = sumFst n" by simp
  finally show ?thesis .
qed

(* helper *)
lemma seqXimage:
  fixes n :: nat
  assumes "n \<ge> 1"
  shows "(seqX n = -1) \<or> (seqX n = 1)"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof(induction n rule: seqX.induct)
    case (1 m)
    then show ?case
    proof(cases "m mod 2 = 0")
      case True
      then show ?thesis
      proof(cases "seqX (Suc (m div 2)) = -1")
        case True
        then show ?thesis
        proof-
          assume "seqX (Suc (m div 2)) = -1"
          have "(Suc m) mod 2 = 1" using \<open>m mod 2 = 0\<close> by auto
          then have "seqX (Suc m) = (-1) ^ (((Suc m) + 3) div 2) * seqX ((Suc m + 1) div 2)"
            using seqX.simps \<open>seqX (Suc (m div 2)) = - 1\<close>
            by (metis Suc_1 add_self_div_2 bits_mod_0 div2_Suc_Suc div_by_Suc_0
                not_mod2_eq_Suc_0_eq_0 one_add_one one_neq_neg_one)
          also have "\<dots> = (-1) ^ (((Suc m) + 3) div 2) * seqX (Suc (Suc m) div 2)" by simp
          also have "\<dots> = (-1) ^ (((Suc m) + 3) div 2) * seqX (Suc (m div 2))" using div2_Suc_Suc by simp
          also have "\<dots> = (-1) ^ (((Suc m) + 3) div 2) * (-1)" using \<open>seqX (Suc (m div 2)) = -1\<close> by simp
          also have "\<dots> = (-1) ^ (((m + 4) div 2) + 1)"
            by (metis Suc_numeral add_One_commute add_Suc_shift power_add power_one_right 
                semiring_norm(2) semiring_norm(4))
          finally have "seqX (Suc m) = (-1) ^ (((m + 4) div 2) + 1)" .
          then show ?thesis
          proof(cases "even (((m + 4) div 2) + 1)")
            case True
            then show ?thesis using \<open>seqX (Suc m) = (-1) ^ (((m + 4) div 2) + 1)\<close>
              by (metis neg_one_even_power)
          next
            case False
            then show ?thesis using \<open>seqX (Suc m) = (-1) ^ (((m + 4) div 2) + 1)\<close>
              by (metis neg_one_odd_power)
          qed
        qed
      next
        case False
        then show ?thesis
        proof-
          assume "seqX (Suc (m div 2)) \<noteq> - 1"
          from 1(3) \<open>m mod 2 = 0\<close> have "m \<noteq> 0" "m \<noteq> 1" "1 \<le> m div 2" by auto
          with 1(4) have "seqX (m div 2) = - 1 \<or> seqX (m div 2) = 1" 
            using seqX.simps True by fastforce
          with 1(1) \<open>m \<noteq> 0\<close> \<open>m \<noteq> 1\<close> \<open>1 \<le> m div 2\<close> \<open>m mod 2 = 0\<close>
          have "seqX (Suc (m div 2)) = - 1 \<or> seqX (Suc (m div 2)) = 1" by simp
          with \<open>seqX (Suc (m div 2)) \<noteq> - 1\<close> have "seqX (Suc (m div 2)) = 1" by simp
          
          have "seqX (Suc m) = (-1) ^ (((Suc m) + 3) div 2) * seqX ((Suc m + 1) div 2)" 
            using seqX.simps 1 True
            by (smt (verit, best) bits_one_mod_two_eq_one mod_Suc_eq not_numeral_le_zero 
                numeral_1_eq_Suc_0 numerals(1) old.nat.inject power_0 power_0_Suc)
          also have "\<dots> = (-1) ^ (((Suc m) + 3) div 2) * seqX (Suc (m div 2))"
            using Suc_eq_plus1 div2_Suc_Suc by presburger
          also have "\<dots> = (-1) ^ (m div 2 + 2) * seqX (Suc (m div 2))" by (simp add: numeral_Bit1)
          also have "\<dots> = (-1) ^ (m div 2 + 2)" using \<open>seqX (Suc (m div 2)) = 1\<close> by simp
          finally have "seqX (Suc m) = (-1) ^ (m div 2 + 2)" .
          then show ?thesis using seqX.simps
            by (metis minus_one_mult_self power2_eq_1_iff power2_eq_square)
        qed
      qed
    next
      case False
      then show ?thesis
      proof(cases "seqX ((m + 1) div 2) = - 1")
        case True
        then show ?thesis
        proof-
          assume "seqX ((m + 1) div 2) = - 1"
          have "seqX (Suc m) = 1" using \<open>m mod 2 \<noteq> 0\<close> seqX.simps \<open>seqX ((m + 1) div 2) = - 1\<close>
            by (metis Suc_1 Suc_eq_plus1 Zero_not_Suc add.inverse_inverse mod_Suc not_mod_2_eq_1_eq_0)
          then show ?thesis by simp
        qed
      next
        case False
        then show ?thesis 
        proof-
          assume "seqX ((m + 1) div 2) \<noteq> - 1"
          from 1 \<open>m mod 2 \<noteq> 0\<close> have "m \<noteq> 0" "1 \<le> (m + 1) div 2" by auto
          then show ?thesis
          proof(cases "m = 1")
            case True
            then show ?thesis by simp
          next
            case False
            then show ?thesis
            proof- 
              from \<open>m mod 2 \<noteq> 0\<close> seqX.simps have "seqX m = (- 1) ^ ((m + 3) div 2) * seqX ((m + 1) div 2)" by simp
              with 1(4) have "(- 1) ^ ((m + 3) div 2) * seqX ((m + 1) div 2) = -1 \<or> (- 1) ^ ((m + 3) div 2) * seqX ((m + 1) div 2) = 1" by simp
              then have 2: "seqX ((m + 1) div 2) = - 1 \<or> seqX ((m + 1) div 2) = 1"
                by (smt (verit, best) mult_minus_left zmult_eq_1_iff)
              with \<open>seqX ((m + 1) div 2) \<noteq> - 1\<close> have "seqX ((m + 1) div 2) = 1" by simp
              have "seqX (Suc m) = seqX (m + 1)" by simp
              also have "\<dots> = -seqX ((m + 1) div 2)" using seqX.simps \<open>m mod 2 \<noteq> 0\<close>
                by (smt (verit, best) add_self_mod_2 bits_div_0 mod_add_left_eq not_mod_2_eq_0_eq_1 one_mod_two_eq_one)
              also have "\<dots> = -1" using \<open>seqX ((m + 1) div 2) = 1\<close> by simp
              finally have "seqX (Suc m) = -1" .
              then show ?thesis by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

\<comment>\<open> Observation (4) \<close>
lemma Sn_eq_n_mod2:
  fixes n :: nat
  assumes "n \<ge> 1"
  shows "(sumFst n) mod 2 = int (n mod 2)"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof-
    have "sumFst (Suc n) mod 2 = (sumFst n + seqX (Suc n)) mod 2" unfolding sumFst_def
      by (metis add.commute old.nat.simps(7))
    also have "\<dots> = ((sumFst n) mod 2 + (seqX (Suc n)) mod 2) mod 2"
      by (metis mod_add_eq)
    also have "\<dots> = (int (n mod 2) + (seqX (Suc n)) mod 2) mod 2" using Suc
      by presburger
    also have "\<dots> = (int (n mod 2) + 1) mod 2" using seqXimage
      by (metis Suc.hyps le_SucI minus_1_mod_2_eq one_mod_two_eq_one)
    also have "\<dots> = int (Suc n mod 2) mod 2"
      by (metis Suc_eq_plus1_left bits_mod_0 int_Suc mod_Suc mod_self of_nat_0 of_nat_eq_1_iff one_add_one)
    also have "\<dots> = int (Suc n mod 2)" by simp
    finally show ?thesis .
  qed
qed

(* helper *)
lemma sumFst_four:
  assumes "i \<le> 4"
  shows "0 \<le> sumFst i"
proof-
  have "\<forall>i \<le> 0. sumFst i \<ge> 0" by simp
  
  have "sumFst 1 \<ge> 0" by simp
  with \<open>\<forall>i \<le> 0. sumFst i \<ge> 0\<close> have "\<forall>i \<le> 1. sumFst i \<ge> 0"
    by (metis less_one nat_less_le verit_comp_simplify1(3))
  
  have "sumFst 2 \<ge> 0" unfolding sumFst_def by simp
  with \<open>\<forall>i \<le> 1. sumFst i \<ge> 0\<close> have "\<forall>i \<le> 2. sumFst i \<ge> 0"
    by (metis Suc_1 le_SucE)
  
  have "sumFst 3 \<ge> 0" unfolding sumFst_def by simp
  with \<open>\<forall>i \<le> 2. sumFst i \<ge> 0\<close> have "\<forall>i \<le> 3. sumFst i \<ge> 0"
    by (metis eval_nat_numeral(3) le_Suc_eq)

  have "sumFst 4 \<ge> 0" unfolding sumFst_def by simp
  with \<open>\<forall>i \<le> 3. 0 \<le> sumFst i\<close> assms show ?thesis using sumFst.simps
    by (metis Suc_numeral le_SucE semiring_norm(2) semiring_norm(8))
qed

lemma Si_gt_0_4k:
  fixes k :: nat
  assumes "1 \<le> k"
  shows "\<forall>i\<le>4*k. 0 \<le> sumFst i"
  using assms
proof(induction k rule: nat_induct_at_least)
  case base
  then show ?case using sumFst_four by simp
next
  case (Suc n)
  then show ?case
  proof-
    (* splitting the problem *)
    (* goal \<longleftrightarrow> 10 \<and> 11 \<and> 12 \<and> 13 \<and> 14 *)
    have 1: "(\<forall>i \<le> 4 * Suc n. 0 \<le> sumFst i) \<longleftrightarrow> 
          (\<forall>i \<le> 4*n. 0 \<le> sumFst i) \<and>
          (0 \<le> sumFst (4*n+1)) \<and> 
          (0 \<le> sumFst (4*n+2)) \<and> 
          (0 \<le> sumFst (4*n+3)) \<and>
          (0 \<le> sumFst (4*n+4))"
    proof
      assume "(\<forall>i \<le> 4 * Suc n. 0 \<le> sumFst i)"
      show "(\<forall>i \<le> 4*n. 0 \<le> sumFst i) \<and> 
          (0 \<le> sumFst (4*n+1)) \<and> 
          (0 \<le> sumFst (4*n+2)) \<and> 
          (0 \<le> sumFst (4*n+3)) \<and>
          (0 \<le> sumFst (4*n+4))"
      proof
        show "\<forall>i\<le>4 * n. 0 \<le> sumFst i" using \<open>(\<forall>i \<le> 4 * Suc n. 0 \<le> sumFst i)\<close> by simp
      next
        show "(0 \<le> sumFst (4*n+1)) \<and> 
          (0 \<le> sumFst (4*n+2)) \<and> 
          (0 \<le> sumFst (4*n+3)) \<and>
          (0 \<le> sumFst (4*n+4))" 
          using \<open>(\<forall>i \<le> 4 * Suc n. 0 \<le> sumFst i)\<close>
        proof-
          from \<open>(\<forall>i \<le> 4 * Suc n. 0 \<le> sumFst i)\<close> have "(\<forall>i \<le> 4*n + 4. 0 \<le> sumFst i)" by simp
          then show "(0 \<le> sumFst (4*n+1)) \<and> 
          (0 \<le> sumFst (4*n+2)) \<and> 
          (0 \<le> sumFst (4*n+3)) \<and>
          (0 \<le> sumFst (4*n+4))" 
            by (metis add_2_eq_Suc add_Suc_right nat_add_left_cancel_le numeral_1_eq_Suc_0 
                numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 numerals(1) one_le_numeral)
        qed
      qed
    next
      assume pp: "(\<forall>i \<le> 4*n. 0 \<le> sumFst i) \<and> 
          (0 \<le> sumFst (4*n+1)) \<and> 
          (0 \<le> sumFst (4*n+2)) \<and> 
          (0 \<le> sumFst (4*n+3)) \<and>
          (0 \<le> sumFst (4*n+4))"
      show "(\<forall>i \<le> 4 * Suc n. 0 \<le> sumFst i)" 
      proof-
        have "(\<forall>i \<le> 4 * Suc n. 0 \<le> sumFst i) \<longleftrightarrow> (\<forall>i \<le> 4 * n + 4. 0 \<le> sumFst i)" by auto
        from pp have "(\<forall>i \<le> 4 * n + 4. 0 \<le> sumFst i)"
        proof-
          have \<open>(0 \<le> sumFst (4*n+4))\<close> using pp by blast
          have "(\<forall>i \<le> 4*n + 3. 0 \<le> sumFst i)" using pp
            by (metis Suc3_eq_add_3 Suc_eq_plus1 add.commute add_2_eq_Suc' le_SucE)
          with \<open>(0 \<le> sumFst (4*n+4))\<close> show "(\<forall>i \<le> 4 * n + 4. 0 \<le> sumFst i)"
            by (metis add.commute add_Suc le_antisym not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3
                numeral_Bit0 numerals(1) plus_1_eq_Suc)
        qed
        with \<open>(\<forall>i \<le> 4 * Suc n. 0 \<le> sumFst i) \<longleftrightarrow> (\<forall>i \<le> 4 * n + 4. 0 \<le> sumFst i)\<close> 
        show "(\<forall>i \<le> 4 * Suc n. 0 \<le> sumFst i)" by simp
      qed   
    qed

    (* === 10 === *)
    have 10: "(\<forall>i \<le> 4*n. 0 \<le> sumFst i)" using Suc(2) by simp

    (* === 14 === *)
    have 14: "0 \<le> sumFst (4*n+4)"
    proof-
      have "((4*n+4) div 4) \<le> 4*n" using Suc(1) by simp
      then have "n+1 \<le> 4*n" by simp
      with Suc have "0 \<le> 2*sumFst (n+1)" by (smt (z3))
      also have "\<dots> = sumFst (4*(n+1))"
        by (metis S4k_eq_2Sk le_add2 nonzero_mult_div_cancel_left zero_neq_numeral)
      also have "\<dots> = sumFst (4*n+4)" by (simp add: algebra_simps)
      finally show "0 \<le> sumFst (4*n+4)" .
    qed

    (* === 13 === *)
    have 13: "0 \<le> sumFst (4*n+3)"
    proof-
      have "sumFst (4*n+3) = sumFst (4*n + 2) + seqX (4*n + 3)" by (simp add: numeral_3_eq_3)
      also with \<open>1 \<le> n\<close> have "\<dots> = sumFst (4*n) + seqX (4*n + 3)" using S4kp2_eq_S4k
        by simp
      also have "\<dots> = sumFst (4*n) + seqX (4*(n+1) - 1)" by (simp add: algebra_simps)
      also have "\<dots> = sumFst (4*n) + seqX (n + 1)" using eq2_1 eq2_2 eq2_3
        by (metis add_gr_0 le_add2 less_numeral_extra(1))
      also have "\<dots> = 2 * sumFst n + seqX (n + 1)" using S4k_eq_2Sk using Suc(1) by auto
      also have "\<dots> = 2 * sumFst n + sumFst (n + 1) - sumFst n" by simp
      also have "\<dots> = sumFst n + sumFst (n + 1)" by simp
      finally have "sumFst (4*n+3) = sumFst n + sumFst (n + 1)" .
      
      have "(n+1) \<le> 4*n" using Suc(1) by simp
      have "n \<le> 4*n" by simp
      then have "sumFst n \<ge> 0" using Suc by simp
      moreover with \<open>(n+1) \<le> 4*n\<close> have "sumFst (n+1) \<ge> 0" using Suc by blast
      ultimately have "sumFst n + sumFst (n + 1) \<ge> 0" by linarith
      with \<open>sumFst (4*n+3) = sumFst n + sumFst (n + 1)\<close> show "0 \<le> sumFst (4*n+3)" by simp
    qed

    (* === 12 === *)
    have 12: "0 \<le> sumFst (4*n + 2)"
    proof-
      have "sumFst (4*n + 2) = sumFst (4*n)"
        using S4kp2_eq_S4k Suc(1) by simp
      also have "\<dots> \<ge> 0" using Suc by simp
      finally show "0 \<le> sumFst (4*n + 2)" by simp
    qed

    (* === 11 === *)
    have 11: "0 \<le> sumFst (4*n+1)"
    proof(cases "n mod 2 = 0")
      case True
      then show ?thesis
      proof-
  
        assume "n mod 2 = 0"
        then have "((-1::int)^((2*(n + 1) + 2) div 2)) = 1"
        proof-
          have "even ((2*(n + 1) + 2) div 2)" using True by fastforce
          then show "(-1::int)^((2*(n + 1) + 2) div 2) = 1" by simp
        qed

        have "seqX (4 * n + 1) = seqX (n + 1)"
        proof-
          from \<open>n mod 2 = 0\<close> have "(n+1) mod 2 = 1" by auto
          then have "(2*(n+1) -1) mod 2 = 1" by auto
          have "seqX (4*n + 1) = seqX (4*(n+1) - 3)" by (simp add: algebra_simps)
          also have "\<dots> = seqX (2*(n+1) - 1)" using eq1_1[where k = "n+1"] by simp
          also with \<open>(2*(n+1) -1) mod 2 = 1\<close> have "\<dots> = ((-1)^((2*(n+1) - 1 + 3) div 2)) * (seqX ((2*(n+1) - 1 + 1) div 2))" 
            by (metis Nat.le_imp_diff_is_add Suc.hyps bits_mod_0 calculation diff_add_inverse2 
                diff_le_self diff_self_eq_0 mult_eq_self_implies_10 not_numeral_le_zero numeral_Bit0
                numeral_One seqX.elims zero_neq_numeral)
          also have "\<dots> = ((-1)^((2*(n + 1) + 2) div 2)) * (seqX ((2*n+2) div 2))" by (simp add: algebra_simps)
          also with \<open>((-1)^((2*(n + 1) + 2) div 2)) = 1\<close> have "\<dots> = (seqX ((2*n+2) div 2))"
            by (smt (verit) left_minus_one_mult_self power_add_numeral2 power_one)
          also have "\<dots> = seqX (n+1)" by simp
          finally show ?thesis .
        qed        

        show "0 \<le> sumFst (4 * n + 1)"
        proof-
          have "sumFst (4*n + 1) = sumFst (4*n) + seqX (4*n + 1)" by simp
          also with \<open>seqX (4 * n + 1) = seqX (n + 1)\<close> have "\<dots> = sumFst (4*n) + seqX (n + 1)" by simp
          also have "\<dots> = 2*sumFst n + seqX (n + 1)" using S4k_eq_2Sk Suc(1) by simp
          also have "\<dots> = 2*sumFst n + sumFst (n + 1) - sumFst n" by simp
          also have "\<dots> = sumFst n + sumFst (n + 1)" by simp
          also have "\<dots> \<ge> 0" using Suc
            by (smt (verit) add_increasing2 add_mono_thms_linordered_semiring(2) distrib_left 
                distrib_right le_add_same_cancel2 le_iff_add mult.comm_neutral mult.commute num_double 
                numeral_times_numeral one_add_one)
          finally show "sumFst (4*n + 1) \<ge> 0" .
        qed
      qed
    next
      case False
      then show ?thesis
      proof-
        assume "n mod 2 \<noteq> 0"
        show "0 \<le> sumFst (4*n + 1)"
        proof-
          have "(sumFst n) mod 2 = 1" using Sn_eq_n_mod2
            using False by auto
          then have "sumFst n \<ge> 1" using Suc
            by (metis mult_le_mono1 nat_mult_1 one_le_numeral 
                unique_euclidean_semiring_numeral_class.mod_less_eq_dividend)

          have "sumFst(4*n) = 2*sumFst(n)" using S4k_eq_2Sk Suc(1) by simp
          also with \<open>sumFst n \<ge> 1\<close> have "\<dots> \<ge> 2" by simp 
          finally have "sumFst (4*n) \<ge> 2" .

          have "sumFst (4*n + 1) = sumFst (4*n) + seqX (4*n + 1)" by simp
          also with \<open>sumFst (4*n) \<ge> 2\<close> have "\<dots> \<ge> 0" using seqXimage
            by (smt (verit, del_insts) le_add_same_cancel2 zero_le)
          finally show "sumFst (4*n + 1) \<ge> 0" .
        qed
      qed
    qed
  
    show ?case using 1 10 11 12 13 14 by blast

  qed
qed

\<comment> \<open> ===== Main problem ===== \<close>

lemma Si_gt_0:
  fixes i :: nat
  assumes "i \<ge> 1"
  shows "sumFst i \<ge> 0"
  using assms Si_gt_0_4k by simp

end