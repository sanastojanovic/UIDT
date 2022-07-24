theory mi16004_Jelena_Milivojevic

imports Main HOL.NthRoot

begin

text \<open>
Link: https://www.imo-official.org/problems/IMO2012SL.pdf
Algebra A3
\<close>

(*  Let a2, \<dots>, an be n − 1 positive real numbers, where n \<ge> 3, such that a2a3 \<sqdot> \<sqdot> \<sqdot> an = 1.
    Prove that: (1+a2)^2*(1+a3)^3...(1+an)^n>n^n *)

find_theorems "prod (_)"

lemma weighted_am_gm[simp]:
  fixes a :: "real list" and w :: "nat list" and n :: "nat" and B :: "nat"
  assumes "\<forall> i. (a ! i) > 0"
  assumes "\<forall> i. (w ! i) > 0"
  assumes "n = (length a) \<and> n = (length w) \<and> n > 0"
  assumes "B > 0 \<and> (sum_list w)  = B"
  shows "(\<Sum> i = 0..(n-1). (w ! i) * (a ! i)) / B \<ge> root B (\<Prod> i = 0..(n-1). (a ! i) ^ (w ! i))"
  sorry

                                  
lemma weighted_am_gm_powered[simp]:
  fixes a :: "real list" and w :: "nat list" and n :: "nat" and B :: "nat"
  assumes "\<forall> i. (a ! i) > 0"
  assumes "\<forall> i. (w ! i) > 0"
  assumes "n = (length a) \<and> n = (length w) \<and> n > 0"
  assumes "B > 0 \<and> (sum_list w)  = B"
  shows "((\<Sum> i = 0..(n-1). (w ! i) * (a ! i)) / B) ^ B \<ge> (\<Prod> i = 0..(n-1). (a ! i) ^ (w ! i))"
  using assms
  sorry 
(*
proof -
  have *: "(\<Sum> i = 0..(n-1). (w ! i) * (a ! i)) / B \<ge> root B (\<Prod> i = 0..(n-1). (a ! i) ^ (w ! i))"
    using assms weighted_am_gm by blast
  also have "((\<Sum> i = 0..(n-1). (w ! i) * (a ! i)) / B) ^ B \<ge> (root B (\<Prod> i = 0..(n-1). (a ! i) ^ (w ! i)))^ B"
    using assms(4) * 
*)

lemma am_gm_powered_specialization[simp]:
  fixes a1 :: "real" and a2 :: "real" and w1 :: "nat" and w2 :: "nat" and w :: "nat"
  assumes "a1 > 0" "a2 > 0" "w1 > 0" "w2 > 0"
  assumes "w > 0 \<and> (w1 + w2) = w"
  shows "((w1*a1 + w2*a2)/w) ^ w \<ge> (a1 ^ w1)* (a2 ^ w2)"
  using assms
  sorry
    
(*ak je na poziciji k-1 u nizu a*)
lemma final:
  fixes a :: "real list" and i :: "nat"
  assumes "length a = n \<and> n \<ge> 3"
  assumes "prod_list(tl a) = 1"
  assumes "\<forall> k > 0 . (a ! k) > 0"
  shows "(\<Prod> i = 1..(n-1). (1 + a ! i) ^ (i + 1)) > n ^ n"
  using assms (*
proof - 
  have "(\<Prod> i = 1..(n-1). (1 + a ! i) ^ (i+1)) = (\<Prod> i = 1..(n-1). (i*(1/i) + a ! i) ^ (i+1))"
    by simp 
  also have "\<dots> = (\<Prod> i = 1..(n-1). ((i+1)*(1/(i+1))*((i)*(1/(i)) + a ! i)) ^ (i+1))"
    by simp
  also have "\<dots> = (\<Prod> i = 1..(n-1). ((i+1)^(i+1))*((1/(i+1)*((i)*(1/(i)) + a ! i))^(i+1)))"
    by (metis (mono_tags, lifting) ab_semigroup_mult_class.mult_ac(1) of_nat_power power_mult_distrib)
  also have "\<dots> = (\<Prod> i = 1..(n-1). ((i+1)^(i+1))*((((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1)))"
    by simp
  also have "\<dots> = (\<Prod> k = 1..(n-1). (k+1)^(k+1))*(\<Prod> i = 1..(n-1). ((((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1)))"
      by (metis of_nat_prod prod.distrib)
  also have "\<dots> \<ge> (\<Prod> k = 1..(n-1). (k+1)^(k+1))*(\<Prod> i = 1..(n-1). (((1/(i))^(i))*((a ! i)^1)))"
     using am_gm_powered_specialization[of "1/i" "a ! i" "i" 1 "i+1"]
     by simp
qed *)
  sorry

end