theory mi15087_Danilo_Vuckovic
  imports Complex_Main
begin

text \<open>
Zadatak 3, treci razred 
Link: https://imomath.com/srb/zadaci/RS_2016_republicko_resenja.pdf
Tekst zadatka:
Ako su m i n prirodni brojevi za koje vazi 7m^2 + 7m + 8 =n^2,
dokazati da je broj n/5 + 1 jednak zbiru kvadrata dva uzastopna prirodna broja.
\<close>

lemma p1:
  fixes m n :: nat
  assumes "7*m^2 + 7*m + 8 = n^2"
  shows "7*(2*m+1)^2 = (2*n-5)*(2*n+5)"
proof-
  have "7*(4*m^2 + 4*m + 1) + 25 = 4*n^2"
    using assms by auto
  
  also have "7*(4*m^2 + 4*m + 1) = 4*n^2 - 25"
    using \<open>7 * (4 * m\<^sup>2 + 4 * m + 1) + 25 = 4 * n\<^sup>2\<close> by linarith
 
  also have "7*(2*m+1)^2 = 4*n^2 -25 "
    by (smt \<open>7 * (4 * m\<^sup>2 + 4 * m + 1) = 4 * n\<^sup>2 - 25\<close> add.assoc add.commute mult.commute mult.left_commute mult_2 nat_mult_1_right numeral_Bit0 one_power2 power2_sum power_mult_distrib)
  
  finally show ?thesis
    by (smt Nat.diff_cancel \<open>7 * (2 * m + 1)\<^sup>2 = 4 * n\<^sup>2 - 25\<close> add.commute add_mult_distrib2 diff_mult_distrib mult.commute mult_2 nat_mult_1 numeral_Bit0 power2_eq_square) 
qed

lemma mod_pom1:
  fixes a :: nat
  assumes "a > 0"
  shows "(7*a^2 + 10) mod 7 = 5"
proof (induction a)
  case 0
   have "(7*0^2 +(10::int)) mod 7 = 10 mod 7"
      by auto
   then have "10 mod (7::int) = 3"
     by auto
  then show ?case 
    sorry
next
  case (Suc a)
  then show ?case sorry
qed



lemma mod_pom3:
  fixes a :: nat
  assumes "a > 0"
  shows "(7*b^2 - 2) mod 7 = 5"
proof (induction a)
  case 0
   have "(7*0^2 -(2::int)) mod 7 = (-2) mod 7"
      by auto
   then have "(-2) mod (7::int) = 5"
     by auto
  then show ?case 
    sorry
next
  case (Suc b)
  then show ?case sorry
qed

lemma mod_rez1:
  fixes a b :: nat
  assumes "b^2 mod 7 = 3"
  shows "False"
  sorry

lemma mod_rez2:
  fixes a b :: nat
  assumes "7*b^2 - a^2 mod 8 = 10" 
  shows "False"
  sorry
(*
lemma mod_rez22:
  fixes a b :: nat
  assumes "a^2 mod 8 = 1"
  shows "False"
  sorry

lemma mod_rez222:
  fixes a b :: nat
  assumes "b^2  mod 8 = 1"
  shows "False"
  sorry
*)


lemma mod_rez3:
  fixes a :: nat
  assumes "a^2 mod 7 = 5"
  shows "False"
  sorry

(*
lemma kontradikcija1:
  fixes m n a b :: nat
  assumes "7*a^2=2*n-5" "b^2 = 2*n+5" "b mod 2 = 1 " "a mod 2 = 1"
  shows "False"
proof-
  have "b^2 - 7*a^2 = 2*n + 5 - (2*n - 5)" 
    using assms by simp
  then have "b^2 - 7*a^2 = 10"
        by (metis Nat.add_diff_assoc2 Suc_1 Suc_inject add_2_eq_Suc' add_Suc_right assms(2) diff_diff_cancel diff_le_self le_Suc_eq le_add2 nat_1_eq_mult_iff numeral_eq_one_iff semiring_norm(86))
  then have "b^2 = 7*a^2 + 10"
    by auto
  then have "b^2 mod 7 = (7*a^2 + 10) mod 7"
    by auto
  then have "b^2 mod 7 = 3"
    using mod_pom1
    by (simp add: assms(3))
  then show ?thesis
    using mod_rez1
    by blast
qed
*)

lemma kontradikcija2:
  fixes m n a b :: nat
  assumes "a^2=2*n-5" "7*b^2 = 2*n+5" "b mod 2 = 1 " "a mod 2 = 1" "b^2 mod 8 = 1 " "a^2 mod 8 = 1"
  shows "False"
proof-
  have "7*b^2 - a^2 = 2*n + 5 - (2*n - 5)" 
    using assms by simp
  then have "7*b^2 - a^2 = 10"
        by (metis Nat.add_diff_assoc2 Suc_1 Suc_inject add_2_eq_Suc' add_Suc_right assms(2) diff_diff_cancel diff_le_self le_Suc_eq le_add2 nat_1_eq_mult_iff numeral_eq_one_iff semiring_norm(86))
  then have "(7*b^2 - a^2) mod 8 = 6"
	by (metis assms(5) assms(6))
  then show ?thesis
    using mod_rez2
    by blast
qed



lemma kontradikcija3:
  fixes m n a b :: nat
  assumes "5*a^2=2*n-5" "5*7*b^2 = 2*n+5" "b mod 2 = 1 " "a mod 2 = 1" "gcd a b = 1"
  shows "False"
proof-
  have "5*7*b^2 - 5*a^2 = 2*n + 5 - (2*n - 5)" 
    using assms by simp
  then have "35*b^2 - 5*a^2 = 10"
    using assms by simp
  then have "7*b^2 - a^2 = 2"
        by (metis Nat.add_diff_assoc2 Suc_1 Suc_inject add_2_eq_Suc' add_Suc_right assms(2) diff_diff_cancel diff_le_self le_Suc_eq le_add2 nat_1_eq_mult_iff numeral_eq_one_iff semiring_norm(86))
  then have "a^2 = 7*b^2 - 2"
    by auto
  then have "a^2 mod 7 = (7*b^2 - 2) mod 7"
    by auto
  then have "a^2 mod 7 = 5"
    using mod_pom3
    by (simp add: assms(3))
  then show ?thesis
    using mod_rez3
    by blast
  qed







lemma p2:
  fixes m n a b k :: nat
  assumes "7*5*a^2=2*n-5" "5*b^2 = 2*n + 5" "b = 2*k + 1"
  shows "n div 5 + 1 = k^2 + (k+1)^2"
proof-
	have "2*n + 5 = 5* (2*k+1)^2"
    by (smt ab_semigroup_add_class.add_ac(1) add.commute assms(2) assms(3) mult_2 mult_numeral_left_semiring_numeral numeral_Bit0 numeral_times_numeral one_add_one one_power2 power2_sum power_mult_distrib)

  also have "2*n + 5 = 20*k^2 + 20*k + 5"
     \<open> 2*n + 5 = 5* (2*k+1)\<^sup>2\<close> by auto 

  also have "n = 10*k^2 + 10*k"
      using \<open>2 * n + 5 = 5*(2 * k + 1)\<^sup>2\<close> by auto
 
  also have "n div 5 + 1 = 2*k^2 + 2*k +1"
    by (simp add: \<open>n  = 10 * k\<^sup>2 + 10 * k\<close>)

   show ?thesis
    by (smt \<open>n div 5 + 1 = 2 * k\<^sup>2 + 2 * k + 1\<close> ab_semigroup_add_class.add_ac(1) add.commute mult_2 mult_numeral_1_right numeral_One one_power2 power2_sum)
  
qed

lemma p3:
  fixes m n a b :: nat
  assumes "7*(2*m+1)^2 = (2*n-5)*(2*n+5)"
  shows "2*n-5 = 7*a^2 \<and> 2*n+5 = b^2 \<or> 2*n-5 = a^2 \<and> 2*n+5 = 7*b^2  \<or> 2*n-5 = 5*a^2 \<and> 2*n+5 = 5*7*b^2  \<or> 2*n-5 = 5*7*a^2 \<and> 2*n+5 = 5*b^2" 
    sorry

lemma glavna:
  fixes m n a b :: nat
  assumes "7*m^2 + 7*m + 8 = n^2" "b > 0" 
  shows "\<exists> a b. b = a + 1 \<and> n div 5 + 1 = a^2 + b^2"
proof-
  have "2*n-5 = 7*a^2 \<and> 2*n+5 = b^2 \<or> 2*n-5 = a^2 \<and> 2*n+5 = 7*b^2  \<or> 2*n-5 = 5*a^2 \<and> 2*n+5 = 5*7*b^2  \<or> 2*n-5 = 5*7*a^2 \<and> 2*n+5 = 5*b^2"
    using p3
    using assms p1 by blast
  then have "2*n+5 = 5*b^2 \<and> 2*n-5 = 5*7*a^2"
    using kontradikcija3
    by (metis assms(2))
  then have "n + 1 = k^2 + (k+1)^2"
    using p2
    by (smt assms p1 p3)
  then show ?thesis
    by blast
qed
  
  
end